/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Corpus.DeclClosure.Cone
import Corpus.DeclClosure.Emit
import Corpus.WorkerExtract

/-!
Single-declaration extraction (`--decl`): emit ONE named declaration together with
its transitive project-owned dependency closure, as a self-contained set of
records.

Where corpus extraction walks every source file and emits a record per constant,
this mode inverts the direction: it starts from a target name, computes what that
target depends on, and elaborates only the files defining those dependencies.

Two phases, in two modules:

  * `Corpus.DeclClosure.Cone` — resolve each target and compute its closure against
    an import-only environment (cheap: loads `.olean`s, elaborates nothing).
  * `Corpus.DeclClosure.Emit` — project a closure out of the elaborated record pool
    and write the target's directory.

This module is the driver that sequences them. Elaborating the union of needed
files ONCE, between the two phases, is what makes several `--decl` targets cheaper
than several invocations.

See `docs/single-decl-extraction.md` for the design and its validation.
-/

namespace Corpus.DeclClosure

open Lean


/-- Run single-declaration extraction end to end.

The ordering matters for cost: resolve targets and compute cones against a
cheap import-only environment FIRST, so that the (expensive) elaboration step
only ever touches files that actually define closure members. The union across
all targets is elaborated once, which is what makes several `--decl` flags
cheaper than several invocations. -/
unsafe def run (cfg : RunConfig) : IO UInt32 := do
  if !cfg.opts.includePrivate then
    IO.eprintln "corpus-extract: warning: --no-private with --decl yields \
      structurally incomplete closures — proofs routinely use private lemmas, and \
      those holes are not recoverable from imports."
  -- Import-only environment for cone computation.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let imports : Array Import := cfg.roots.map (fun n => { module := n })
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  -- Resolve every target and compute its closure.
  let mut closures : Array Closure := #[]
  for name in cfg.targets do
    let target ← resolveTarget env name
    let closure ← computeClosure env cfg.roots target cfg.opts
    IO.println s!"corpus-extract: {target.display}: closure of {closure.roles.size} \
      declaration(s) across {closure.modules.size} module(s)"
    closures := closures.push closure
  -- Union the modules needed by all targets, then map to files on disk.
  let discovered ← Discover.discoverFiles cfg.projectRoot cfg.roots
  let mut neededModules : Array Name := #[]
  for closure in closures do
    for m in closure.modules do
      unless neededModules.contains m do
        neededModules := neededModules.push m
  let (files, missingModules) := filesForModules discovered neededModules
  if !missingModules.isEmpty then
    let rendered := ", ".intercalate (missingModules.toList.map toString)
    IO.eprintln s!"corpus-extract: warning: {missingModules.size} closure \
      module(s) have no source file under {cfg.projectRoot} and will contribute no \
      records: {rendered}"
  if files.isEmpty then
    fail s!"no source files found for the requested closure(s) under {cfg.projectRoot}"
  -- Elaborate the union ONCE.
  let mode := if cfg.isolateFiles then "isolated" else "in-process"
  IO.println s!"corpus-extract: elaborating {files.size} file(s) for \
    {closures.size} target(s) ({mode}, jobs={cfg.jobs})…"
  let (pool, wstats) ←
    if cfg.isolateFiles then
      extractViaFrontendIsolated cfg.projectRoot files cfg.opts
        cfg.configPath? cfg.jobs cfg.reverseTimeoutMs cfg.outDir cfg.resume
    else
      extractViaFrontend files cfg.tagConfig cfg.opts cfg.jobs
  IO.println s!"corpus-extract: {wstats.filesOk} ok, {wstats.filesEmpty} empty, \
    {wstats.filesError} error (of {wstats.filesTotal})"
  if wstats.filesError > 0 then
    let resumeHint := if cfg.isolateFiles then "; staged shards were retained for --resume" else ""
    fail s!"extraction failed for {wstats.filesError} file(s){resumeHint}"
  -- Write one directory per target from the shared pool.
  let relPaths := files.map (·.relPath)
  IO.FS.createDirAll cfg.outDir
  for closure in closures do
    let (targetDir, p) ← writeTarget cfg.outDir closure pool cfg relPaths missingModules
    IO.println s!"corpus-extract: wrote {closure.target.display} → {targetDir} \
      ({p.theorems.size} theorem(s), {p.definitions.size} definition(s))"
  if cfg.isolateFiles then
    cleanupShards cfg.outDir
  return 0

end Corpus.DeclClosure
