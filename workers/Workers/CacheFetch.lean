/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Workers.Cache
import Init.System.IO

/-!
Drives `lake update` + `lake cache get` against a synthetic workspace, so a remote consumer can
ask the server to fetch a package's pre-built artifacts from Reservoir (or another cache
service) without having any project on disk.

Single-shot, blocking, shell-out-to-lake. No streaming progress, no partial-result handling, no
retries — if the consumer calls it, the request serializes the entire fetch and returns when lake
is done.

The synthetic workspace is per-call, not shared across calls. Each invocation builds up a
fresh `${tempDir}/lean-server-cache-{pid}/cache-ws-{n}/` with one `[[require]]`. Reusing a
workspace across calls is a planned follow-up.
-/

namespace Workers

structure FetchRequest where
  /-- Reservoir scope, e.g. `leanprover-community/mathlib4`. -/
  package  : String
  /-- Git revision (branch, tag, or commit sha). -/
  revision : String
  /-- Override the git URL. Defaults to inferring from the package name. -/
  gitUrl?  : Option String := none
  /-- Cache service name as known by the user's `~/.lake/config.toml`. Defaults to Reservoir. -/
  service? : Option String := none

structure FetchResult where
  /-- Whether the fetch succeeded. -/
  success     : Bool
  /-- Combined stdout+stderr from each shelled-out command, in order, for the consumer to inspect. -/
  log         : String
  /-- Absolute paths to the populated package olean directories that should be added to the
  worker `LEAN_PATH`. Empty on failure. -/
  libDirs     : Array System.FilePath
  /-- Path to the synthetic workspace, retained on disk so callers can inspect it on failure. -/
  workspace   : System.FilePath

namespace Fetch

/-- Per-call workspace counter, scoped by PID. We don't need it to be unique across processes
(`{pid}` already handles that). -/
private initialize wsCounter : IO.Ref Nat ← IO.mkRef 0

/-- Allocate a fresh synthetic workspace path. Caller writes files into it. -/
private def freshWorkspace : IO System.FilePath := do
  let base : System.FilePath :=
    match (← IO.getEnv "TMPDIR") with
    | some t => System.FilePath.mk t
    | none   => System.FilePath.mk "/tmp"
  let pid ← IO.Process.getPID
  let n ← wsCounter.modifyGet fun n => (n, n + 1)
  let dir := base / s!"lean-server-cache-{pid}" / s!"cache-ws-{n}"
  IO.FS.createDirAll dir
  return dir

/-- Default https URL for a Reservoir-style scope like `leanprover-community/mathlib4`. -/
private def defaultGitUrl (scope : String) : String :=
  s!"https://github.com/{scope}.git"

/-- Generate a minimal lakefile.toml that just `require`s the given dependency. -/
private def renderLakefile (req : FetchRequest) (toolchain : String) : String :=
  let url := req.gitUrl?.getD (defaultGitUrl req.package)
  -- Split the Reservoir scope into (owner, name) on the first `/`.
  let parts := req.package.splitOn "/"
  let (scope, name) :=
    match parts with
    | [a, b] => (a, b)
    | _      => ("", req.package)
  let scopeLine := if scope.isEmpty then "" else s!"\nscope = \"{scope}\""
  -- Suppress mention of `toolchain` to silence warnings; we set lean-toolchain separately.
  let _ := toolchain
  s!"name = \"lean-server-cache-fetch\"
defaultTargets = []

[[require]]
name = \"{name}\"{scopeLine}
git = \"{url}\"
rev = \"{req.revision}\"
"

/-- Run a single command in `cwd`, capturing its merged stdout+stderr. Returns `(exitCode, output)`. -/
private def runCmd (cwd : System.FilePath) (cmd : String) (args : Array String)
    : IO (UInt32 × String) := do
  let out ← IO.Process.output {
    cmd, args, cwd := some cwd
  }
  return (out.exitCode, s!"$ {cmd} {String.intercalate " " args.toList}\n{out.stdout}{out.stderr}")

/-- Walk `<workspace>/.lake/packages/*/.lake/build/lib` and return absolute paths that exist. -/
private def collectLibDirs (workspace : System.FilePath) : IO (Array System.FilePath) := do
  let pkgRoot := workspace / ".lake" / "packages"
  if ! (← pkgRoot.pathExists) then
    return #[]
  let mut dirs : Array System.FilePath := #[]
  for entry in (← pkgRoot.readDir) do
    let lib := entry.path / ".lake" / "build" / "lib"
    if (← lib.isDir) then
      let abs ← IO.FS.realPath lib
      dirs := dirs.push abs
  return dirs

/-- Drive a single `lake update` + `lake cache get` cycle for one dependency.

This is the entire happy path:

1. Make `${TMPDIR}/lean-server-cache-{pid}/cache-ws-{n}/`.
2. Write `lean-toolchain` and `lakefile.toml`.
3. `cd` there and run `lake update` (clones the package's git, populates manifest).
4. `cd` there and run `lake cache get --scope=PKG --rev=REV [--service=...]`.
5. Walk `.lake/packages/*/.lake/build/lib` and report absolute paths.

On any non-zero exit code we stop and return `{success := false}` with the log so far. We
intentionally do **not** delete the workspace on failure — the caller (or a human debugging via
the caller) can inspect it. Successful workspaces are also retained for now; a follow-up may
add periodic GC. -/
def run (req : FetchRequest) (toolchain : String) : IO FetchResult := do
  let workspace ← freshWorkspace
  IO.FS.writeFile (workspace / "lean-toolchain") s!"{toolchain}\n"
  IO.FS.writeFile (workspace / "lakefile.toml") (renderLakefile req toolchain)
  let mut log : String := ""

  -- Step 1: lake update
  let (rc, out) ← runCmd workspace "lake" #["update"]
  log := log ++ out
  if rc != 0 then
    return { success := false, log, libDirs := #[], workspace }

  -- Step 2: lake cache get
  let mut args : Array String := #["cache", "get", s!"--scope={req.package}",
                                    s!"--rev={req.revision}"]
  if let some svc := req.service? then
    args := args.push s!"--service={svc}"
  let (rc, out) ← runCmd workspace "lake" args
  log := log ++ out
  if rc != 0 then
    return { success := false, log, libDirs := #[], workspace }

  let libDirs ← collectLibDirs workspace
  return { success := true, log, libDirs, workspace }

end Fetch

end Workers
