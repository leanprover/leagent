/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Corpus.DeclClosure.Cone
import Corpus.Artifact

/-!
Phase 2 of single-declaration extraction: turn a closure plus a pool of elaborated
records into one target's artifact.

`projectClosure` is pure decision-making — select, annotate with `closure_role`,
order dependencies-first, derive the import union — and returns a `Projection`.
`renderMetadata` / `renderDropped` turn that into JSON, and `writeTarget` only lays
bytes down. Keeping the decisions separate from the writing is what lets the tests
assert on role annotation and ordering directly instead of through the filesystem.

## Output layout

One directory per target, mirroring the corpus layout so existing consumers read it
unchanged, plus a `data/target.jsonl` holding the target record ALONE. That file
exists for composition with `lean_reassemble materialize-units`, which emits one
task per record it is handed: passing the whole closure would emit a task per
premise as well, so the target must be separable. See
`docs/single-decl-extraction.md`.
-/

namespace Corpus.DeclClosure

open Lean

/-! ## Topological ordering

Records are written dependencies-first so a consumer can concatenate them into
one Lean input. We order by `deps` restricted to the closure. Mutual blocks make
the graph cyclic in general, so this is a DFS post-order with cycle tolerance
rather than a strict topological sort: a back edge is skipped, which keeps the
order deterministic and total while placing every acyclic dependency correctly.
-/

/-- Depth-first post-order over closure-internal `deps`, tolerant of cycles.
Ties break on name so the result is deterministic. -/
partial def topoOrder (records : Array ConstRecord) : Array String := Id.run do
  let inClosure : Std.HashSet String := records.foldl (fun s r => s.insert r.name) {}
  let mut depsOf : Std.HashMap String (Array String) := {}
  for r in records do
    let internal := (r.deps.filter (fun d => inClosure.contains d && d != r.name))
    depsOf := depsOf.insert r.name (internal.mergeSort (· < ·)).toArray
  let roots := (records.map (·.name)).qsort (· < ·)
  let mut visited : Std.HashSet String := {}
  let mut onStack : Std.HashSet String := {}
  let mut out : Array String := #[]
  -- Explicit stack: (name, next-child-index). Recursion depth on a deep closure
  -- would otherwise risk the interpreter's stack.
  for root in roots do
    if visited.contains root then continue
    let mut stack : Array (String × Nat) := #[(root, 0)]
    onStack := onStack.insert root
    while h : stack.size > 0 do
      let (name, idx) := stack[stack.size - 1]
      let children := depsOf.getD name #[]
      if idx < children.size then
        stack := stack.set! (stack.size - 1) (name, idx + 1)
        let child := children[idx]!
        -- Skip already-emitted nodes and back edges (cycles in mutual blocks).
        unless visited.contains child || onStack.contains child do
          stack := stack.push (child, 0)
          onStack := onStack.insert child
      else
        stack := stack.pop
        onStack := onStack.erase name
        unless visited.contains name do
          visited := visited.insert name
          out := out.push name
  return out

/-- Reorder `records` to follow `order`, appending anything `order` omits. -/
def applyOrder (records : Array ConstRecord) (order : Array String)
    : Array ConstRecord := Id.run do
  let mut byName : Std.HashMap String ConstRecord := {}
  for r in records do
    byName := byName.insert r.name r
  let mut out : Array ConstRecord := #[]
  let mut emitted : Std.HashSet String := {}
  for name in order do
    if let some r := byName[name]? then
      unless emitted.contains name do
        emitted := emitted.insert name
        out := out.push r
  for r in records do
    unless emitted.contains r.name do
      emitted := emitted.insert r.name
      out := out.push r
  return out

/-! ## Projection: closure + record pool → the artifact's contents

Separated from writing so the interesting logic — selection, role annotation,
ordering, and the derived metadata — is a pure function that tests can assert on
directly, without going through the filesystem.
-/

/-- Everything the `--decl` run needs from the CLI. -/
structure RunConfig where
  targets          : Array Name
  projectRoot      : System.FilePath
  outDir           : System.FilePath
  roots            : Array Name
  tagConfig        : TagConfig
  configPath?      : Option System.FilePath
  includeInternal  : Bool
  includePrivate   : Bool
  reverseElab      : Bool
  reverseClosers   : Bool
  reverseSkip      : Array String
  reverseTimeoutMs : Nat
  jobs             : Nat
  isolateFiles     : Bool
  resume           : Bool
  strictClosure    : Bool
  toolVersion      : String
  deriving Inhabited

/-- One target's artifact contents, before anything touches disk. -/
structure Projection where
  /-- The target's display name — the artifact's identity. -/
  targetName  : String
  /-- Every selected record, annotated with `closureRole`, dependencies first. -/
  ordered     : Array ConstRecord
  /-- `ordered` split into the `theorems` and `definitions` configs. -/
  theorems    : Array ConstRecord
  definitions : Array ConstRecord
  /-- The target record alone — what `materialize-units` must be handed so the
  target is the only hole. See the module docstring. -/
  target      : Array ConstRecord
  /-- Union of NON-OWNED file imports across the closure, sorted. Owned modules
  are inlined as records, so they are excluded. -/
  imports     : Array String
  /-- Closure members that resolved to no record, sorted. -/
  unresolved  : Array String
  /-- Those members grouped by why they were dropped: `(reason, count, names)`,
  ordered with the categories that signal a problem first. Written to
  `dropped.json` so the dataset records what the closure could not represent. -/
  dropped     : Array (DropReason × Nat × Array String)
  deriving Inhabited

/-- Sort `unexplained` first (the only category that signals a problem), then the
rest alphabetically so the report is stable. -/
private def dropSortKey (r : DropReason) : String :=
  if dropIsUnexplained r then "0" else "1" ++ r

/-- Group unresolved closure members by why they were dropped. A member with no
recorded reason is `unexplained` — it looked eligible, so its absence is a real
gap rather than an expected exclusion. -/
def groupDropped (closure : Closure) (unresolved : Array String)
    : Array (DropReason × Nat × Array String) := Id.run do
  -- Bucket by reason, carrying the reason itself so it need not be recovered.
  let mut buckets : Array (DropReason × Array String) := #[]
  for name in unresolved do
    let reason := (closure.dropReasons[name]?).getD unexplainedDrop
    match buckets.findIdx? (fun (r, _) => r == reason) with
    | some i => buckets := buckets.set! i (reason, (buckets[i]!).2.push name)
    | none   => buckets := buckets.push (reason, #[name])
  let grouped := buckets.map fun (reason, names) =>
    let sorted := names.qsort (· < ·)
    (reason, sorted.size, sorted)
  return grouped.qsort (fun a b => dropSortKey a.1 < dropSortKey b.1)

/-- Index the pool by record name, keeping only closure members.

Two records sharing a name but coming from different modules would make selection
ambiguous — the caller cannot know which one the closure meant — so that is an
error rather than a silent pick. -/
private def indexPool (targetName : String) (closure : Closure)
    (pool : Array ConstRecord) : IO (Std.HashMap String ConstRecord) := do
  let mut byName : Std.HashMap String ConstRecord := {}
  for r in pool do
    if closure.roles.contains r.name then
      if let some existing := byName[r.name]? then
        if existing.module != r.module then
          fail s!"closure for {targetName}: {r.name} was emitted by two modules \
            ({existing.module} and {r.module}); cannot build an unambiguous closure"
      byName := byName.insert r.name r
  return byName

/-- Select one target's records from the pool, annotate each with its role, and
order them dependencies-first.

`pool` is every record produced by elaborating the union of closure files across
all targets; each target projects its own view out of it rather than re-elaborating. -/
def projectClosure (closure : Closure) (pool : Array ConstRecord)
    (cfg : RunConfig) : IO Projection := do
  let targetName := closure.target.display.toString
  let byName ← indexPool targetName closure pool
  -- A closure without its target is useless, whatever the strictness setting.
  unless byName.contains targetName do
    fail s!"the target {targetName} produced no record. It may be filtered out of \
      the corpus (a constructor, recursor, projection, or generated lemma), or its \
      file failed to elaborate."
  -- Annotate what resolved; collect what did not.
  let mut selected : Array ConstRecord := #[]
  let mut unresolved : Array String := #[]
  for (name, role) in closure.roles.toList do
    match byName[name]? with
    | some r => selected := selected.push { r with closureRole := some role.toString }
    | none   => unresolved := unresolved.push name
  unresolved := unresolved.qsort (· < ·)
  let dropped := groupDropped closure unresolved
  unless unresolved.isEmpty do
    -- `unexplained` first: everything else is machinery the corpus excludes on
    -- purpose, but an unexplained member means a record we expected went missing.
    let summary := ", ".intercalate <| dropped.toList.map fun (reason, n, _) =>
      s!"{n} {reason}"
    if cfg.strictClosure then
      fail s!"closure for {targetName} has {unresolved.size} member(s) with no \
        emitted record ({summary}); see dropped.json"
    IO.eprintln s!"corpus-extract: closure for {targetName}: {unresolved.size} \
      member(s) not representable as records ({summary}); see dropped.json"
    if let some (_, n, names) := dropped.find? (fun (r, _, _) => dropIsUnexplained r) then
      IO.eprintln s!"corpus-extract: warning: {n} closure member(s) of \
        {targetName} are eligible but produced no record — this is unexpected: \
        {", ".intercalate names.toList}"
  let ordered := applyOrder selected (topoOrder selected)
  let (theorems, definitions) := Artifact.partitionByConfig ordered
  -- The import header a consumer needs to make non-owned constants resolvable.
  let mut imports : Array String := #[]
  let mut importSet : Std.HashSet String := {}
  for r in ordered do
    for imp in r.fileImports do
      unless CollectCommon.isOwnedModuleName cfg.roots imp.toName do
        unless importSet.contains imp do
          importSet := importSet.insert imp
          imports := imports.push imp
  return { targetName
           ordered
           theorems
           definitions
           target := ordered.filter (fun r => r.name == targetName)
           imports := imports.qsort (· < ·)
           unresolved
           dropped }

/-- Tally records by `closureRole`, as a sorted JSON object. -/
private def roleCountsJson (ordered : Array ConstRecord) : Json :=
  let counts := ordered.foldl (init := ({} : Std.HashMap String Nat)) fun acc r =>
    let key := r.closureRole.getD "unknown"
    acc.insert key (acc.getD key 0 + 1)
  Json.mkObj <| (counts.toList.mergeSort (fun a b => a.1 < b.1)).map fun (k, n) =>
    (k, Json.num (JsonNumber.fromNat n))

private def strArr (xs : Array String) : Json := Json.arr (xs.map Json.str)

private def nameArr (xs : Array Name) : Json := strArr (xs.map (·.toString))

/-- Render one target's `metadata.json`, making the artifact self-describing. -/
def renderMetadata (closure : Closure) (p : Projection) (cfg : RunConfig)
    (targetRecord : ConstRecord) (filesElaborated : Array String)
    (missingModules : Array Name) : Json :=
  Json.mkObj [
    ("toolVersion",          Json.str cfg.toolVersion),
    ("mode",                 Json.str "decl-closure"),
    ("target",               Json.str p.targetName),
    ("targetRequested",      Json.str closure.target.requested.toString),
    ("targetKind",           Json.str targetRecord.kind),
    ("targetModule",         Json.str targetRecord.module),
    ("targetFile",           Lean.toJson targetRecord.file),
    ("closureCounts",        roleCountsJson p.ordered),
    ("assemblyOrder",        strArr (p.ordered.map (·.name))),
    ("imports",              strArr p.imports),
    -- Counts only; the names live in `dropped.json`, which on a real proof is
    -- larger than everything else in this file combined.
    ("droppedTotal",         Json.num (JsonNumber.fromNat p.unresolved.size)),
    ("droppedByReason",      Json.mkObj (p.dropped.toList.map fun (reason, n, _) =>
                                (reason, Json.num (JsonNumber.fromNat n)))),
    ("droppedDetail",        Json.str "dropped.json"),
    ("privateNames",         Json.arr (closure.privateMap.map fun (display, raw, m) =>
                                Json.mkObj [("displayName", Json.str display),
                                            ("rawName", Json.str raw),
                                            ("module", Json.str m)])),
    ("ownershipRoots",       nameArr cfg.roots),
    ("closureModules",       nameArr closure.modules),
    ("modulesWithoutSource", nameArr missingModules),
    ("filesElaborated",      strArr filesElaborated),
    ("extractionFlags",      Json.mkObj [
                                ("includeInternal", Json.bool cfg.includeInternal),
                                ("includePrivate",  Json.bool cfg.includePrivate),
                                ("reverseElab",     Json.bool cfg.reverseElab),
                                ("reverseClosers",  Json.bool cfg.reverseClosers),
                                ("strictClosure",   Json.bool cfg.strictClosure)])
  ]

/-- Render `dropped.json`: what the closure reached but could not represent as
records, grouped by reason with the full name list per category.

Kept in its own file rather than inlined in `metadata.json` because on a real proof
it dwarfs everything else — `church_rosser` in the LambdaCalc corpus drops 83
members against 42 emitted records. `metadata.json` carries only the per-category
counts and a pointer here. -/
def renderDropped (p : Projection) : Json :=
  Json.mkObj [
    ("format",   Json.str "lean-corpus-dropped.v1"),
    ("target",   Json.str p.targetName),
    ("total",    Json.num (JsonNumber.fromNat p.unresolved.size)),
    ("note",     Json.str "Closure members with no emitted record. All categories \
except `unexplained` are machinery the corpus excludes by design (constructors, \
recursors, projections, generated companions, equation-compiler helpers, synthetic \
theorems). `unexplained` means a member looked eligible but produced no record."),
    ("categories", Json.arr (p.dropped.map fun (reason, n, names) =>
        Json.mkObj [
          ("reason", Json.str reason),
          ("count",       Json.num (JsonNumber.fromNat n)),
          ("names",       strArr names)
        ]))
  ]

/-! ## Writing one target's output -/

/-- Write one target's directory: the two config files, the target-only file, and
`metadata.json`. All of the decisions were made by `projectClosure`; this only
lays bytes down. -/
def writeTarget (outDir : System.FilePath) (closure : Closure)
    (pool : Array ConstRecord) (cfg : RunConfig)
    (filesElaborated : Array String) (missingModules : Array Name)
    : IO (System.FilePath × Projection) := do
  let p ← projectClosure closure pool cfg
  let targetDir := outDir / Artifact.safeName p.targetName
  let dataDir := targetDir / "data"
  IO.FS.createDirAll (dataDir / "theorems")
  Artifact.writeJsonl (dataDir / "definitions.jsonl") p.definitions
  Artifact.writeJsonl (dataDir / "theorems" / "train.jsonl") p.theorems
  Artifact.writeJsonl (dataDir / "target.jsonl") p.target
  -- `projectClosure` guarantees the target resolved, so this lookup is total.
  let some targetRecord := p.target[0]?
    | fail s!"internal error: projection for {p.targetName} lost its target record"
  let metaJson := renderMetadata closure p cfg targetRecord filesElaborated missingModules
  IO.FS.writeFile (targetDir / "metadata.json") (metaJson.render.pretty ++ "\n")
  -- Always written, even when nothing was dropped, so a consumer never has to
  -- distinguish "no drops" from "this extractor did not report drops".
  IO.FS.writeFile (targetDir / "dropped.json") ((renderDropped p).render.pretty ++ "\n")
  return (targetDir, p)

end Corpus.DeclClosure
