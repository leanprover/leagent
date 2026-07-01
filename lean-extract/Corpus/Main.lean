import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Card
import Corpus.Extract
import Corpus.Discover
import Corpus.WorkerExtract

/-!
CLI entry for `corpus-extract`.

```
corpus-extract \
  --modules <Mod>                   (required: root module; repeat for several)
  --output <dir>                    (required: output directory)
  --config <path>                   (optional: tags config JSON)
  --include-internal                (default: false)
  --no-private                      (default: include private decls)
  --source-root <path>              (optional: override source-file root)
  --split-by-tag <key>              (theorems config: stratified 80/10/10 split)
  --seed <n>                        (default 0; deterministic split)
  --dataset-card-config <path>      (project metadata JSON for the README.md)
  --help                            (print usage and exit 0)
```

Output layout:

```
<output-dir>/
  README.md                            (only if --dataset-card-config given)
  metadata.json
  data/
    definitions.jsonl                  (always a single "train" split — HF reserves "all")
    theorems/
      train.jsonl, valid.jsonl, test.jsonl   (with --split-by-tag)
      train.jsonl                            (otherwise — HF reserves "all" as a split keyword)
```
-/

namespace Corpus

open Lean

/-- Tool version, bumped manually as the schema evolves. -/
def toolVersion : String := "0.2.0"

/-- How to enumerate the declarations to extract.
  * `glob`   — drive `lean --worker` over the source files discovered on disk
               under the `--modules` roots (orphan-safe; the default).
  * `import` — the legacy path: `importModules` the `--modules` roots and walk
               the resulting `Environment`. Misses orphan files but needs no
               worker/plugin. -/
inductive EnumerateMode where
  | glob
  | import
  deriving Inhabited, BEq

structure CliArgs where
  modules            : Array Name := #[]
  output             : Option System.FilePath := none
  config             : Option System.FilePath := none
  sourceRoot         : Option System.FilePath := none
  includeInternal    : Bool := false
  includePrivate     : Bool := true
  reverseElab        : Bool := false
  reverseClosers     : Bool := false
  traceReverseElab   : Bool := false
  splitByTag         : Option String := none
  seed               : Nat := 0
  datasetCardConfig  : Option System.FilePath := none
  enumerate          : EnumerateMode := .glob
  listOrphans        : Bool := false
  deriving Inhabited

private def usage : String := "\
Usage: corpus-extract --modules <Mod> [--modules <Mod> ...] --output <dir>
                     [--enumerate glob|import] [--list-orphans]
                     [--config <path>] [--source-root <path>]
                     [--include-internal] [--no-private]
                     [--reverse-elab] [--closers]
                     [--trace-reverse-elab]
                     [--split-by-tag <key>] [--seed <n>]
                     [--dataset-card-config <path>]
                     [--help]

If --source-root (or, failing that, the current directory) contains a
lakefile.lean or lakefile.toml, the tool re-execs itself under `lake env`
from that directory so LEAN_PATH resolves to the project's built .oleans.

--enumerate glob (default) drives `lean --worker` over the source files found
on disk under the --modules roots (orphan-safe). --enumerate import uses the
legacy importModules + Environment walk. --list-orphans prints the modules on
disk that are not in the import closure of the --modules roots, then exits.
"

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private def parseArgs (args : List String) : Except String CliArgs :=
  go args {}
where
  go : List String → CliArgs → Except String CliArgs
    | [], acc => .ok acc
    -- `--modules` consumes a single module name. To pass several, repeat the flag
    -- (e.g. `--modules A --modules B`). Keeps the tail strictly shorter so
    -- structural recursion succeeds without a custom termination measure.
    | "--modules" :: v :: xs, acc =>
        if v.startsWith "--" then .error "--modules expects a module name"
        else go xs { acc with modules := acc.modules.push v.toName }
    | "--output" :: v :: xs, acc =>
        go xs { acc with output := some v }
    | "--config" :: v :: xs, acc =>
        go xs { acc with config := some v }
    | "--source-root" :: v :: xs, acc =>
        go xs { acc with sourceRoot := some v }
    | "--include-internal" :: xs, acc =>
        go xs { acc with includeInternal := true }
    | "--no-private" :: xs, acc =>
        go xs { acc with includePrivate := false }
    | "--reverse-elab" :: xs, acc =>
        go xs { acc with reverseElab := true }
    | "--closers" :: xs, acc =>
        go xs { acc with reverseElab := true, reverseClosers := true }
    | "--trace-reverse-elab" :: xs, acc =>
        go xs { acc with reverseElab := true, traceReverseElab := true }
    | "--split-by-tag" :: v :: xs, acc =>
        if v.startsWith "--" then .error "--split-by-tag expects a tag key"
        else go xs { acc with splitByTag := some v }
    | "--seed" :: v :: xs, acc =>
        match parseNat? v with
        | some n => go xs { acc with seed := n }
        | none   => .error s!"--seed expects a non-negative integer, got: {v}"
    | "--dataset-card-config" :: v :: xs, acc =>
        go xs { acc with datasetCardConfig := some v }
    | "--enumerate" :: v :: xs, acc =>
        match v with
        | "glob"   => go xs { acc with enumerate := .glob }
        | "import" => go xs { acc with enumerate := .import }
        | _        => .error s!"--enumerate expects glob|import, got: {v}"
    | "--list-orphans" :: xs, acc =>
        go xs { acc with listOrphans := true }
    | x :: _, _ => .error s!"unknown argument: {x}"

/-- Render the extractor's own `metadata.json` payload. -/
private def renderStats (stats : Corpus.RunStats) (modulesIn : Array Name)
    (splitCounts : List (String × Nat)) : Json :=
  let kindObj := Json.mkObj <| stats.byKind.map fun (k, n) =>
    (k, Json.num (Lean.JsonNumber.fromNat n))
  let splitObj := Json.mkObj <| splitCounts.map fun (s, n) =>
    (s, Json.num (Lean.JsonNumber.fromNat n))
  let modulesIn := modulesIn.toList.map (fun n => Json.str n.toString)
  let modulesOut := stats.modules.map Json.str
  Json.mkObj [
    ("toolVersion",    Json.str toolVersion),
    ("totalRecords",   Json.num (Lean.JsonNumber.fromNat stats.total)),
    ("countsByKind",   kindObj),
    ("splitCounts",    splitObj),
    ("rootModules",    Json.arr modulesIn.toArray),
    ("modulesEmitted", Json.arr modulesOut.toArray)
  ]

/-- Partition records into the `theorems` config (kind ends in "theorem")
and the `definitions` config (everything else). Order within each bucket
follows the input. -/
private def partitionByConfig (rs : Array ConstRecord) :
    Array ConstRecord × Array ConstRecord := Id.run do
  let mut thms : Array ConstRecord := #[]
  let mut defs : Array ConstRecord := #[]
  for r in rs do
    if r.kind.endsWith "theorem" then
      thms := thms.push r
    else
      defs := defs.push r
  return (thms, defs)

/-- Lookup a record's tag value for `key`, falling back to a synthetic
`__untagged__` group when the tag is absent. -/
private def tagValue (r : ConstRecord) (key : String) : String :=
  match r.tags.find? (fun (k, _) => k == key) with
  | some (_, v) => v
  | none        => "__untagged__"

/-- Group records by their tag value. Preserves first-occurrence order of
groups so the output is deterministic across runs. -/
private def groupByTag (rs : Array ConstRecord) (key : String) :
    List (String × Array ConstRecord) := Id.run do
  let mut groups : List (String × Array ConstRecord) := []
  for r in rs do
    let v := tagValue r key
    let mut found := false
    let mut newGroups : List (String × Array ConstRecord) := []
    for (k, arr) in groups do
      if k == v then
        newGroups := newGroups ++ [(k, arr.push r)]
        found := true
      else
        newGroups := newGroups ++ [(k, arr)]
    if !found then
      newGroups := newGroups ++ [(v, #[r])]
    groups := newGroups
  return groups

/-- Stable per-record sort key for deterministic shuffling. We hash
`name ++ ":" ++ seed_string` with `String.hash` (Lean core) and order
ascending. Same seed + same input = same order across runs and platforms. -/
private def sortKey (seedStr : String) (r : ConstRecord) : UInt64 :=
  String.hash (r.name ++ ":" ++ seedStr)

/-- Split a single tagged group into (train, valid, test). Sizes follow the
documented 80/10/10 boundaries with `n_train = max(1, n*8/10)`. -/
private def splitGroup (members : Array ConstRecord) (seedStr : String) :
    Array ConstRecord × Array ConstRecord × Array ConstRecord :=
  let n := members.size
  if n == 0 then (#[], #[], #[])
  else
    let sorted := members.qsort (fun a b => sortKey seedStr a < sortKey seedStr b)
    let nTrain := Nat.max 1 (n * 8 / 10)
    let remainder := n - nTrain
    let nValid := remainder / 2
    let nTest := remainder - nValid
    let train := sorted.extract 0 nTrain
    let valid := sorted.extract nTrain (nTrain + nValid)
    let test := sorted.extract (nTrain + nValid) (nTrain + nValid + nTest)
    (train, valid, test)

/-- Apply the stratified split across every tag group. Returns the three
buckets in train/valid/test order. -/
private def stratifiedSplit (rs : Array ConstRecord) (key : String)
    (seed : Nat) : Array ConstRecord × Array ConstRecord × Array ConstRecord :=
  let seedStr := toString seed
  let groups := groupByTag rs key
  Id.run do
    let mut tr : Array ConstRecord := #[]
    let mut va : Array ConstRecord := #[]
    let mut te : Array ConstRecord := #[]
    for (_, members) in groups do
      let (a, b, c) := splitGroup members seedStr
      tr := tr ++ a
      va := va ++ b
      te := te ++ c
    return (tr, va, te)

/-- Write a list of records as JSONL to `path`, one record per line. -/
private def writeJsonl (path : System.FilePath)
    (records : Array ConstRecord) : IO Unit := do
  IO.FS.writeFile path ""  -- truncate or create
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for r in records do
    h.putStrLn (Lean.toJson r).compress
  h.flush

/-- Tally `kind` occurrences across `rs`, returning a sorted (kind, count) list. -/
private def kindCountsOf (rs : Array ConstRecord) : List (String × Nat) := Id.run do
  let mut tally : Std.HashMap String Nat := {}
  for r in rs do
    let n := tally.getD r.kind 0
    tally := tally.insert r.kind (n + 1)
  let entries := tally.toList
  return entries.mergeSort (fun a b => a.1 < b.1)

/-- Tally tag values across every record, grouped by tag key. Both the outer
list (by key) and each inner list (by value) are sorted alphabetically so
the rendered card is stable across runs. -/
private def tagCountsOf (rs : Array ConstRecord) :
    List (String × List (String × Nat)) := Id.run do
  let mut perKey : Std.HashMap String (Std.HashMap String Nat) := {}
  for r in rs do
    for (k, v) in r.tags do
      let inner := perKey.getD k {}
      let n := inner.getD v 0
      perKey := perKey.insert k (inner.insert v (n + 1))
  let keys := perKey.toList.map (·.1)
  let keysSorted := keys.mergeSort (fun a b => a < b)
  let mut out : List (String × List (String × Nat)) := []
  for k in keysSorted do
    let inner := (perKey.getD k {}).toList
    let innerSorted := inner.mergeSort (fun a b => a.1 < b.1)
    out := out ++ [(k, innerSorted)]
  return out

private def hasNonEmpty (s? : Option String) : Bool :=
  (s?.map (· != "")).getD false

/-- Pick a representative theorem example: prefer one with both a non-empty
`signature` and non-empty `premises`, then any with a non-empty `signature`,
then any. -/
private def pickTheoremExample (rs : Array ConstRecord) : Option ConstRecord :=
  let withBoth := rs.find? fun r => hasNonEmpty r.signature && !r.premises.isEmpty
  match withBoth with
  | some r => some r
  | none =>
    let withSrc := rs.find? fun r => hasNonEmpty r.signature
    withSrc.orElse (fun _ => rs[0]?)

/-- Pick a representative definition example: prefer non-empty `signature`,
fall back to the first record. -/
private def pickDefinitionExample (rs : Array ConstRecord) : Option ConstRecord :=
  let withSrc := rs.find? fun r => hasNonEmpty r.signature
  withSrc.orElse (fun _ => rs[0]?)

/-- Marker env var used to break the auto re-exec loop. When set, the
running process is the child invocation under `lake env` and should
just do the work. -/
private def reexecMarker : String := "CORPUS_EXTRACT_REEXEC"

/-- Resolve a path against `base` if it isn't already absolute. -/
private def absolutize (base : System.FilePath) (p : System.FilePath) :
    System.FilePath :=
  if p.isAbsolute then p else base / p

/-- True if `dir` looks like a Lake project root (has a `lakefile.lean`
or `lakefile.toml`). -/
private def isLakeProject (dir : System.FilePath) : IO Bool := do
  let lean := dir / "lakefile.lean"
  let toml := dir / "lakefile.toml"
  pure ((← lean.pathExists) || (← toml.pathExists))

/-- Re-exec ourselves under `lake env` from inside `project`, with
relative user paths absolutized against the original cwd. Returns the
child's exit code. -/
private unsafe def reexecUnderLake (project : System.FilePath)
    (rawArgs : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let self ← IO.appPath
  let projectAbs := absolutize cwd project
  -- Walk the original arg list and absolutize every flag value that is
  -- a filesystem path. Bare flags and non-path values (`--modules`,
  -- `--split-by-tag`, `--seed`, etc.) pass through untouched.
  let pathFlags : List String :=
    ["--output", "--config", "--source-root", "--dataset-card-config"]
  let rec rebuild : List String → List String
    | [] => []
    | f :: v :: xs =>
      if pathFlags.contains f then
        f :: (absolutize cwd v).toString :: rebuild xs
      else
        f :: v :: rebuild xs
    | [x] => [x]
  let childArgs : Array String :=
    #["env", self.toString] ++ (rebuild rawArgs).toArray
  let child ← IO.Process.spawn {
    cmd  := "lake"
    args := childArgs
    cwd  := some projectAbs
    env  := #[(reexecMarker, some "1")]
  }
  child.wait

/-- Real entry point. Loads search path, imports modules, runs extraction,
applies filters/splits, then writes JSONL files, metadata, and (optionally)
a HF dataset card. -/
unsafe def runCli (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  match parseArgs args with
  | .error e =>
    IO.eprintln s!"corpus-extract: {e}"
    IO.eprintln usage
    return 1
  | .ok cli =>
    -- Auto re-exec under `lake env` when --source-root (or, failing
    -- that, the cwd) points at a Lake project. The marker env var
    -- breaks the loop on the second pass.
    let alreadyReexec := (← IO.getEnv reexecMarker).isSome
    if !alreadyReexec then
      let candidate := cli.sourceRoot.getD (← IO.currentDir)
      if (← isLakeProject candidate) then
        return (← reexecUnderLake candidate args)
    if cli.modules.isEmpty then
      IO.eprintln "corpus-extract: --modules is required"
      IO.eprintln usage
      return 1
    -- `--list-orphans`: discover files on disk under the `--modules` roots vs the
    -- import closure, print the difference, and exit. (Diagnostic only — no JSONL.)
    if cli.listOrphans then
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
      Lean.enableInitializersExecution
      Lean.initSearchPath (← Lean.findSysroot)
      let imports : Array Import := cli.modules.map (fun n => { module := n })
      let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
      let imported := env.allImportedModuleNames
      let orphans := Corpus.Discover.findOrphans (files.map (·.module)) imported
      IO.println s!"corpus-extract: {files.size} file(s) on disk, {imported.size} in import closure"
      if orphans.isEmpty then
        IO.println "corpus-extract: no orphans (every discovered file is in the import closure)"
      else
        IO.println s!"corpus-extract: {orphans.size} orphan module(s) NOT in the import closure:"
        for m in orphans do IO.println s!"  {m}"
      return 0
    let outDir := match cli.output with
      | some d => d
      | none   => "."
    if cli.output.isNone then
      IO.eprintln "corpus-extract: --output is required"
      IO.eprintln usage
      return 1
    -- Ensure output + data subdirs exist.
    IO.FS.createDirAll outDir
    let dataDir     : System.FilePath := outDir / "data"
    let theoremsDir : System.FilePath := dataDir / "theorems"
    IO.FS.createDirAll dataDir
    IO.FS.createDirAll theoremsDir
    -- Load tag config if provided.
    let tagConfig ← match cli.config with
      | none      => pure TagConfig.empty
      | some path => Corpus.loadConfig path
    -- Obtain the records either via the worker/plugin path (default, orphan-safe)
    -- or the legacy import-and-walk path. Both produce `Array ConstRecord` +
    -- per-kind counts; everything downstream (split/write/metadata/card) is shared.
    let records : Array ConstRecord ← match cli.enumerate with
      | .glob => do
          let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
          let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
          IO.println s!"corpus-extract: discovered {files.size} source file(s); driving workers…"
          let (recs, wstats) ← Corpus.extractViaWorkers projectRoot files tagConfig
                                 cli.includeInternal cli.includePrivate cli.reverseElab
                                 cli.reverseClosers cli.traceReverseElab
          IO.println s!"corpus-extract: {wstats.filesOk} ok, {wstats.filesEmpty} empty, \
            {wstats.filesError} error (of {wstats.filesTotal})"
          pure recs
      | .import => do
          -- Bring up Lean's search path and import the requested modules.
          Lean.enableInitializersExecution
          Lean.initSearchPath (← Lean.findSysroot)
          let imports : Array Import := cli.modules.map (fun n => { module := n })
          -- `loadExts := true` is REQUIRED on Lean 4.31: it loads imported modules'
          -- environment-extension state, which includes the tactic-elaborator
          -- registration table. Without it, reverse-elaboration's `runTactic` fails
          -- with "Tactic `rfl` has not been implemented".
          let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
          let opts : ExtractOptions := {
            rootModules     := cli.modules
            tagConfig       := tagConfig
            includeInternal := cli.includeInternal
            includePrivate  := cli.includePrivate
            sourceRoot      := cli.sourceRoot.getD "."
            reverseElab     := cli.reverseElab
            reverseClosers  := cli.reverseClosers
          }
          let (recs, _stats) ← Corpus.runMetaOnEnv env (Corpus.extractAllBuffered env opts)
          pure recs
    -- Derive `total`/`modules` from the records themselves rather than from a
    -- per-path RunStats: the worker (`.glob`) path returns WorkerRunStats and the
    -- legacy (`.import`) path's RunStats is discarded, so neither reaches here.
    -- Computing from `records` keeps metadata.json correct and path-independent.
    let emittedModules :=
      (records.map (·.module)).toList.eraseDups.mergeSort (fun a b => a < b)
    let stats : Corpus.RunStats :=
      { total := records.size, modules := emittedModules }
    let (theorems, defns) := partitionByConfig records
    -- Definitions: always a single `all` split.
    writeJsonl (dataDir / "definitions.jsonl") defns
    -- Theorems: split if `--split-by-tag`, else single `all` split.
    let (theoremSplitCounts, splitCountsForMeta) ←
      match cli.splitByTag with
      | none =>
          let p : System.FilePath := theoremsDir / "train.jsonl"
          writeJsonl p theorems
          pure ([("train", theorems.size)], [("theorems/train", theorems.size),
                                              ("definitions/train", defns.size)])
      | some key =>
          let (tr, va, te) := stratifiedSplit theorems key cli.seed
          writeJsonl (theoremsDir / "train.jsonl") tr
          writeJsonl (theoremsDir / "valid.jsonl") va
          writeJsonl (theoremsDir / "test.jsonl")  te
          pure (
            [("train", tr.size), ("valid", va.size), ("test", te.size)],
            [("theorems/train", tr.size), ("theorems/valid", va.size),
             ("theorems/test", te.size), ("definitions/train", defns.size)])
    -- Combined kind / tag counts (post-extraction, no filtering).
    let combinedKindCounts := kindCountsOf records
    -- Write metadata.json.
    let metaPath : System.FilePath := outDir / "metadata.json"
    let metaJson := renderStats { stats with byKind := combinedKindCounts }
                                 cli.modules splitCountsForMeta
    IO.FS.writeFile metaPath ((metaJson.render.pretty) ++ "\n")
    -- Write README.md if a dataset card config was supplied.
    if let some cardPath := cli.datasetCardConfig then
      let cardCfg ← DatasetCardConfig.load cardPath
      let thmEx := (pickTheoremExample theorems).map fun r => (Lean.toJson r).pretty
      let defEx := (pickDefinitionExample defns).map fun r => (Lean.toJson r).pretty
      let cardStats : CardStats := {
        total := records.size
        theoremsTotal := theorems.size
        definitionsTotal := defns.size
        theoremSplits := theoremSplitCounts
        kindCounts := combinedKindCounts
        tagCounts := tagCountsOf records
        theoremExample := thmEx
        definitionExample := defEx
      }
      let card := renderCard cardCfg cardStats
      IO.FS.writeFile (outDir / "README.md") card
    IO.println s!"corpus-extract: wrote {theorems.size} theorems + {defns.size} definitions to {outDir}"
    return 0

end Corpus

unsafe def main (args : List String) : IO UInt32 :=
  Corpus.runCli args
