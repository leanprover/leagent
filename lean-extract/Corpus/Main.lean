import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Card
import Corpus.CollectCommon
import Corpus.Discover
import Corpus.Reexec
import Corpus.WorkerExtract
import Corpus.GrindExtract
import Corpus.GrindInProofExtract
import Corpus.ProofStatesExtract
import Corpus.DeclClosure
import Corpus.Artifact

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
open Corpus.Artifact (writeJsonl partitionByConfig)

/-- Tool version, bumped manually as the schema evolves. -/
def toolVersion : String := "0.2.0"

/-- Per-kind counters for the corpus `metadata.json`. -/
structure RunStats where
  total   : Nat := 0
  byKind  : List (String × Nat) := []
  modules : List String := []
  deriving Inhabited

structure CliArgs where
  modules            : Array Name := #[]
  output             : Option System.FilePath := none
  config             : Option System.FilePath := none
  sourceRoot         : Option System.FilePath := none
  includeInternal    : Bool := false
  includePrivate     : Bool := true
  reverseElab        : Bool := false
  reverseClosers     : Bool := false
  reverseSkip        : Array String := #[]
  reverseTimeoutMs   : Nat := 300000
  jobs               : Option Nat := none
  isolateFiles       : Bool := true
  resume             : Bool := false
  splitByTag         : Option String := none
  seed               : Nat := 0
  datasetCardConfig  : Option System.FilePath := none
  listOrphans        : Bool := false
  /-- Emit the AlphaGrind grind manifest (`data/grind/train.jsonl`): re-prove
  every theorem with `grind`'s default strategy and record what it did. Uses the
  worker path only. When set, this REPLACES the corpus extraction (the tool runs
  grind collection instead of writing definitions/theorems). -/
  grindManifest      : Bool := false
  /-- Emit the in-proof grind dataset (`data/grind-in-proof/train.jsonl`):
  capture grind data at grind CALL SITES inside existing proofs (one record per
  VC), rather than re-proving whole statements. Uses the worker path only. When
  set, this REPLACES the corpus extraction. Mutually exclusive with
  `--grind-manifest`. -/
  grindInProof       : Bool := false
  /-- Emit the per-step proof-state dataset (`data/proof-states/train.jsonl`):
  for every tactic-proved theorem, the nested tree of author-written tactics with
  the goal state before and after each one. When set, this REPLACES the corpus
  extraction. Mutually exclusive with the grind modes. -/
  proofStates        : Bool := false
  /-- Single-declaration mode: extract each named declaration plus its transitive
  owned dependency closure into its own per-target directory under `--output`.
  Repeatable. When non-empty, this REPLACES corpus extraction. -/
  decls              : Array Name := #[]
  /-- With `--decl`, fail instead of warning when a closure member has no emitted
  record (constructors, recursors, projections, generated lemmas). -/
  strictClosure      : Bool := false
  deriving Inhabited

/-- The per-file collection knobs these arguments select. Everything downstream —
the drivers, the isolated child, the collectors — takes this one value rather than
the five flags separately. -/
def CliArgs.opts (cli : CliArgs) : CollectOptions :=
  { includeInternal := cli.includeInternal
    includePrivate  := cli.includePrivate
    reverseElab     := cli.reverseElab
    reverseClosers  := cli.reverseClosers
    reverseSkip     := cli.reverseSkip }

private def usage : String := "\
Usage: corpus-extract --modules <Mod> [--modules <Mod> ...] --output <dir>
                     [--list-orphans]
                     [--config <path>] [--source-root <path>]
                     [--include-internal] [--no-private]
                     [--reverse-elab] [--closers] [--skip-reverse <decl>]
                     [--reverse-timeout <seconds>]
                     [--jobs <n>] [--no-isolate-files] [--resume]
                     [--grind-manifest] [--grind-in-proof] [--proof-states]
                     [--decl <Name> ...] [--strict-closure]
                     [--split-by-tag <key>] [--seed <n>]
                     [--dataset-card-config <path>]
                     [--help]

If --source-root (or, failing that, the current directory) contains a
lakefile.lean or lakefile.toml, the tool re-execs itself under `lake env`
from that directory so LEAN_PATH resolves to the project's built .oleans.

The tool drives Lean's frontend over the source files found on disk under the
--modules roots (orphan-safe). --list-orphans prints the modules on disk that are
not in the import closure of the declared roots, then exits.

--grind-manifest re-proves every theorem with `grind`'s default strategy and
writes data/grind/train.jsonl (the interactive script, the `grind only`
reconstruction, and the activated/used lemma triple per theorem), plus the
env-wide available-hint set into metadata.json. This REPLACES corpus extraction.

File extraction is isolated by default: each source file is processed in a child
process and the results are merged by the parent.

--no-isolate-files reverts to in-process extraction (one shared Lean environment
per run).

Under isolation each completed file's records are staged to <output>/.shards/ as
soon as its child returns. --resume reuses shards only when all relevant inputs
and source hashes match. Successful runs remove the staging directory.

--jobs controls extraction concurrency. Under isolation (the default) it is the
number of concurrent child processes, defaulting to half the machine's hardware
threads and capped at 4. Under --no-isolate-files it defaults to 1.

--skip-reverse skips reverse-elaboration for a theorem declaration. Repeat it for
multiple declarations. It matches either the corpus display name or the raw Lean
internal name and emits proof_method=skipped_requested for that theorem.

--reverse-timeout sets the isolated reverse-elaboration timeout in seconds
(default 300). On timeout the file is re-run without reverse elaboration. A value
of 0 disables this timeout.

--decl extracts ONE named declaration plus its transitive project-owned
dependency closure, into its own directory under --output (mirroring the corpus
layout, plus a data/target.jsonl holding the target record alone for composition
with `lean_reassemble materialize-units`). Every record is annotated with
closure_role: target / statement (needed to state the target) / proof (used only
by its proof). Repeat --decl for several targets; the union of needed source files
is elaborated once. This REPLACES corpus extraction, and is mutually exclusive
with the grind modes. --strict-closure turns the closure-member-has-no-record
warning into an error.

--proof-states captures the INTERIOR of every tactic proof: for each
tactic-proved theorem it walks the elaborated proof and writes one record to
data/proof-states/train.jsonl holding the nested tree of author-written tactics,
each step carrying the goal states before and after it ran (hypotheses + target,
structured and pretty-printed). Theorems proved by a bare term (`:= rfl`) have no
tactics and are counted, not emitted. Records join to the theorems config by name,
and each step's byte offsets locate it inside that theorem's proof source.
REPLACES corpus extraction; mutually exclusive with the grind modes and --decl.

--grind-in-proof instead captures grind data at the grind CALL SITES inside
existing proofs: it walks each proof, re-runs instrumented grind on every
subgoal a source `grind` was applied to (using the author's hints), and writes
one record per call site to data/grind-in-proof/train.jsonl. Use this for
tactic-heavy corpora where grind only discharges subgoals mid-proof (e.g.
mvcgen). REPLACES corpus extraction; mutually exclusive with --grind-manifest.
"

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

@[extern "lean_internal_get_hardware_concurrency"]
private opaque hardwareConcurrency (_ : Unit) : UInt32

private def maxDefaultIsolatedJobs : Nat := 4

/-- Resolve explicit or mode-specific extraction concurrency. -/
private def resolveJobs (jobs? : Option Nat) (isolate : Bool) : Nat :=
  match jobs? with
  | some n => n
  | none   =>
    if isolate then
      Nat.max 1 (Nat.min maxDefaultIsolatedJobs
        ((hardwareConcurrency ()).toNat / 2))
    else
      Frontend.defaultMaxConcurrent


/-- Internal child mode: reverse-elaborate ONE theorem and print its `ScriptResult`
as JSON. The request arrives as a single JSON argument
(`Corpus.ReverseOneRequest`) — one encoding shared with the parent. -/
private def parseReverseOneRequest? (args : List String)
    : Option (Except String ReverseOneRequest) :=
  match args with
  | [flag, payload] =>
      if flag == reverseOneFlag then some (Json.parse payload >>= fromJson?) else none
  | _ => none

private unsafe def runReverseOneCli (request : ReverseOneRequest) : IO UInt32 := do
  let r ← Corpus.reverseOneInFile request.sourceFile request.module request.decl
    request.closers
  IO.println (Lean.toJson r).compress
  return 0

/-- Internal child mode: extract ONE file and print its records as JSONL.

The request arrives as a single JSON argument (`Corpus.ExtractOneRequest`), so the
parent's encoding and this decode are the same one — there is no flag writer/parser
pair to drift. Returns `none` when this is not a child invocation. -/
private def parseExtractOneRequest? (args : List String)
    : Option (Except String ExtractOneRequest) :=
  match args with
  | [flag, payload] =>
      if flag == extractOneFlag then
        some (Json.parse payload >>= fromJson?)
      else none
  | _ => none

private unsafe def runExtractOneCli (request : ExtractOneRequest) : IO UInt32 := do
  let tagConfig ← match request.config with
    | none => pure TagConfig.empty
    | some path => Corpus.loadConfig path
  let df : Corpus.Discover.DiscoveredFile :=
    { absPath := request.sourceFile, module := request.module, relPath := request.relPath }
  for r in (← Corpus.extractOneFileViaFrontend df tagConfig request.opts) do
    IO.println (Lean.toJson r).compress
  return 0

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
    | "--skip-reverse" :: v :: xs, acc =>
        if v.startsWith "--" then .error "--skip-reverse expects a declaration name"
        else go xs { acc with reverseSkip := acc.reverseSkip.push v }
    | "--reverse-timeout" :: v :: xs, acc =>
        match parseNat? v with
        | some n => go xs { acc with reverseTimeoutMs := n * 1000 }
        | none   => .error s!"--reverse-timeout expects seconds (non-negative integer), got: {v}"
    | "--jobs" :: v :: xs, acc =>
        match parseNat? v with
        | some n =>
            if n == 0 then .error "--jobs expects a positive integer"
            else go xs { acc with jobs := some n }
        | none   => .error s!"--jobs expects a positive integer, got: {v}"
    | "--isolate-files" :: xs, acc =>
        go xs { acc with isolateFiles := true }
    | "--no-isolate-files" :: xs, acc =>
        go xs { acc with isolateFiles := false }
    | "--resume" :: xs, acc =>
        go xs { acc with resume := true }
    | "--split-by-tag" :: v :: xs, acc =>
        if v.startsWith "--" then .error "--split-by-tag expects a tag key"
        else go xs { acc with splitByTag := some v }
    | "--seed" :: v :: xs, acc =>
        match parseNat? v with
        | some n => go xs { acc with seed := n }
        | none   => .error s!"--seed expects a non-negative integer, got: {v}"
    | "--dataset-card-config" :: v :: xs, acc =>
        go xs { acc with datasetCardConfig := some v }
    | "--list-orphans" :: xs, acc =>
        go xs { acc with listOrphans := true }
    | "--grind-manifest" :: xs, acc =>
        go xs { acc with grindManifest := true }
    | "--grind-in-proof" :: xs, acc =>
        go xs { acc with grindInProof := true }
    | "--proof-states" :: xs, acc =>
        go xs { acc with proofStates := true }
    | "--decl" :: v :: xs, acc =>
        if v.startsWith "--" then .error "--decl expects a declaration name"
        else go xs { acc with decls := acc.decls.push v.toName }
    | "--strict-closure" :: xs, acc =>
        go xs { acc with strictClosure := true }
    | x :: _, _ => .error s!"unknown argument: {x}"

/-- The alternate extraction modes: each REPLACES corpus extraction and owns its
own output layout, so at most one may be requested. Each is an early-return branch
in `runCli`, which means a silently-accepted combination would run only the first
and misreport what the run produced. -/
private def alternateModes (cli : CliArgs) : List (String × Bool) :=
  [("--grind-manifest", cli.grindManifest),
   ("--grind-in-proof", cli.grindInProof),
   ("--proof-states",   cli.proofStates)]

/-- The requested alternate modes, by flag name. -/
private def requestedAlternateModes (cli : CliArgs) : List String :=
  (alternateModes cli).filterMap fun (name, on) => if on then some name else none

/-- Every mode-compatibility rule, as `(violated?, complaint)` pairs.

A flat list, deliberately: each rule is evaluated independently of the others, so a
rule can never be shadowed by an earlier branch returning first. An earlier nested
version had exactly that bug — the `--decl` rules formed their own `if` chain, so
`--decl --resume --no-isolate-files` skipped the `--resume` rule and RAN instead of
being rejected.

`modeComplaint?` reports the first violated rule, so order here is only the reporting
priority; the rejection itself does not depend on it. Rejecting rather than ignoring a
bad combination matters because each mode is an early-return branch in `runCli`: a
silently-accepted combination would run only the first branch and misreport what the
run produced.

Pure, so the rules are checkable without running an extraction. -/
private def modeRules (cli : CliArgs) : List (Bool × String) :=
  let requested := requestedAlternateModes cli
  let decl := !cli.decls.isEmpty
  [ -- At most one alternate mode: each owns its own output layout.
    (requested.length > 1,
      s!"{", ".intercalate requested} are mutually exclusive"),
    -- `--decl` is its own extraction with per-target output.
    (decl && !requested.isEmpty,
      s!"--decl is mutually exclusive with {", ".intercalate requested}"),
    (decl && cli.listOrphans,
      "--decl is mutually exclusive with --list-orphans"),
    (decl && cli.splitByTag.isSome,
      "--split-by-tag is meaningless with --decl (each target is a single \
        closure, not a dataset split)"),
    (decl && cli.datasetCardConfig.isSome,
      "--dataset-card-config is meaningless with --decl (the card renders \
        whole-corpus statistics)"),
    -- Flags that require a mode they were not given with.
    (cli.strictClosure && !decl,
      "--strict-closure requires --decl"),
    -- `--resume` only stages shards on the isolated path (corpus or `--decl`).
    (cli.resume && (!cli.isolateFiles || cli.listOrphans || !requested.isEmpty),
      "--resume requires isolated extraction") ]

/-- The first violated rule's complaint, if any; `none` when the combination is
valid. See `modeRules`. -/
private def modeComplaint? (cli : CliArgs) : Option String :=
  (modeRules cli).findSome? fun (violated, complaint) =>
    if violated then some complaint else none

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

/-- Write one alternate mode's output: its records as JSONL under
`data/<subdir>/train.jsonl`, plus `metadata.json`.

The three alternate modes (`--grind-manifest`, `--grind-in-proof`,
`--proof-states`) each REPLACE corpus extraction and own their output directory, but
lay it down identically; only `subdir` and the mode-specific metadata keys differ.
`toolVersion`, `mode`, `totalRecords`, and `rootModules` are common to all three and
supplied here, so a mode cannot forget one.

`Json.mkObj` sorts keys, so appending `extraMeta` cannot change the field order of
the rendered file. -/
private def writeAltMode [ToJson α] (outDir : System.FilePath) (mode subdir : String)
    (modules : Array Name) (records : Array α)
    (extraMeta : List (String × Json)) : IO System.FilePath := do
  let dir := outDir / "data" / subdir
  IO.FS.createDirAll dir
  let path := dir / "train.jsonl"
  writeJsonl path records
  let metaJson := Json.mkObj ([
    ("toolVersion",  Json.str toolVersion),
    ("mode",         Json.str mode),
    ("totalRecords", Json.num (Lean.JsonNumber.fromNat records.size)),
    ("rootModules",  Json.arr (modules.map (fun n => Json.str n.toString)))
  ] ++ extraMeta)
  IO.FS.writeFile (outDir / "metadata.json") ((metaJson.render.pretty) ++ "\n")
  return path

/-- Count as a JSON number, the shape every run-summary metadata field takes. -/
private def jnat (n : Nat) : Json := Json.num (Lean.JsonNumber.fromNat n)

/-- Marker env var used to break the auto re-exec loop. When set, the
running process is the child invocation under `lake env` and should
just do the work. -/
private def reexecMarker : String := "CORPUS_EXTRACT_REEXEC"

/-- Flags whose values are filesystem paths, absolutized before re-exec. -/
private def reexecPathFlags : List String :=
  ["--output", "--config", "--source-root", "--dataset-card-config"]

/-- Real entry point. Loads search path, imports modules, runs extraction,
applies filters/splits, then writes JSONL files, metadata, and (optionally)
a HF dataset card. -/
unsafe def runCli (args : List String) : IO UInt32 := do
  match parseExtractOneRequest? args with
  | some (.ok request) => return (← runExtractOneCli request)
  | some (.error e) =>
      IO.eprintln s!"corpus-extract: {e}"
      return 2
  | none => pure ()
  match parseReverseOneRequest? args with
  | some (.ok request) => return (← runReverseOneCli request)
  | some (.error e) =>
      IO.eprintln s!"corpus-extract: {e}"
      return 2
  | none => pure ()
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
      if (← Corpus.Reexec.isLakeProject candidate) then
        return (← Corpus.Reexec.reexecUnderLake reexecMarker reexecPathFlags candidate args)
    if cli.modules.isEmpty then
      IO.eprintln "corpus-extract: --modules is required"
      IO.eprintln usage
      return 1
    -- Every mode-compatibility rule, in one table (`modeComplaint?`). Rejecting a
    -- bad combination rather than ignoring it matters because each mode is an
    -- early-return branch below: a silently-accepted combination would run only the
    -- first and misreport what the run produced.
    if let some complaint := modeComplaint? cli then
      IO.eprintln s!"corpus-extract: {complaint}"
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
    -- `--decl`: extract each named declaration plus its transitive owned
    -- dependency closure into its own per-target directory. REPLACES corpus
    -- extraction (its own closure computation + output layout), parallel to the
    -- grind branches below.
    if !cli.decls.isEmpty then
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let tagConfig ← match cli.config with
        | none      => pure TagConfig.empty
        | some path => Corpus.loadConfig path
      -- Closure resolution rejects bad input (unknown/ambiguous/orphan targets,
      -- name collisions) by throwing a `userError` that already carries the
      -- `corpus-extract:` prefix. Report it as a plain diagnostic rather than
      -- letting it surface as an uncaught exception.
      try
        return (← Corpus.DeclClosure.run {
          targets          := cli.decls
          projectRoot      := projectRoot
          outDir           := outDir
          roots            := cli.modules
          tagConfig        := tagConfig
          configPath?      := cli.config
          opts             := cli.opts
          reverseTimeoutMs := cli.reverseTimeoutMs
          jobs             := resolveJobs cli.jobs cli.isolateFiles
          isolateFiles     := cli.isolateFiles
          resume           := cli.resume
          strictClosure    := cli.strictClosure
          toolVersion      := toolVersion
        })
      catch e =>
        IO.eprintln e.toString
        return 1
    -- `--grind-manifest`: re-prove every theorem with grind and write the grind
    -- dataset. This REPLACES corpus extraction (its own worker plugin + output).
    if cli.grindManifest then
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
      IO.println s!"corpus-extract: discovered {files.size} source file(s); running grind…"
      let (recs, available, gstats) ←
        Corpus.extractGrindViaFrontend files cli.includePrivate
      IO.println s!"corpus-extract: {gstats.filesOk} ok, {gstats.filesEmpty} empty, \
        {gstats.filesError} error (of {gstats.filesTotal}); \
        theorems: {gstats.outcome Outcome.closed} closed, {gstats.outcome Outcome.stuck} stuck, \
        {gstats.outcomesOther Corpus.grindOutcomeLabels} error, \
        {gstats.outcome Outcome.deadlineSkipped} skipped"
      -- metadata.json: run summary + the env-wide available-hint set.
      let path ← writeAltMode outDir "grind-manifest" "grind" cli.modules recs [
        ("theoremsClosed",  jnat (gstats.outcome Outcome.closed)),
        ("theoremsStuck",   jnat (gstats.outcome Outcome.stuck)),
        ("theoremsError",   jnat (gstats.outcomesOther Corpus.grindOutcomeLabels)),
        ("theoremsSkipped", jnat (gstats.outcome Outcome.deadlineSkipped)),
        ("availableHints",  Json.arr (available.map Json.str))
      ]
      IO.println s!"corpus-extract: wrote {recs.size} grind records to {path} \
        ({available.size} available hints)"
      return 0
    -- `--grind-in-proof`: capture grind data at grind call sites inside existing
    -- proofs (one record per VC). REPLACES corpus extraction (its own plugin +
    -- output dir), parallel to the grind-manifest branch above.
    if cli.grindInProof then
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
      IO.println s!"corpus-extract: discovered {files.size} source file(s); running in-proof grind…"
      let (recs, available, gstats) ←
        Corpus.extractGrindInProofViaFrontend files cli.includePrivate
      IO.println s!"corpus-extract: {gstats.filesOk} ok, {gstats.filesEmpty} empty, \
        {gstats.filesError} error (of {gstats.filesTotal}); \
        call sites: {gstats.outcome Outcome.closed} closed, {gstats.outcome Outcome.stuck} stuck, \
        {gstats.outcomesOther Corpus.grindOutcomeLabels} error, \
        {gstats.outcome Outcome.deadlineSkipped} skipped"
      -- metadata.json: run summary + the env-wide available-hint set.
      let path ← writeAltMode outDir "grind-in-proof" "grind-in-proof" cli.modules recs [
        ("callsClosed",    jnat (gstats.outcome Outcome.closed)),
        ("callsStuck",     jnat (gstats.outcome Outcome.stuck)),
        ("callsError",     jnat (gstats.outcomesOther Corpus.grindOutcomeLabels)),
        ("callsSkipped",   jnat (gstats.outcome Outcome.deadlineSkipped)),
        ("availableHints", Json.arr (available.map Json.str))
      ]
      IO.println s!"corpus-extract: wrote {recs.size} in-proof grind records to {path} \
        ({available.size} available hints)"
      return 0
    -- `--proof-states`: capture the interior of every tactic proof (one record per
    -- tactic-proved theorem, nested tactic tree with per-step goal states).
    -- REPLACES corpus extraction, parallel to the grind branches above.
    if cli.proofStates then
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
      let jobs := resolveJobs cli.jobs (isolate := false)
      IO.println s!"corpus-extract: discovered {files.size} source file(s); \
        collecting proof states (jobs={jobs})…"
      let (recs, pstats, pextra) ← Corpus.extractProofStatesViaFrontend files
        cli.includePrivate jobs
      IO.println s!"corpus-extract: {pstats.filesOk} ok, {pstats.filesEmpty} empty, \
        {pstats.filesError} error (of {pstats.filesTotal}); \
        theorems: {pstats.outcome Outcome.ok} captured, \
        {pextra.theoremsTermProved} term-proved (no tactics), \
        {pstats.outcome Outcome.skippedLarge} too large, \
        {pstats.outcome Outcome.deadlineSkipped} past deadline, \
        {pstats.outcomesOther Corpus.proofStateOutcomeLabels} error; \
        {pextra.totalSteps} step(s) total"
      if pstats.filesError > 0 then
        throw <| IO.userError s!"proof-state extraction failed for {pstats.filesError} file(s)"
      let path ← writeAltMode outDir "proof-states" "proof-states" cli.modules recs [
        ("totalSteps",           jnat pextra.totalSteps),
        ("theoremsCaptured",     jnat (pstats.outcome Outcome.ok)),
        ("theoremsTermProved",   jnat pextra.theoremsTermProved),
        ("theoremsSkippedLarge", jnat (pstats.outcome Outcome.skippedLarge)),
        ("theoremsDeadline",     jnat (pstats.outcome Outcome.deadlineSkipped)),
        ("theoremsError",        jnat (pstats.outcomesOther Corpus.proofStateOutcomeLabels)),
        ("stepCeiling",          jnat Corpus.ProofStates.stepCeiling),
        ("includePrivate",       Json.bool cli.includePrivate)
      ]
      IO.println s!"corpus-extract: wrote {recs.size} proof-state record(s) to {path}"
      return 0
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
    -- Drive the frontend over the discovered source files. Clean staging only
    -- after all final outputs are written.
    let cleanupShardsRef ← IO.mkRef false
    let records : Array ConstRecord ← do
      let projectRoot := cli.sourceRoot.getD (← IO.currentDir)
      let files ← Corpus.Discover.discoverFiles projectRoot cli.modules
      let jobs := resolveJobs cli.jobs cli.isolateFiles
      let mode := if cli.isolateFiles then "isolated" else "in-process"
      IO.println s!"corpus-extract: discovered {files.size} source file(s); driving frontend ({mode}, jobs={jobs})…"
      let (recs, wstats) ←
        if cli.isolateFiles then
          Corpus.extractViaFrontendIsolated projectRoot files cli.opts
            cli.config jobs cli.reverseTimeoutMs outDir cli.resume
        else
          Corpus.extractViaFrontend files tagConfig cli.opts jobs
      IO.println s!"corpus-extract: {wstats.filesOk} ok, {wstats.filesEmpty} empty, \
        {wstats.filesError} error (of {wstats.filesTotal})"
      if wstats.filesError > 0 then
        let resumeHint := if cli.isolateFiles then "; staged shards were retained for --resume" else ""
        throw <| IO.userError s!"extraction failed for {wstats.filesError} file(s){resumeHint}"
      if cli.isolateFiles then
        cleanupShardsRef.set true
      pure recs
    -- Derive `total`/`modules` from the records themselves: the driver returns a
    -- WorkerRunStats (file counters), so `metadata.json`'s record-level counts are
    -- computed here from `records`.
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
    if (← cleanupShardsRef.get) then
      Corpus.cleanupShards outDir
    IO.println s!"corpus-extract: wrote {theorems.size} theorems + {defns.size} definitions to {outDir}"
    return 0

end Corpus

unsafe def main (args : List String) : IO UInt32 :=
  Corpus.runCli args
