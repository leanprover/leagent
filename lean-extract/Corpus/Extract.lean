import Lean
import Corpus.Records
import Corpus.Tags
import WorkerPlugins.ReverseElab

/-!
Core extraction: walk an `Environment` (built by `importModules`) and emit
`ConstRecord`s for each user-relevant declaration.

All work happens in `MetaM` (so `ppExpr` works); IO interleaves at the JSONL
sink via the `emit` callback so we don't materialise every record in memory.
-/

namespace Corpus

open Lean Meta

/-- Configuration for one extraction run. -/
structure ExtractOptions where
  /-- Root module names to import. Also treated as the "owned" prefix tree —
  anything outside is considered external and skipped. -/
  rootModules     : Array Name
  /-- Optional tag config (default = no tags). -/
  tagConfig       : TagConfig := TagConfig.empty
  /-- Include compiler-internal names (e.g. `_aux.*`, `match_<n>`, `eq_<n>`). -/
  includeInternal : Bool := false
  /-- Include declarations marked `private`. -/
  includePrivate  : Bool := true
  /-- Source root for resolving module names to file paths (default = cwd). -/
  sourceRoot      : System.FilePath := "."
  /-- Reverse-elaborate theorem proof terms into verified tactic scripts and
  emit them in the `proof_script` / `proof_method` fields. Off by default
  because it re-elaborates every proof (slower). -/
  reverseElab     : Bool := false
  /-- When reverse-elaborating, also try goal-closing tactics (`simp`, `omega`,
  …) to recover high-level proofs for opaque automation bodies. Off by default:
  it tries a tactic menu across every opaque proof and is ~20× slower than the
  structural+exact path. Requires `reverseElab`. -/
  reverseClosers  : Bool := false
  deriving Inhabited

/-- The kind label we emit per declaration. Mirrors `ConstantInfo`. -/
private def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "def"
  | .thmInfo _     => "theorem"
  | .opaqueInfo _  => "opaque"
  | .quotInfo _    => "quot"
  | .inductInfo _  =>
      if Lean.isStructure env ci.name then "structure" else "inductive"
  | .ctorInfo _    => "ctor"
  | .recInfo _     => "rec"

/-- True if `n` belongs to one of the root prefixes given via `--modules`. -/
private def isOwned (roots : Array Name) (modName : Name) : Bool :=
  roots.any fun root => root == modName || root.isPrefixOf modName

/-- Module name for a constant, if any. -/
private def moduleOf? (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun idx =>
    env.allImportedModuleNames[idx.toNat]!

/-- "Mod.Sub.Leaf" -> "Mod/Sub/Leaf.lean" (relative; no source-root prefix).
The emitted record stores this so the dataset stays portable to other
machines where the source tree may live elsewhere. -/
private def moduleNameToRelPath (modName : Name) : System.FilePath :=
  let parts := modName.componentsRev.reverse.map toString
  let rel : System.FilePath :=
    parts.foldl (init := (⟨""⟩ : System.FilePath))
      (fun acc s => if acc.toString.isEmpty then ⟨s⟩ else acc / s)
  ⟨rel.toString ++ ".lean"⟩

/-- Detect Lean's compiler-synthesized name fragments. These slip past
`isInternalDetail` for some declarations but are never useful corpus
material:
  - `._proof_*`  proof-term lifts from tactic blocks inside `def`s
  - `._eq_*`     auto-generated equation lemmas for definitions / matches
  - `._eqDef`    canonical equation form
  - `._sunfold`  smart-unfolding helper
  - `._unfold`   unfolder helper -/
private def hasGeneratedTag (n : Name) : Bool :=
  let s := n.toString
  let containsTag (tag : String) : Bool := (s.splitOn tag).length > 1
  containsTag "._proof_"
    || containsTag "._eq_"
    || containsTag "._eqDef"
    || containsTag "._sunfold"
    || containsTag "._unfold"

/-- Auto-generated theorems produced by Lean's `def` equation compiler. Their
last name segment is `eq_def` (canonical equation) or `induct` (custom
induction principle for a recursive def). They carry no docstring and no
source range, and they crowd premise tracking with mechanical boilerplate.

We deliberately keep the inductive/structure-level auxiliaries `injEq`,
`inj`, and `sizeOf_spec` — they encode user-relevant facts (constructor
injectivity, sizeOf equations) that may legitimately appear as premises in
authored proofs. -/
private def isGeneratedTheoremSuffix : Name → Bool
  | .str _ s => s == "eq_def" || s == "induct"
  | _        => false

/-- Names not visible to users we should always drop.

We additionally drop structure-projection theorems / functions: when the
parent type is a structure, names like `Foo.field` are auto-generated
projections (for Prop-valued structures these surface as theorems). They
are not authored corpus material and clutter premise tracking. -/
private def alwaysSkip (env : Environment) (n : Name) : Bool :=
  Lean.isAuxRecursor env n
  || Lean.isNoConfusion env n
  || n.isAnonymous
  || hasGeneratedTag n
  || isGeneratedTheoremSuffix n
  || env.isProjectionFn n

/-- Return a sorted list of fully-qualified names with duplicates removed. -/
private def fmtNames (ns : Array Name) : List String :=
  let strs := ns.toList.map toString
  let uniq := strs.eraseDups
  uniq.mergeSort (fun a b => a < b)

/-- True if `n` belongs to a constant in an owned module. -/
private def isOwnedName (env : Environment) (isOwnedMod : Name → Bool)
    (n : Name) : Bool :=
  match moduleOf? env n with
  | none   => false
  | some m => isOwnedMod m

/-- Transitive premise cone for `root`: BFS over `Environment.constants`
following only owned constants. The seed is the direct dep set of `root`.
For each owned constant in the worklist we add its own direct deps; external
or absent constants are skipped (we never drag Init/Std/Mathlib into the
cone). The result is filtered to owned-only and excludes `root`.

Termination: every popped name is added to `visited` before its deps are
enqueued, and `Name`s drawn from a finite environment form a finite set. -/
private def collectPremises (env : Environment) (isOwnedMod : Name → Bool)
    (root : Name) : Array Name := Id.run do
  let some rootCi := env.find? root | #[]
  let mut visited : Std.HashSet Name := {}
  let mut queue   : Array Name := rootCi.getUsedConstantsAsSet.toArray
  visited := visited.insert root
  let mut result  : Array Name := #[]
  while h : queue.size > 0 do
    let n := queue[queue.size - 1]
    queue := queue.pop
    if visited.contains n then continue
    visited := visited.insert n
    -- Only owned constants are reported and only owned bodies are expanded.
    if isOwnedName env isOwnedMod n then
      result := result.push n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet.toArray do
          unless visited.contains d do
            queue := queue.push d
  return result

/-- Should we skip this constant entirely (before doing any heavy work)? -/
private def shouldSkip (env : Environment) (opts : ExtractOptions)
    (name : Name) (ci : ConstantInfo) : Bool := Id.run do
  if alwaysSkip env name then return true
  unless opts.includeInternal do
    if name.isInternalDetail then return true
    -- Constructors and recursors: dropped unless explicitly included; we have
    -- the parent inductive itself, which carries the same information.
    match ci with
    | .ctorInfo _ | .recInfo _ => return true
    | _ => pure ()
  if !opts.includePrivate && Lean.isPrivateName name then return true
  -- External: must belong to an owned module prefix.
  match moduleOf? env name with
  | none => return true  -- builtins / unattached: always skip
  | some m => if !isOwned opts.rootModules m then return true
  return false

/-- Build the record for one accepted constant. -/
private def buildRecord (env : Environment) (opts : ExtractOptions)
    (name : Name) (ci : ConstantInfo) : MetaM ConstRecord := do
  let kind := kindOf env ci
  let typeStr := ((← Meta.ppExpr ci.type).pretty 120).trimAsciiEnd.toString
  -- `allowOpaque := true`: Lean 4.31 gates theorem/opaque values behind this
  -- flag (default false would return `none` for theorems). The extractor needs
  -- proof terms, so we opt in — matching pre-4.31 `value?` behavior.
  let valueStr ← match ci.value? (allowOpaque := true) with
    | none   => pure none
    | some v => do
        let s := ((← Meta.ppExpr v).pretty 120).trimAsciiEnd.toString
        pure (some s)
  -- Reverse-elaborated proof script (theorems only, when enabled). Failures
  -- inside reverse elaboration are swallowed to a null script so a single
  -- pathological proof never aborts the run.
  let mut proofScript? : Option String := none
  let mut proofMethod? : Option String := none
  if opts.reverseElab then
    match ci with
    | .thmInfo _ =>
        if let some v := ci.value? (allowOpaque := true) then
          let r ← (try WorkerPlugins.ReverseElab.reverseProof ci.type v opts.reverseClosers
                   catch _ => pure { script := "", method := "error" })
          proofMethod? := some r.method
          proofScript? := if r.script.isEmpty then none else some r.script
    | _ => pure ()
  let modName? := moduleOf? env name
  let modStr := modName?.map toString |>.getD ""
  -- Source ranges. NOTE (Lean 4.31 port): the byte-level source slicer that
  -- produced `signature`/`body` from `DeclarationRange` + a re-read source file
  -- (`sliceSource`/`colToPos`/`splitStatementProof`) was removed — it depended
  -- on the old flat `String.Pos` (a bare byte index), and 4.31 redesigned
  -- `String.Pos` to be string-dependent (`s.Pos` / `Pos.Raw`). Rather than port
  -- a heuristic that was already slated for replacement, `signature`/`body` are
  -- left `none` here; they will be repopulated by parser-AST navigation
  -- (`parseCommand` → `declSig`/`declVal`) in the frontend/plugin rework. The
  -- line/col ranges and file path below are unaffected.
  let ranges? ← Lean.findDeclarationRanges? name
  let mut startLine? : Option Nat := none
  let mut startCol?  : Option Nat := none
  let mut endLine?   : Option Nat := none
  let mut endCol?    : Option Nat := none
  let mut filePath?  : Option String := none
  let signature? : Option String := none
  let body?      : Option String := none
  if let some r := ranges? then
    let p := r.range.pos
    let q := r.range.endPos
    startLine? := some p.line
    startCol?  := some p.column
    endLine?   := some q.line
    endCol?    := some q.column
    if let some modName := modName? then
      filePath? := some (moduleNameToRelPath modName).toString
  -- Doc string (independent of source slicing).
  let doc? ← (Lean.findDocString? env name : IO (Option String))
  -- Direct deps from union of type and value used-constants.
  let depsArr := ci.getUsedConstantsAsSet.toArray
  let depsList :=
    (fmtNames depsArr).filter (fun s => s != name.toString)
  -- Transitive premise cone: only non-empty for declarations that carry a
  -- term (theorems and defs with bodies). Axioms / opaques / inductives /
  -- quots / structures get an empty list.
  let isOwnedMod := isOwned opts.rootModules
  let premisesList : List String := match ci with
    | .thmInfo _ | .defnInfo _ =>
        let names := collectPremises env isOwnedMod name
        (fmtNames names).filter (fun s => s != name.toString)
    | _ => []
  -- Transitive axioms (only meaningful for theorems).
  let axList ← match ci with
    | .thmInfo _ =>
        let axs ← Lean.collectAxioms name
        pure (fmtNames axs)
    | _ => pure []
  let isPriv := Lean.isPrivateName name
  let isProt := Lean.isProtected env name
  let kindStr :=
    if isPriv && kind == "theorem" then "private theorem"
    else if isPriv && kind == "def" then "private def"
    else kind
  let tags := opts.tagConfig.matchTags modStr
  return {
    name        := name.toString
    kind        := kindStr
    module      := modStr
    file        := filePath?
    startLine   := startLine?
    startCol    := startCol?
    endLine     := endLine?
    endCol      := endCol?
    signature   := signature?
    body        := body?
    type        := typeStr
    value       := valueStr
    proofScript := proofScript?
    proofMethod := proofMethod?
    doc         := doc?
    deps        := depsList
    premises    := premisesList
    axioms      := axList
    isProtected := isProt
    isPrivate   := isPriv
    tags        := tags
  }

/-- Per-kind counters returned alongside the run for `metadata.json`. -/
structure RunStats where
  total   : Nat := 0
  byKind  : List (String × Nat) := []
  modules : List String := []
  deriving Inhabited

private def bumpKind (counts : List (String × Nat)) (k : String) :
    List (String × Nat) :=
  let rec go : List (String × Nat) → List (String × Nat)
    | [] => [(k, 1)]
    | (k', n) :: rest =>
        if k == k' then (k', n + 1) :: rest else (k', n) :: go rest
  go counts

/-- Drop theorems with no source range. These are compiler-synthesized
auxiliary lemmas (`.injEq`, `.sizeOf_spec`, `.brecOn`, `.ofNat_toCtorIdx`,
…) that survive the `alwaysSkip` filters but have no human-authored
source: they exist only as elaborated terms in the environment. They
add bulk to the corpus without adding learnable content. -/
private def isSyntheticTheorem (ci : ConstantInfo) : MetaM Bool := do
  match ci with
  | .thmInfo _ => pure (← Lean.findDeclarationRanges? ci.name).isNone
  | _          => pure false

/-- Walk every imported constant, emit a record for the ones that survive
filtering, and return run statistics. The `emit` callback writes to IO so this
function stays bounded in memory. -/
def extractAll (env : Environment) (opts : ExtractOptions)
    (emit : ConstRecord → IO Unit) : MetaM RunStats := do
  let mut stats : RunStats := {}
  let mut modSet : Std.HashSet String := {}
  -- `map₁` is the imported half of the SMap; `map₂` is empty for us.
  let consts := env.constants.map₁
  for (name, ci) in consts.toList do
    if shouldSkip env opts name ci then continue
    if (← isSyntheticTheorem ci) then continue
    let record ← buildRecord env opts name ci
    let _ ← (emit record : IO Unit)
    stats := { stats with
      total := stats.total + 1
      byKind := bumpKind stats.byKind record.kind }
    unless modSet.contains record.module do
      modSet := modSet.insert record.module
  let modSorted := modSet.toList.mergeSort (fun a b => a < b)
  return { stats with modules := modSorted }

/-- Buffered variant: returns the full list of accepted records along with run
stats. Uses linear memory in the number of records — fine for typical projects
(O(thousands)) but if a future caller pushes O(100K)+ records they should
reach for `extractAll` and stream instead. -/
def extractAllBuffered (env : Environment) (opts : ExtractOptions) :
    MetaM (Array ConstRecord × RunStats) := do
  let mut stats : RunStats := {}
  let mut modSet : Std.HashSet String := {}
  let mut buf : Array ConstRecord := #[]
  let consts := env.constants.map₁
  for (name, ci) in consts.toList do
    if shouldSkip env opts name ci then continue
    if (← isSyntheticTheorem ci) then continue
    let record ← buildRecord env opts name ci
    buf := buf.push record
    stats := { stats with
      total := stats.total + 1
      byKind := bumpKind stats.byKind record.kind }
    unless modSet.contains record.module do
      modSet := modSet.insert record.module
  let modSorted := modSet.toList.mergeSort (fun a b => a < b)
  return (buf, { stats with modules := modSorted })

/-- Build a `MetaM` runner over a freshly-imported environment and execute
`act`. Only the environment matters here; all other contexts are default.

`maxHeartbeats := 0` disables the global deterministic-timeout budget: this is a
batch tool that walks an entire environment in a single `MetaM` action, so the
default 200k cumulative ceiling would trip partway through a large project.
Per-proof verification cost is bounded locally instead (see
`ReverseElab.tryElab`, which resets the heartbeat baseline and caps each
attempt), so removing the global ceiling does not let any single proof hang. -/
def runMetaOnEnv {α} (env : Environment) (act : MetaM α) : IO α := do
  let coreCtx : Core.Context :=
    { fileName := "<corpus-extract>", fileMap := default, maxHeartbeats := 0 }
  let coreSt  : Core.State   := { env := env }
  let (a, _, _) ← act.toIO coreCtx coreSt
  return a

end Corpus
