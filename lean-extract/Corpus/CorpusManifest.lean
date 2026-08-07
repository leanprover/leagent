/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Lean.Util.CollectAxioms
import Lean.PrettyPrinter
import Corpus.CollectCommon
import Corpus.ReverseElab
import Corpus.Frontend
import Corpus.SourceSyntax
import Corpus.ProofMetrics
import Corpus.Verify
import Corpus.ChildProcess
import Corpus.Options

/-!
The corpus collector: for each user declaration in an elaborated file, computes
the data a theorem/definition CORPUS needs — fully-qualified name, kind,
pretty-printed type and (for defs/theorems) value, direct dependencies,
transitive axioms/premises, source signature/body, and (optionally) a verified
reverse-elaborated `proofScript`.

`corpusManifestCore` is the entry point the driver calls: it runs the `CoreM` fold
below against a frontend-elaborated environment via `Corpus.Frontend.runCollectorOn`
(so the fold sees the file's TRUE post-elaboration environment). The `source` string
and per-command `Syntax` array the source reconstruction needs
(`buildSourceMap`/`buildSimpArgMap`) come from `Frontend.ElabResult`.

A pathological proof term can pin the compute thread it runs on; the size and
wall-clock guards below bound that (see `reverseNodeCeiling` and the
cheap-first/deadline scheduling in `foldCorpusEntries`).
-/

namespace Corpus

open Lean
open SourceSyntax

/-- One declaration in the corpus manifest. -/
structure CorpusManifestEntry where
  /-- Fully-qualified constant name. -/
  name        : String
  /-- `axiom` / `theorem` / `definition` / `opaque` / `inductive` / `constructor`
  / `recursor` / `quotient`. -/
  kind        : String
  /-- The module that elaborated this constant (the file under study). -/
  module      : String
  /-- Pretty-printed elaborated type (line width 120). -/
  type        : String
  /-- Pretty-printed term-level value, for defs/theorems; `none` otherwise.
  Theorem values are included (`value?` is read with `allowOpaque := true`). -/
  value?      : Option String
  /-- Docstring, if any. -/
  doc?        : Option String
  /-- Direct dependencies: sorted, deduped constant names appearing in
  `type ∪ value`, excluding the constant itself. -/
  deps        : Array String
  /-- Transitive axioms (`collectAxioms`), sorted. -/
  axioms      : Array String
  /-- `true` iff `axioms` contains `sorryAx`. -/
  hasSorry    : Bool
  /-- SOURCE text of the statement: binders + `: type`, but NOT the `:=`/body and
  NOT the leading doc comment. Reconstructed by navigating the command `Syntax`
  (the `declSig`/`optDeclSig` node). `none` for constants with no source command
  (companions, projections, recursors, anonymous instances) or with no type
  ascription. -/
  signature   : Option String
  /-- SOURCE text of the value/proof: the `declVal` (for `:= term`, just the
  term; for equations/`where`, the whole `declVal`). `none` when there is no
  source command or no value (e.g. `axiom`). -/
  body        : Option String
  /-- FULL SOURCE of the declaration command: doc comment + modifiers + signature
  + body, verbatim and re-elaboratable. Captured for EVERY kind (including
  `inductive`/`structure`, whose `signature`/`body` are `none`). This is what a
  self-contained record inlines for its owned `def`/`inductive`/`structure`
  dependencies. `none` only for constants with no source command (companions,
  projections, recursors, anonymous instances). -/
  declSource  : Option String
  /-- Dotted enclosing namespace the declaration was elaborated under (e.g.
  `"LeanSQLite.Engine"`; empty at top level). The TRUE declaring namespace, from
  the command-stack walk — NOT derivable from `name` (which cannot be split back
  into namespace vs. dotted short name). Lets a self-contained record wrap the
  decl's verbatim (unqualified) `declSource` under the right `namespace`. -/
  declNamespace : String
  /-- Verbatim source of the scope commands in effect at the declaration,
  outermost first (the `namespace`/`section` openers plus any live
  `open`/`variable`/`universe`/`set_option`). Replaying these — then closing
  namespaces/sections — reproduces the declaration's elaboration scope in an
  assembled standalone file. -/
  scopePrelude : Array String
  /-- The DIRECT imports of the declaration's file (`env.imports`, the actual
  `import X` header lines), as dotted module names. A self-contained record needs
  these to reconstruct the file's baseline: the assembler imports the
  non-project-owned ones (Init/Std/Mathlib) and inlines the owned cone. Identical
  for every declaration elaborated in the same file. -/
  fileImports : Array String
  /-- Transitive premise cone: every PROJECT-OWNED constant reachable through the
  term of this declaration (BFS over `getUsedConstantsAsSet`, expanding only
  owned bodies so core/Std/Mathlib is never dragged in), sorted and excluding
  the declaration itself. Non-empty only for `theorem`/`definition` (constants
  that carry a term). "Owned" = elaborated by the file under study (the worker's
  main module) or by another module sharing the project root prefix. -/
  premises    : Array String
  /-- Mechanically reverse-elaborated tactic script (from the proof `Expr`),
  e.g. `by intro h; exact …`. Populated only for theorems; `none` otherwise.
  Every emitted script is VERIFIED to re-elaborate to a defeq proof with the
  `errToSorry := false` + `Expr.hasSorry` guards (so `sorry`/partial scripts are
  rejected, not stored). Re-elaboration happens in the file's TRUE context with
  registered tactics. -/
  proofScript : Option String
  /-- Which reverse-elaboration rung produced `proofScript`: `structural`,
  `rfl`, `exact`, `intro_rfl`, `intro_exact` (genuine decompositions);
  with `--closers`, also `(intro_)simp`/`omega`/`assumption`/… (a no-arg closer
  fired) and `(intro_)simp_args` (an author-sourced `simp [..]` harvested from the
  proof fired); `*_opaque`/`exact_whole` (verified but automation residue / zero
  decomposition), `fail` (nothing verified), or `skipped_large` (proof term
  exceeded `reverseNodeCeiling`, so reverse-elaboration was not attempted — it
  would risk pinning the worker for no expected gain). `none` for non-theorems. -/
  proofMethod : Option String
  /-- `true` iff the constant's name is `private`. The client cannot compute
  this (no `Environment`), and it drives the `private def`/`private theorem`
  kind labels in the corpus schema. -/
  isPrivate   : Bool
  /-- `true` iff the constant is marked `protected`. -/
  isProtected : Bool
  /-- `true` iff this `inductive` is actually a `structure`. Lets the corpus
  schema emit `structure` vs `inductive`; needs the `Environment`. -/
  isStructure : Bool
  /-- 1-based start line of the declaration's full source range
  (`findDeclarationRanges?.range`, doc-comment-inclusive), or `none`. -/
  startLine   : Option Nat
  /-- 0-based start column. -/
  startCol    : Option Nat
  /-- 1-based end line. -/
  endLine     : Option Nat
  /-- 0-based end column. -/
  endCol      : Option Nat
  /-- Proof-complexity metrics for the record schema, populated only under
  `--proof-metrics` (`opts.proofMetrics`). `none` otherwise, which maps to the
  record's empty column forms. The tactic half is `ProofMetrics.TacticMetrics`
  (from proof syntax); the two `proofTerm*` fields are the semantic half (from the
  elaborated proof `Expr`, theorems only). See `Corpus.ProofMetrics`. -/
  metrics       : Option ProofMetrics.TacticMetrics := none
  /-- Which body `metrics` was measured from: `sourceAuthor` / `sourceReverseElab`,
  or `none` when `metrics` is `none`. See `ConstRecord.tacticMetricsSource`. -/
  metricsSource : Option String := none
  /-- Semantic family: distinct sub-expressions of the elaborated proof term
  (`ReverseElab.distinctNodes`). `none` for non-theorems or flag off. -/
  proofTermSize : Option Nat := none
  /-- Semantic family: approximate depth of the elaborated proof term. `none` as
  `proofTermSize`. -/
  proofTermDepth : Option Nat := none

open Lean.PrettyPrinter

/-- Pretty-print an `Expr` at width 120 (lifting the `MetaM`-based `ppExpr`). -/
private def ppExpr120 (e : Expr) : CoreM String := do
  let fmt ← Lean.Meta.MetaM.run' (Lean.Meta.ppExpr e)
  return (fmt.pretty 120).trimAsciiEnd.copy

/-- Proof-term size ceiling (distinct sub-expressions, `ReverseElab.distinctNodes`)
above which reverse-elaboration is SKIPPED outright, emitting `proofMethod :=
"skipped_large"`. This is the primary guard against a pathological proof pinning
the compute thread it runs on.

Why a size pre-filter rather than a time/heartbeat budget: proof terms are freshly
elaborated, and re-elaborating + `isDefEq`-checking a candidate against a huge term
can run for
*minutes* of wall time. Neither bound the latency reliably — heartbeats track
work not wall time (a giant `isDefEq` accrues few), and cooperative cancellation
(`IO.CancelToken`) does not preempt a single in-flight `isDefEq`/tactic call
mid-flight. The size is known up front and O(term) to compute, so skipping is the
one bound that fires *before* any expensive work starts. And it costs nothing
real: measured on LeanSQLite, every genuine decomposition has ≤266 distinct nodes
(most ≤150) and completes in <100ms, while the proofs that hang/`fail` are
1400–3000+ nodes — so a 600 ceiling (>2× the largest observed success) skips only
proofs that were going to be `fail`/timeout anyway, never a real result.
Re-measure if the recognizer set or corpus changes materially. -/
def reverseNodeCeiling : Nat := 600

/-- Reverse-elaborate one theorem, but SKIP proofs whose term exceeds
`reverseNodeCeiling` (emitting `skipped_large`) so a pathological proof never
pins the worker. The skip is the bound that matters; see `reverseNodeCeiling`
for why a size pre-filter beats a time/heartbeat budget here. The aggregate
heartbeat budget inside `reverseProof` still bounds work for the in-range case. -/
def reverseProofGuarded (ty v : Expr) (enableClosers : Bool)
    (extraClosers : Array String := #[])
    : CoreM ReverseElab.ScriptResult := do
  if ReverseElab.distinctNodes v > reverseNodeCeiling then
    return { script := "", method := "skipped_large" }
  -- `tryCatchRuntimeEx` swallows a heartbeat/recursion blowup on an in-range
  -- proof to a null script (rather than aborting the whole request); genuine
  -- interrupts (worker shutdown) still propagate.
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
    tryCatchRuntimeEx
      (Lean.Meta.MetaM.run' (ReverseElab.reverseProof ty v enableClosers extraClosers))
      (fun _ => pure { script := "", method := "error" })

/-- The constants an inductive/structure DEPENDS ON, including its field/argument
types. A structure's own `type` is just `Type u` (`getUsedConstantsAsSet = #[]`) —
the field types live in the CONSTRUCTOR's type (`Cache.mk : PageNo → … → Cache`),
so `info.getUsedConstantsAsSet` alone misses every field-type dependency (e.g.
`Cache` would not list `Node`/`PageNo`). We union the inductive's own used
constants with each constructor's, dropping the inductive's own auto-generated
companions (`.mk`, other ctors, the type itself). Non-inductives fall back to the
plain used-constant set. This makes `deps` sound for topological reconstruction of
a self-contained record (a struct must be emitted after its field types). -/
private def usedConstantsFor (env : Environment) (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo iv =>
      let ctorTypeConsts := iv.ctors.foldl (init := info.getUsedConstantsAsSet) fun acc ctor =>
        match env.find? ctor with
        | some ci => acc.union ci.getUsedConstantsAsSet
        | none    => acc
      -- Drop the family's own names (the type + its constructors): a decl never
      -- depends on itself, and the ctors are companions, not external deps.
      let ownNames := (iv.all ++ iv.ctors).foldl (·.insert ·) (∅ : Std.HashSet Name)
      ctorTypeConsts.toArray.filter (!ownNames.contains ·)
  | _ => info.getUsedConstantsAsSet.toArray

/-- Sorted, deduped fully-qualified names (excluding `self`), each normalized to
its resolvable display form (`CollectCommon.displayName` unmangles `_private.…`).
`self` is compared in the same normalized form so a decl never lists itself even
when private. Dedup+sort happen AFTER normalization, so two references that only
differed by mangling collapse to one. -/
private def fmtNames (self : Name) (ns : Array Name) : Array String :=
  let selfStr := (CollectCommon.displayName self).toString
  let strs := ns.toList.map (fun n => (CollectCommon.displayName n).toString)
  let uniq := strs.eraseDups.filter (· != selfStr)
  (uniq.mergeSort (· < ·)).toArray

/-! ## Corpus-eligibility filter

The shared predicates (`CollectCommon.alwaysSkip` etc.) exclude compiler
noise. This filter additionally drops constructors/recursors (unless
`--include-internal`), private names (unless `--include-private`), and
range-less synthetic theorems (`.injEq`/`.sizeOf_spec`/`.brecOn`/…). -/


/-- The full corpus-eligibility test applied per constant inside the collector,
mirroring `Extract.shouldSkip` (minus the owned-module check — in the worker the
plugin already restricts to module-local user constants) plus
`Extract.isSyntheticTheorem` (drop range-less synthetic theorems). Returns
`true` to KEEP the constant. -/
private def corpusEligible (env : Environment) (includeInternal includePrivate : Bool)
    (name : Name) (info : ConstantInfo) : CoreM Bool := do
  if CollectCommon.alwaysSkip env name then return false
  unless includeInternal do
    -- A private decl (`_private.…`) is internal-detail by name but is user-authored
    -- material: keep it iff its UNMANGLED user name is itself not internal-detail
    -- (a genuine authored private decl, not a private compiler shard). Its ultimate
    -- inclusion is still gated by `includePrivate` below. Non-private internal
    -- details (`match_…`, `_aux`, …) are dropped as before.
    let genuinePrivate :=
      Lean.isPrivateName name && !(Lean.privateToUserName name).isInternalDetail
    if name.isInternalDetail && !genuinePrivate then return false
    match info with
    | .ctorInfo _ | .recInfo _ => return false
    | _ => pure ()
  if !includePrivate && Lean.isPrivateName name then return false
  -- Range-less synthetic theorems (`.injEq`, `.sizeOf_spec`, `.brecOn`, …).
  match info with
  | .thmInfo _ => return (← Lean.findDeclarationRanges? name).isSome
  | _          => return true



/-- The SCOPE a declaration was elaborated under: the enclosing namespace path and
the verbatim source of every scope-setting command in effect. -/
structure DeclScope where
  /-- Dotted enclosing namespace, e.g. `"LeanSQLite.Engine"` (empty at top level).
  This is the TRUE declaring namespace — recoverable only by walking the command
  stack, NOT from the constant's full name (which cannot be split back into
  namespace vs. dotted short name: `LeanSQLite.Engine.Node.lookupKey` declared as
  `def Node.lookupKey` under `namespace LeanSQLite.Engine` has short name
  `Node.lookupKey`, not `lookupKey`). -/
  «namespace» : String
  /-- Verbatim source of the scope commands active at the declaration, outermost
  first: the `namespace`/`section` openers plus any `open`/`variable`/`universe`/
  `set_option` still in scope. Replaying these (then closing namespaces/sections
  with matching `end`s) reproduces the declaration's elaboration scope. -/
  prelude : Array String
  deriving Inhabited

/-- Build a map from each declaration's key position to its `DeclScope`, by a
single left-to-right walk of the file's top-level `commands` maintaining a scope
stack. `namespace N`/`section [id]` push (tracking the name for the dotted path
and for the matching `end`); `end [id]` pops; `open`/`variable`/`universe`/
`set_option` are recorded as active scope entries (also popped when their
enclosing section closes). Every `declaration` command encountered is filed with
a snapshot of the current namespace path + active scope-command sources.

`open X in foo` / `set_option ... in foo` attach to a SINGLE declaration and are
part of that decl's own command syntax (hence already in `decl_source`), so they
never appear as standalone top-level commands here — this walk only sees
command-level scoping, which is exactly what must be replayed AROUND the decl. -/
private def buildScopeMap (src : String) (commands : Array Syntax)
    : Std.HashMap (Nat × Nat) DeclScope := Id.run do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) DeclScope := {}
  -- Stack of open scopes. Each frame: (kind-name for the dotted path or "" if the
  -- entry is not a namespace, isNamespace, verbatim source, endName for matching).
  -- We keep namespace/section as structural frames and open/variable/... as
  -- content frames that live until their enclosing section closes.
  let mut nsPath : Array String := #[]          -- namespace components, for the dotted path
  let mut scopeStack : Array (Bool × String) := #[]  -- (isSectionOrNamespace, verbatimSrc); content entries have isSection=false
  -- For matching `end`, track how many scopeStack entries + nsPath comps each
  -- opener contributed. A namespace/section opener records a barrier.
  let mut barriers : Array (Nat × Nat × Option String) := #[]  -- (scopeStackLen, nsPathLen, nsCompPushed?)
  for cmdStx in commands do
    let k := cmdStx.getKind
    let srcOf : Option String := sliceTrimmed cmdStx src
    if (declarationId? cmdStx).isSome then
      for key in declarationKeys fileMap cmdStx do
        m := m.insert key { «namespace» := ".".intercalate nsPath.toList,
                            prelude := scopeStack.map (·.2) }
    else if k == ``Lean.Parser.Command.namespace then
      -- `namespace <id>`: the identifier is the last significant child.
      let comp := (cmdStx.getArg 1).getId.toString
      barriers := barriers.push (scopeStack.size, nsPath.size, some comp)
      nsPath := nsPath.push comp
      if let some s := srcOf then scopeStack := scopeStack.push (true, s)
      else scopeStack := scopeStack.push (true, s!"namespace {comp}")
    else if k == ``Lean.Parser.Command.section then
      barriers := barriers.push (scopeStack.size, nsPath.size, none)
      if let some s := srcOf then scopeStack := scopeStack.push (true, s)
      else scopeStack := scopeStack.push (true, "section")
    else if k == ``Lean.Parser.Command.end then
      -- Pop to the most recent barrier.
      if let some (ssLen, nsLen, _) := barriers.back? then
        barriers := barriers.pop
        scopeStack := scopeStack.extract 0 ssLen
        nsPath := nsPath.extract 0 nsLen
    else if k == ``Lean.Parser.Command.open
         || k == ``Lean.Parser.Command.variable
         || k == ``Lean.Parser.Command.universe
         || k == ``Lean.Parser.Command.set_option then
      if let some s := srcOf then scopeStack := scopeStack.push (false, s)
  return m

/-- Syntax kinds of the simp-family tactics whose argument-lists we harvest from
the source proof to use as reverse-elaboration closer candidates. `simp only` is
the `simp` kind with an `only` child, so both forms are covered by these two. -/
private def simpKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.simpAll]

/-- Collect EVERY sub-node of `stx` whose kind is in `kinds` (pre-order DFS, all
matches — unlike `findByKind` which stops at the first). -/
private partial def collectByKind (stx : Syntax) (kinds : List SyntaxNodeKind)
    (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if kinds.contains stx.getKind then acc.push stx else acc
  match stx with
  | .node _ _ args => args.foldl (fun acc a => collectByKind a kinds acc) acc
  | _              => acc

/-- Collect every identifier leaf under `stx`. -/
private partial def collectIdents (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .ident _ _ n _ => acc.push n
  | .node _ _ args => args.foldl (fun acc a => collectIdents a acc) acc
  | _              => acc

/-- Harvest a POOLED, GLOBAL-LEMMA argument set for `simp`/`simp_all` from a
declaration's proof syntax: the union of every identifier the author named inside
any simp-family call, keeping only those that resolve to a global constant.

Intended as an "argument oracle": a verbatim single `simp [a]` from the source
almost never closes the goal alone (it is one step of a multi-tactic chain), but
the author's lemmas signal WHICH rewrites matter, and `simp [..]` is order-
insensitive and tolerant of extras, so one combined `simp [a,…,n]` over the pool
is an informed guess at a closer.

STATUS (measured on LeanSQLite, both verbatim and pooled): 0 wins. The plumbing
is kept behind `--closers` but is currently low-yield, for TWO reasons worth
recording before anyone revisits:
  1. Source idents are resolved here WITHOUT each simp call's true elaboration
     context, so a bare name resolves wrong — e.g. the author's local `Disk.read`
     resolves to Mathlib's `MonadReader.read`. Fixing this needs per-call context
     (or sourcing names from the elaborated term's `getUsedConstantsAsSet`, i.e.
     the `premises` cone — a broader but correctly-resolved pool).
  2. The pool picks up structural non-lemmas (`if_pos`, `And.intro`, `rfl`) that
     are not useful `simp` lemmas, and one bad/unknown name fails the WHOLE
     `simp [..]`. A useful version would filter to actual simp-eligible lemmas.

We drop non-global idents (local hyps `hi`/`heq`/`this`, `*`, config tokens). The
pool is verified like any closer, so a wrong guess is simply dropped — never
unsound, just (today) unproductive. -/
private def harvestSimpPool (cmdStx : Syntax) : CoreM (Array Name) := do
  let env ← getEnv
  let opts ← getOptions
  let ns ← getCurrNamespace
  let openDecls ← getOpenDecls
  let mut pool : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  for node in collectByKind cmdStx simpKinds do
    for id in collectIdents node do
      -- Resolve to a global constant: direct hit, or via the current opens.
      let resolved? : Option Name :=
        if env.contains id then some id
        else match (ResolveName.resolveGlobalName env opts ns openDecls id).filter (·.2.isEmpty) with
          | (n, _) :: _ => some n
          | []          => none
      if let some n := resolved? then
        unless seen.contains n do
          seen := seen.insert n
          pool := pool.push n
  return pool

/-- Render the pooled lemmas as candidate closer tactic strings: one combined
`simp [..]` and one `simp_all [..]`. Empty pool ⇒ no candidates (bare `simp`/
`simp_all` are already in the no-arg menu). -/
private def simpPoolClosers (pool : Array Name) : Array String :=
  if pool.isEmpty then #[]
  else
    let argList := ", ".intercalate (pool.toList.map toString)
    #[s!"simp [{argList}]", s!"simp_all [{argList}]"]

/-- Map each declaration key `(line, column)` to the pooled-lemma simp
closer candidates harvested from its proof syntax (see `harvestSimpPool`). Keyed
like `buildSourceMap` so `buildEntry` can look up a constant's candidates by its
`findDeclarationRanges?` selection position. -/
private def buildSimpArgMap (src : String) (commands : Array Syntax)
    : CoreM (Std.HashMap (Nat × Nat) (Array String)) := do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) (Array String) := {}
  for cmdStx in commands do
    if (declarationId? cmdStx).isSome then
      let pool ← harvestSimpPool cmdStx
      for key in declarationKeys fileMap cmdStx do
        m := m.insert key (simpPoolClosers pool)
  return m


/-- Hard wall-clock budget for a single theorem's reverse-elab child process. -/
def reverseProofTimeoutMs : Nat := 15000

/-- Small proofs are safe and much faster to reverse-elaborate in the already
elaborated file process. Larger proofs still use the killable child path below,
because a single `isDefEq` on an automation-heavy term can otherwise pin the
collector in wall time despite heartbeat limits. -/
def reverseInProcessNodeCeiling : Nat := 250

private def parseScriptResult (stdout : String) : Option ReverseElab.ScriptResult :=
  match Json.parse stdout.trimAscii.toString >>= fromJson? with
  | .ok r => some r
  | .error _ => none

/-- The complete request for one reverse-elaboration child: which theorem, in which
file, and whether to try closers. Serialized as ONE JSON argument, so parent and
child share a single encoding (see `Corpus.ExtractOneRequest` for the same pattern on
the file-extraction child). -/
structure ReverseOneRequest where
  sourceFile : System.FilePath
  module     : Name
  decl       : Name
  closers    : Bool := false
  deriving Inhabited, ToJson, FromJson

/-- The flag that carries a `ReverseOneRequest` to the child. -/
def reverseOneFlag : String := "--internal-reverse-one"

/-- Internal child-process entry point: elaborate one file, reverse-elaborate one
theorem in-process, print the `ScriptResult` as JSON in `Main.lean`. -/
unsafe def reverseOneInFile (absPath : System.FilePath) (moduleName declName : Name)
    (closers : Bool) : IO ReverseElab.ScriptResult := do
  Frontend.initFrontend
  let importLock : Frontend.ImportLock ← Std.Mutex.new ()
  let df : Discover.DiscoveredFile := {
    absPath := absPath
    module := moduleName
    relPath := absPath.toString
  }
  let r ← Frontend.elaborateFile importLock df
  Frontend.runCollectorOn r do
    let env ← getEnv
    let some info := env.find? declName
      | return { script := "", method := "error" }
    match info with
    | .thmInfo _ =>
        match info.value? (allowOpaque := true) with
        | none => return { script := "", method := "error" }
        | some v =>
            let simpArgMap ← if closers then buildSimpArgMap r.source r.commands else pure {}
            let ranges? ← Lean.findDeclarationRanges? info.name
            let extraClosers := if closers then
                match ranges? with
                | some rg => simpArgMap.getD (rg.selectionRange.pos.line, rg.selectionRange.pos.column) #[]
                | none    => #[]
              else #[]
            reverseProofGuarded info.type v closers extraClosers
    | _ => return { script := "", method := "error" }

/-- Run one theorem's reverse-elab in a child process so a pathological proof can
be killed without pinning the main extraction. -/
def reverseProofInChild (file : Frontend.ElabResult) (declName : Name)
    (enableClosers : Bool) (timeoutMs : Nat := reverseProofTimeoutMs)
    : CoreM ReverseElab.ScriptResult := do
  let exe ← IO.appPath
  let request : ReverseOneRequest := {
    sourceFile := file.file.absPath, module := file.file.module
    decl := declName, closers := enableClosers }
  let args := #[reverseOneFlag, (toJson request).compress]
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := args
    stdin := .null
    stdout := .piped
    stderr := .piped
    setsid := false -- Inherit the isolated file worker's process group.
  }
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let started ← IO.monoMsNow
  match (← ChildProcess.waitWithDeadline child started timeoutMs) with
  | none =>
      let _ ← IO.wait stdoutTask
      let _ ← IO.wait stderrTask
      IO.eprintln s!"corpus-extract: reverse-elab timed out for {declName} after {timeoutMs}ms"
      return { script := "", method := "timeout" }
  | some code =>
      let stdout ← IO.ofExcept (← IO.wait stdoutTask)
      let stderr ← IO.ofExcept (← IO.wait stderrTask)
      if code != 0 then
        IO.eprintln s!"corpus-extract: reverse-elab child failed for {declName} (exit {code}): {stderr.trimAscii}"
        return { script := "", method := "error" }
      match parseScriptResult stdout with
      | some r => return r
      | none =>
          IO.eprintln s!"corpus-extract: reverse-elab child returned invalid JSON for {declName}: {stdout.trimAscii}"
          return { script := "", method := "error" }

/-- Reverse-elaborate using the already-elaborated file for small proof terms and
the killable one-theorem child process for larger terms. This avoids re-elaborating
the same file once per cheap theorem while preserving hard wall-clock containment
for the proofs most likely to hang. -/
def reverseProofHybrid (file : Frontend.ElabResult) (declName : Name)
    (ty v : Expr) (enableClosers : Bool) (extraClosers : Array String)
    : CoreM ReverseElab.ScriptResult := do
  let nodes := ReverseElab.distinctNodes v
  if nodes > reverseNodeCeiling then
    return { script := "", method := "skipped_large" }
  if nodes ≤ reverseInProcessNodeCeiling then
    reverseProofGuarded ty v enableClosers extraClosers
  else
    reverseProofInChild file declName enableClosers

private def shouldSkipReverse (reverseSkip : Array String) (info : ConstantInfo) : Bool :=
  let rawName := info.name.toString
  let displayName := (CollectCommon.displayName info.name).toString
  reverseSkip.any fun skip => skip == rawName || skip == displayName

/-- The per-file source maps every entry is built against, keyed by the declaration's
selection position. Derived once per file from `Frontend.ElabResult` (see
`SourceMaps.of`) and read for every constant, so they travel as one value rather than
four positional arguments. -/
structure SourceMaps where
  /-- Position → (signature, body) source slices. -/
  sig        : Std.HashMap (Nat × Nat) (Option String × Option String) := {}
  /-- Position → the full declaration command's source. -/
  declSource : Std.HashMap (Nat × Nat) String := {}
  /-- Position → the enclosing namespace + live scope commands. -/
  scope      : Std.HashMap (Nat × Nat) DeclScope := {}
  /-- Position → `simp [..]` argument lists harvested from that proof, for
  `--closers`. Empty unless closers are enabled (building it walks every proof). -/
  simpArgs   : Std.HashMap (Nat × Nat) (Array String) := {}
  /-- Position → tactic-family proof metrics. Empty unless `--proof-metrics` is on
  (building it walks every proof's syntax). -/
  metrics    : Std.HashMap (Nat × Nat) ProofMetrics.TacticMetrics := {}

private def buildEntry (maps : SourceMaps) (opts : CollectOptions)
    (info : ConstantInfo)
    (attemptReverse : Bool := true) (reverseFile? : Option Frontend.ElabResult := none)
    : CoreM CorpusManifestEntry := do
  let env ← getEnv
  let typeStr ← ppExpr120 info.type
  let value? ← match info.value? (allowOpaque := true) with
    | some v => some <$> ppExpr120 v
    | none   => pure none
  let axs ← Lean.collectAxioms info.name
  let allAxStrs := (axs.map toString).qsort (· < ·)
  let hasSorry := allAxStrs.contains (toString ``sorryAx)
  -- Only theorems report their axioms in the corpus schema; `hasSorry` is still
  -- derived from the full set.
  let axStrs := match info with
    | .thmInfo _ => allAxStrs
    | _          => #[]
  let deps := fmtNames info.name (usedConstantsFor env info)
  let doc? ← findDocString? env info.name
  let modStr := match env.getModuleIdxFor? info.name with
    | some idx => (env.allImportedModuleNames[idx.toNat]?).map toString |>.getD ""
    | none     => env.mainModule.toString
  -- Declaration ranges, fetched once. `selectionRange` (the name token) keys the
  -- sig/body map; `range` (the whole decl, doc-comment-inclusive) gives the
  -- start/end line-cols.
  let ranges? ← Lean.findDeclarationRanges? info.name
  let (signature, body) :=
    match ranges? with
    | some r => maps.sig.getD (r.selectionRange.pos.line, r.selectionRange.pos.column) (none, none)
    | none   => (none, none)
  let declSource :=
    match ranges? with
    | some r => maps.declSource[(r.selectionRange.pos.line, r.selectionRange.pos.column)]?
    | none   => none
  let declScope :=
    match ranges? with
    | some r => maps.scope[(r.selectionRange.pos.line, r.selectionRange.pos.column)]?
    | none   => none
  let (startLine, startCol, endLine, endCol) :=
    match ranges? with
    | some r => (some r.range.pos.line, some r.range.pos.column,
                 some r.range.endPos.line, some r.range.endPos.column)
    | none   => (none, none, none, none)
  let isPrivate := Lean.isPrivateName info.name
  let isProtected := Lean.isProtected env info.name
  let isStructure := match info with
    | .inductInfo _ => Lean.isStructure env info.name
    | _             => false
  -- Transitive premise cone (project-owned constants). Only meaningful for
  -- declarations carrying a term — theorems and defs; axioms/opaques/inductives/
  -- ctors/recs/quots get an empty list.
  let premises := match info with
    | .thmInfo _ | .defnInfo _ =>
        let root := CollectCommon.projectRoot env
        fmtNames info.name (CollectCommon.collectPremises env (CollectCommon.isOwnedName env root) info.name)
    | _ => #[]
  -- Reverse-elaborated tactic script (theorems only), via `reverseProofGuarded`:
  -- the proof-term SIZE FILTER (`reverseNodeCeiling`) skips obviously-pathological
  -- terms up front (→ `skipped_large`), and the heartbeat budget inside
  -- `reverseProof` bounds the rest; the client (`Corpus.WorkerExtract`) wraps the
  -- whole request in a per-file wall-clock fallback so a slow proof never loses
  -- the file's records. When `closers`, we also pass the `simp [..]` calls
  -- harvested verbatim from THIS proof's source as argument-bearing closer
  -- candidates (keyed, like sig/body, by the decl's selection position).
  let (proofScript, proofMethod) ← match info with
    | .thmInfo _ =>
        if opts.reverseElab then
          if shouldSkipReverse opts.reverseSkip info then
            pure (none, some "skipped_requested")
          else
          -- Once the fold's wall-clock deadline has passed, `attemptReverse` is
          -- false: emit the record with a `deadline_skipped` marker instead of
          -- running the expensive reverse-elab, so the theorem's record still
          -- survives (only its proof script is forgone).
          if !attemptReverse then
            pure (none, some "deadline_skipped")
          else match info.value? (allowOpaque := true) with
          | some v =>
              let extraClosers := if opts.reverseClosers then
                  match ranges? with
                  | some r => maps.simpArgs.getD (r.selectionRange.pos.line, r.selectionRange.pos.column) #[]
                  | none   => #[]
                else #[]
              let r ← match reverseFile? with
                | some file =>
                    reverseProofHybrid file info.name info.type v opts.reverseClosers extraClosers
                | none => reverseProofGuarded info.type v opts.reverseClosers extraClosers
              pure (if r.script.isEmpty then none else some r.script, some r.method)
          | none => pure (none, none)
        else pure (none, none)
    | _ => pure (none, none)
  -- Proof-complexity metrics (`--proof-metrics`). The tactic family starts from the
  -- author's source `by` block (looked up from the syntax-derived map by the decl's
  -- selection position, the same key as sig/body). On a `--reverse-elab` run it is
  -- REPLACED by the metrics of the reverse-elaborated body — `--reverse-elab` is the
  -- request for that reconstruction, so its metrics are what the run reports — and
  -- nulled when no script was produced. `metricsSource` records which body was
  -- measured. `isTermProof`/`attributes` are always carried from the author metrics,
  -- so they describe the ORIGINAL declaration regardless. The semantic family
  -- (below) is sized from the elaborated term and is unaffected by `--reverse-elab`.
  let authorMetrics? :=
    if opts.proofMetrics then
      match ranges? with
      | some r => maps.metrics[(r.selectionRange.pos.line, r.selectionRange.pos.column)]?
      | none   => none
    else none
  let (metrics?, metricsSource) ←
    match authorMetrics? with
    | none      => pure (none, none)
    | some base =>
      if opts.reverseElab then
        -- Measure the reverse-elaborated body instead. `proofScript` is the rendered
        -- `by …` string (or `none` when reverse-elab produced nothing). When there is
        -- no measurable body, keep `isTermProof`/`attributes` (they describe the
        -- original decl) but null the tactic family and the source marker.
        let unmeasured := (some base.withNullTactics, none)
        match proofScript with
        | none        => pure unmeasured  -- nothing reconstructed → nothing to measure
        | some script =>
            let kinds := CollectCommon.tacticKindSet env
            match ProofMetrics.metricsFromScript env kinds base script with
            | some m => pure (some m, some ProofMetrics.sourceReverseElab)
            | none   => pure unmeasured   -- script did not parse → null, honestly
      else
        pure (some base, some ProofMetrics.sourceAuthor)
  let (proofTermSize, proofTermDepth) :=
    if opts.proofMetrics then
      match info with
      | .thmInfo _ =>
          match info.value? (allowOpaque := true) with
          | some v => (some (ReverseElab.distinctNodes v), some v.approxDepth.toNat)
          | none   => (none, none)
      | _ => (none, none)
    else (none, none)
  return {
    -- Resolvable display name: private decls are unmangled from `_private.…` to
    -- their user name, so the record is citeable and joins with deps/premises.
    name := (CollectCommon.displayName info.name).toString
    kind := CollectCommon.kindToString info
    module := modStr
    type := typeStr
    value? := value?
    doc? := doc?
    deps := deps
    axioms := axStrs
    hasSorry
    signature
    body
    declSource
    declNamespace := (declScope.map (·.«namespace»)).getD ""
    scopePrelude  := (declScope.map (·.prelude)).getD #[]
    fileImports   := env.imports.map (·.module.toString)
    premises
    proofScript
    proofMethod
    isPrivate
    isProtected
    isStructure
    startLine
    startCol
    endLine
    endCol
    metrics := metrics?
    metricsSource
    proofTermSize
    proofTermDepth
  }

/-- Reverse-elab cost proxy for scheduling: a theorem's proof-term node count
(`distinctNodes`, the same measure `reverseProofGuarded` pre-filters on), else 0.
Non-theorems never reverse-elaborate, so they cost nothing and sort first. -/
private def reverseCost (info : ConstantInfo) : Nat :=
  match info with
  | .thmInfo _ =>
      match info.value? (allowOpaque := true) with
      | some v => ReverseElab.distinctNodes v
      | none   => 0
  | _ => 0

private def isTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | _          => false

private def theoremProgressStep (total : Nat) : Nat :=
  if total ≤ 20 then 1
  else if total ≤ 100 then 10
  else 25

/-- Fold `buildEntry` over the module-local user constants that also pass the
corpus-eligibility filter (`corpusEligible`), threading the params'
`includeInternal` / `includePrivate` knobs.

When `reverseElab` and `deadlineMs > 0`, entries are processed CHEAP-FIRST (by
`reverseCost`) under a wall-clock budget: once `deadlineMs` ms have elapsed, the
remaining (most expensive) theorems are built WITHOUT attempting reverse-elab
(`proofMethod := "deadline_skipped"`). This turns a per-file timeout — which
would otherwise kill the whole request and lose EVERY script for the file — into
the loss of only the expensive tail, while the many cheap proofs land their
scripts. The output is re-sorted by name, so ordering is unchanged; only WHICH
theorems get a script depends on the schedule. `deadlineMs = 0` disables all of
this (process in name order, always attempt — the historical behavior). -/
private def foldCorpusEntries (maps : SourceMaps) (opts : CollectOptions)
    (deadlineMs : Nat := 0)
    (fileLabel : String := "") (reverseFile? : Option Frontend.ElabResult := none)
    : CoreM (Array CorpusManifestEntry) := do
  let env ← getEnv
  -- Source the file-local constants from the shared VERIFICATION substrate
  -- (`Verify.verifiedFileConstants`) rather than re-enumerating `env.constants`:
  -- the corpus collector is a CLIENT of the verification mechanism. This iterates
  -- `env.constants` in the same order and applies the same `isUserConstant` filter
  -- as before, so the eligible set — and thus the record set — is unchanged. Each
  -- `VerifiedConst` also carries `isSorryFree`; the reverse-elab ENRICHMENT is the
  -- consumer of that signal (a `sorry`-laced proof is not a valid learning target),
  -- and `ReverseElab`'s own `errToSorry := false` / `Expr.hasSorry` guards already
  -- reject any `sorry`/partial script, so no valid `proof_script` is ever emitted
  -- for an unverified proof. The base record (name/type/deps/…) is emitted for every
  -- eligible constant regardless (a `sorry` theorem still belongs in the corpus,
  -- flagged `has_sorry`); only its `proof_script` would be forgone.
  let mut eligible : Array Verify.VerifiedConst := #[]
  for vc in (← Verify.verifiedFileConstants) do
    if (← corpusEligible env opts.includeInternal opts.includePrivate vc.info.name vc.info) then
      eligible := eligible.push vc
  let theoremTotal := eligible.foldl (fun n vc => if isTheoremInfo vc.info then n + 1 else n) 0
  let logPrefix :=
    if fileLabel.isEmpty then "corpus-extract: theorem extraction"
    else s!"corpus-extract: theorem extraction {fileLabel}"
  if theoremTotal > 0 then
    IO.eprintln s!"{logPrefix}: 0/{theoremTotal} theorem(s) starting \
      ({eligible.size} total record(s), reverse-elab={opts.reverseElab})"
  -- Cheap-first scheduling only matters when we actually reverse-elaborate under a
  -- deadline; otherwise keep the original (name) order to minimize behavior change.
  let scheduled :=
    if opts.reverseElab && deadlineMs > 0 then
      eligible.qsort (fun a b => reverseCost a.info < reverseCost b.info)
    else eligible
  let startMs ← IO.monoMsNow
  let mut out : Array CorpusManifestEntry := #[]
  let mut theoremDone := 0
  let progressStep := theoremProgressStep theoremTotal
  for vc in scheduled do
    -- Past the budget, keep emitting records but stop attempting reverse-elab.
    let attemptReverse := deadlineMs == 0 || (← IO.monoMsNow) - startMs < deadlineMs
    let entry ← buildEntry maps opts vc.info attemptReverse reverseFile?
    out := out.push entry
    if isTheoremInfo vc.info then
      theoremDone := theoremDone + 1
      if theoremDone == theoremTotal || theoremDone % progressStep == 0 then
        let method := entry.proofMethod.getD "none"
        IO.eprintln s!"{logPrefix}: {theoremDone}/{theoremTotal} theorem(s) \
          last={entry.name} proof_method={method}"
  return out.qsort (fun a b => a.name < b.name)

/-- Derive the per-file source maps from an elaborated file.

The simp-arg map is built ONLY when closers are enabled: constructing it walks every
proof's syntax, and nothing reads it otherwise. -/
def SourceMaps.of (r : Frontend.ElabResult) (opts : CollectOptions) : CoreM SourceMaps := do
  let env ← getEnv
  return {
    sig        := buildSourceMap r.source r.commands
    declSource := buildDeclSourceMap r.source r.commands
    scope      := buildScopeMap r.source r.commands
    simpArgs   := ← if opts.reverseClosers then buildSimpArgMap r.source r.commands else pure {}
    metrics    := if opts.proofMetrics then
                    ProofMetrics.buildMetricsMap (CollectCommon.tacticKindSet env)
                      r.source r.commands
                  else {} }

/-- The corpus-collector entry point: build the corpus manifest entries for one
frontend-elaborated file. The `CoreM` fold runs via `Frontend.runCollectorOn` against
`r`'s post-elaboration environment (with the file's real `FileMap`, so source
positions line up); `source`/`commands` for the sig/body reconstruction come from `r`.

`reverseDeadlineMs` gives the fold an internal wall-clock budget (cheap-first,
tail-shed to `deadline_skipped`); the driver sets it below its own per-file bound.
See `foldCorpusEntries` for the scheduling contract. -/
def corpusManifestCore (r : Frontend.ElabResult) (opts : CollectOptions)
    (reverseDeadlineMs : Nat := 0)
    : IO (Array CorpusManifestEntry) :=
  Frontend.runCollectorOn r do
    let maps ← SourceMaps.of r opts
    foldCorpusEntries maps opts reverseDeadlineMs r.file.relPath (some r)

end Corpus
