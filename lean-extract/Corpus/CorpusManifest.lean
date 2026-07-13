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
import Corpus.Verify

/-!
The corpus collector: for each user declaration in an elaborated file, computes
the data a theorem/definition CORPUS needs — fully-qualified name, kind,
pretty-printed type and (for defs/theorems) value, direct dependencies,
transitive axioms/premises, source signature/body, and (optionally) a verified
reverse-elaborated `proofScript`.

This is the in-process form of what was the `$/lean/corpusManifest` FileWorker
request. The per-constant computation (the `CoreM` fold below) is UNCHANGED from
the plugin — it runs in the file's TRUE post-elaboration environment either way.
What changed is how that environment is obtained: instead of a worker answering
an LSP request against `doc.cmdSnaps`, `Corpus.Frontend.runCollectorOn` runs this
fold directly against the frontend-elaborated environment (see
`corpusManifestCore`, the entry point the driver calls). The `source` string and
per-command `Syntax` array the source reconstruction needs
(`buildSourceMap`/`buildSimpArgMap`) come straight from `Frontend.ElabResult`.

Terminology in the comments below still refers to "the worker" for the pathology
it guards against (a pathological proof pinning a compute thread); that hazard is
the same in-process, only now it pins one of the parallel file threads rather than
a subprocess.
-/

namespace Corpus

open Lean

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
  rejected, not stored). Running inside the worker means re-elaboration happens
  in the file's TRUE context with registered tactics — the import-based extractor
  could not reproduce that. -/
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
  deriving FromJson, ToJson

open Lean.PrettyPrinter

/-- Pretty-print an `Expr` at width 120 (lifting the `MetaM`-based `ppExpr`). -/
private def ppExpr120 (e : Expr) : CoreM String := do
  let fmt ← Lean.Meta.MetaM.run' (Lean.Meta.ppExpr e)
  return (fmt.pretty 120).trimAsciiEnd.copy

/-- Proof-term size ceiling (distinct sub-expressions, `ReverseElab.distinctNodes`)
above which reverse-elaboration is SKIPPED outright, emitting `proofMethod :=
"skipped_large"`. This is the primary guard against pathological proofs pinning
the worker.

Why a size pre-filter rather than a time/heartbeat budget: on the worker path
proof terms are freshly elaborated (vs the import path's compacted oleans), and
re-elaborating + `isDefEq`-checking a candidate against a huge term can run for
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



/-! ## SOURCE signature/body via command-`Syntax` navigation

We reconstruct the SOURCE signature/body by navigating the parsed command
`Syntax` (NOT a byte heuristic). The top command node is
`Lean.Parser.Command.declaration` with two children: `[0]` the `declModifiers`
(where the leading doc comment lives) and `[1]` the inner decl node
(`theorem`/`definition`/`abbrev`/`instance`/…). Inner child indices DIFFER per
kind, so we locate sub-nodes by KIND via a DFS rather than by position.

Keying back to `ConstantInfo`: a `declId`'s `ident` carries only the
SOURCE-LOCAL name (`PAGE_SIZE`, not `LeanSQLite.PAGE_SIZE`), so we cannot match
it to `info.name` directly. Instead we key a map by the `(line, column)` of each
declaration's name token, and look each constant up via
`findDeclarationRanges? info.name |>.selectionRange.pos` — whose `Position`
points exactly at that name token. Companions/projections/recursors and
anonymous instances/examples have no matching declId token, so they fall through
to `(none, none)` as required. -/

/-- DFS pre-order: the first sub-node whose `getKind` is in `kinds`. Used to find
`declSig`/`optDeclSig` and `declValSimple`/`declValEqns`/`whereStructInst`
regardless of the per-kind child layout. -/
private partial def findByKind (stx : Syntax) (kinds : List SyntaxNodeKind) : Option Syntax :=
  if kinds.contains stx.getKind then some stx
  else match stx with
    | .node _ _ args => args.findSome? (findByKind · kinds)
    | _ => none

private def sigKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declSig, ``Lean.Parser.Command.optDeclSig]
private def valKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
   ``Lean.Parser.Command.whereStructInst]

/-- Slice the SOURCE substring for `stx`'s absolute byte range out of `src`
(`doc.meta.text.source`), trimming trailing ASCII whitespace. `none` if `stx`
has no original range (synthetic / empty node, e.g. an `optDeclSig` with no
binders and no type). -/
private def sliceTrimmed (stx : Syntax) (src : String) : Option String := do
  let r ← stx.getRange?
  pure (String.Pos.Raw.extract src r.start r.stop).trimAsciiEnd.copy

/-- Reconstruct `(signature?, body?)` from a `declaration` command's `Syntax`.
For `declValSimple` (`:= term`) the body is just the term (child `[1]`), so the
`:=` is excluded; for equations/`where` the whole `declVal` node is used. -/
private def sigBodyOf (cmdStx : Syntax) (src : String) : Option String × Option String :=
  let sig := (findByKind cmdStx sigKinds).bind (sliceTrimmed · src)
  let body := (findByKind cmdStx valKinds).bind fun v =>
    if v.getKind == ``Lean.Parser.Command.declValSimple then
      sliceTrimmed v[1] src
    else
      sliceTrimmed v src
  (sig, body)

/-- Build a map from each declaration's name-token `(line, column)` to its
SOURCE `(signature?, body?)`, by walking the per-command parsed `Syntax`
(`ElabResult.commands`, which excludes the header). Any non-`declaration` command
is skipped naturally (no `Command.declId` child). Positions are produced by
`FileMap.toPosition` so they line up with `findDeclarationRanges?`'s `Position`. -/
private def buildSourceMap (src : String) (commands : Array Syntax)
    : Std.HashMap (Nat × Nat) (Option String × Option String) := Id.run do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) (Option String × Option String) := {}
  for cmdStx in commands do
    if cmdStx.getKind == ``Lean.Parser.Command.declaration then
      if let some declId := findByKind cmdStx [``Lean.Parser.Command.declId] then
        if let some idPos := declId[0].getPos? then
          let p := fileMap.toPosition idPos
          m := m.insert (p.line, p.column) (sigBodyOf cmdStx src)
  return m

/-- Build a map from each declaration's name-token `(line, column)` to the FULL
SOURCE of its command — the entire `declaration` node's range, which begins at
`declModifiers` (so the leading doc comment and any `@[...]`/`private`/`noncomputable`
modifiers are included) and runs through the whole body. Unlike `buildSourceMap`
(which isolates the sig and the value/proof separately, and returns `(none,none)`
for inductives/structures whose layout it does not decompose), this captures the
verbatim, re-elaboratable text of the WHOLE declaration for EVERY kind — exactly
what a self-contained record inlines for its owned `def`/`inductive`/`structure`
dependencies. Keyed identically to `buildSourceMap` (the name-token position, via
`findDeclarationRanges?.selectionRange` on the constant side). -/
private def buildDeclSourceMap (src : String) (commands : Array Syntax)
    : Std.HashMap (Nat × Nat) String := Id.run do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) String := {}
  for cmdStx in commands do
    if cmdStx.getKind == ``Lean.Parser.Command.declaration then
      if let some src? := sliceTrimmed cmdStx src then
        -- Key by the position `findDeclarationRanges?.selectionRange.pos` reports
        -- for the constant (which is how `buildEntry` looks the source up):
        --  * NAMED decl → the `declId` name-token position.
        --  * ANONYMOUS `instance`/`example` (no `declId`) → the whole command's
        --    start position (`cmdStx[1]`, the inner decl node — past the
        --    `declModifiers`), which is what `selectionRange.pos` points at for a
        --    nameless declaration. Without this, anonymous instances (e.g.
        --    `instance : Monad M where …`) never landed in the map and had null
        --    `declSource`, breaking any record whose proof uses that instance.
        let keyPos? :=
          match findByKind cmdStx [``Lean.Parser.Command.declId] with
          | some declId => declId[0].getPos?
          | none        => (cmdStx.getArg 1).getPos? <|> cmdStx.getPos?
        if let some p := keyPos? then
          let pos := fileMap.toPosition p
          m := m.insert (pos.line, pos.column) src?
  return m

/-- The `(line, column)` key that a `declaration` command should be filed under —
the position `findDeclarationRanges?.selectionRange.pos` reports for the constant,
which is how `buildEntry` looks entries up. NAMED decls key on the `declId`
name-token; ANONYMOUS `instance`/`example` (no `declId`) key on the inner decl
node start (`cmdStx[1]`, past `declModifiers`). `none` if neither has a position. -/
private def declKeyPos (fileMap : FileMap) (cmdStx : Syntax) : Option (Nat × Nat) := do
  let p ← match findByKind cmdStx [``Lean.Parser.Command.declId] with
    | some declId => declId[0].getPos?
    | none        => (cmdStx.getArg 1).getPos? <|> cmdStx.getPos?
  let pos := fileMap.toPosition p
  return (pos.line, pos.column)

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
    if k == ``Lean.Parser.Command.declaration then
      if let some key := declKeyPos fileMap cmdStx then
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

/-- Map each declaration's name-token `(line, column)` to the pooled-lemma simp
closer candidates harvested from its proof syntax (see `harvestSimpPool`). Keyed
like `buildSourceMap` so `buildEntry` can look up a constant's candidates by its
`findDeclarationRanges?` selection position. -/
private def buildSimpArgMap (src : String) (commands : Array Syntax)
    : CoreM (Std.HashMap (Nat × Nat) (Array String)) := do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) (Array String) := {}
  for cmdStx in commands do
    if cmdStx.getKind == ``Lean.Parser.Command.declaration then
      if let some declId := findByKind cmdStx [``Lean.Parser.Command.declId] then
        if let some idPos := declId[0].getPos? then
          let p := fileMap.toPosition idPos
          let pool ← harvestSimpPool cmdStx
          m := m.insert (p.line, p.column) (simpPoolClosers pool)
  return m


/-- Hard wall-clock budget for a single theorem's reverse-elab child process. -/
def reverseProofTimeoutMs : Nat := 15000

/-- Small proofs are safe and much faster to reverse-elaborate in the already
elaborated file process. Larger proofs still use the killable child path below,
because a single `isDefEq` on an automation-heavy term can otherwise pin the
collector in wall time despite heartbeat limits. -/
def reverseInProcessNodeCeiling : Nat := 250

private partial def waitChildWithTimeout {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) (started timeoutMs : Nat) : IO (Option UInt32) := do
  match (← child.tryWait) with
  | some code => return some code
  | none =>
      if (← IO.monoMsNow) - started ≥ timeoutMs then
        try child.kill catch _ => pure ()
        let _ ← child.wait
        return none
      IO.sleep (100 : UInt32)
      waitChildWithTimeout child started timeoutMs

private def parseScriptResult (stdout : String) : Option ReverseElab.ScriptResult :=
  match Json.parse stdout.trimAscii.toString >>= fromJson? with
  | .ok r => some r
  | .error _ => none

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
  let args :=
    #["--internal-reverse-one",
      "--source-file", file.file.absPath.toString,
      "--module", file.file.module.toString,
      "--decl", declName.toString] ++
    (if enableClosers then #["--closers"] else #[])
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := args
    stdin := .null
    stdout := .piped
    stderr := .piped
    setsid := true
  }
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let started ← IO.monoMsNow
  match (← waitChildWithTimeout child started timeoutMs) with
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

private def buildEntry (srcMap : Std.HashMap (Nat × Nat) (Option String × Option String))
    (declSrcMap : Std.HashMap (Nat × Nat) String)
    (scopeMap : Std.HashMap (Nat × Nat) DeclScope)
    (simpArgMap : Std.HashMap (Nat × Nat) (Array String))
    (reverseElab closers : Bool) (reverseSkip : Array String) (info : ConstantInfo)
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
  -- Only theorems report their axioms in the corpus schema (matching the
  -- import-based extractor); `hasSorry` is still derived from the full set.
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
  -- start/end line-cols, matching the import-based extractor (Extract.lean uses
  -- `range`, not `selectionRange`, for start*/end*).
  let ranges? ← Lean.findDeclarationRanges? info.name
  let (signature, body) :=
    match ranges? with
    | some r => srcMap.getD (r.selectionRange.pos.line, r.selectionRange.pos.column) (none, none)
    | none   => (none, none)
  let declSource :=
    match ranges? with
    | some r => declSrcMap[(r.selectionRange.pos.line, r.selectionRange.pos.column)]?
    | none   => none
  let declScope :=
    match ranges? with
    | some r => scopeMap[(r.selectionRange.pos.line, r.selectionRange.pos.column)]?
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
  -- ctors/recs/quots get an empty list (matching the import-based extractor).
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
        if reverseElab then
          if shouldSkipReverse reverseSkip info then
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
              let extraClosers := if closers then
                  match ranges? with
                  | some r => simpArgMap.getD (r.selectionRange.pos.line, r.selectionRange.pos.column) #[]
                  | none   => #[]
                else #[]
              let r ← match reverseFile? with
                | some file => reverseProofHybrid file info.name info.type v closers extraClosers
                | none      => reverseProofGuarded info.type v closers extraClosers
              pure (if r.script.isEmpty then none else some r.script, some r.method)
          | none => pure (none, none)
        else pure (none, none)
    | _ => pure (none, none)
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
corpus-eligibility filter (`corpusEligible`), so the manifest matches the
import-based extractor's record set. Unlike `Common.foldUserConstants`, this
applies the extra parity filter and threads the params' `includeInternal` /
`includePrivate` knobs.

When `reverseElab` and `deadlineMs > 0`, entries are processed CHEAP-FIRST (by
`reverseCost`) under a wall-clock budget: once `deadlineMs` ms have elapsed, the
remaining (most expensive) theorems are built WITHOUT attempting reverse-elab
(`proofMethod := "deadline_skipped"`). This turns a per-file timeout — which
would otherwise kill the whole request and lose EVERY script for the file — into
the loss of only the expensive tail, while the many cheap proofs land their
scripts. The output is re-sorted by name, so ordering is unchanged; only WHICH
theorems get a script depends on the schedule. `deadlineMs = 0` disables all of
this (process in name order, always attempt — the historical behavior). -/
private def foldCorpusEntries (srcMap : Std.HashMap (Nat × Nat) (Option String × Option String))
    (declSrcMap : Std.HashMap (Nat × Nat) String)
    (scopeMap : Std.HashMap (Nat × Nat) DeclScope)
    (simpArgMap : Std.HashMap (Nat × Nat) (Array String))
    (includeInternal includePrivate reverseElab closers : Bool)
    (reverseSkip : Array String := #[]) (deadlineMs : Nat := 0)
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
    if (← corpusEligible env includeInternal includePrivate vc.info.name vc.info) then
      eligible := eligible.push vc
  let theoremTotal := eligible.foldl (fun n vc => if isTheoremInfo vc.info then n + 1 else n) 0
  let logPrefix :=
    if fileLabel.isEmpty then "corpus-extract: theorem extraction"
    else s!"corpus-extract: theorem extraction {fileLabel}"
  if theoremTotal > 0 then
    IO.eprintln s!"{logPrefix}: 0/{theoremTotal} theorem(s) starting \
      ({eligible.size} total record(s), reverse-elab={reverseElab})"
  -- Cheap-first scheduling only matters when we actually reverse-elaborate under a
  -- deadline; otherwise keep the original (name) order to minimize behavior change.
  let scheduled :=
    if reverseElab && deadlineMs > 0 then
      eligible.qsort (fun a b => reverseCost a.info < reverseCost b.info)
    else eligible
  let startMs ← IO.monoMsNow
  let mut out : Array CorpusManifestEntry := #[]
  let mut theoremDone := 0
  let progressStep := theoremProgressStep theoremTotal
  for vc in scheduled do
    -- Past the budget, keep emitting records but stop attempting reverse-elab.
    let attemptReverse := deadlineMs == 0 || (← IO.monoMsNow) - startMs < deadlineMs
    let entry ← buildEntry srcMap declSrcMap scopeMap simpArgMap reverseElab closers reverseSkip vc.info attemptReverse reverseFile?
    out := out.push entry
    if isTheoremInfo vc.info then
      theoremDone := theoremDone + 1
      if theoremDone == theoremTotal || theoremDone % progressStep == 0 then
        let method := entry.proofMethod.getD "none"
        IO.eprintln s!"{logPrefix}: {theoremDone}/{theoremTotal} theorem(s) \
          last={entry.name} proof_method={method}"
  return out.qsort (fun a b => a.name < b.name)

/-- The in-process corpus-collector entry point: build the corpus manifest entries
for one frontend-elaborated file. Replaces the `$/lean/corpusManifest` request
handler — same `CoreM` fold, run via `Frontend.runCollectorOn` against `r`'s
post-elaboration environment (with the file's real `FileMap`, so source positions
line up). `source`/`commands` for the sig/body reconstruction come from `r`.

`reverseDeadlineMs` gives the fold an internal wall-clock budget (cheap-first,
tail-shed to `deadline_skipped`); the driver sets it below its own per-file bound.
See `foldCorpusEntries` for the scheduling contract. -/
def corpusManifestCore (r : Frontend.ElabResult)
    (includeInternal includePrivate reverseElab closers : Bool)
    (reverseDeadlineMs : Nat := 0) (reverseSkip : Array String := #[])
    : IO (Array CorpusManifestEntry) :=
  Frontend.runCollectorOn r do
    let srcMap := buildSourceMap r.source r.commands
    let declSrcMap := buildDeclSourceMap r.source r.commands
    let scopeMap := buildScopeMap r.source r.commands
    -- Only build the simp-arg map when closers are on (it walks every proof's
    -- syntax); otherwise it is unused.
    let simpArgMap ← if closers then buildSimpArgMap r.source r.commands else pure {}
    foldCorpusEntries srcMap declSrcMap scopeMap simpArgMap
      includeInternal includePrivate reverseElab closers reverseSkip reverseDeadlineMs r.file.relPath (some r)

end Corpus
