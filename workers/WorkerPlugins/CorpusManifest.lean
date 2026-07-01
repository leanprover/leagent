/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean.Server.Requests
import Lean.Server.Snapshots
import Lean.Util.CollectAxioms
import Lean.Data.Lsp.Basic
import Lean.PrettyPrinter
import WorkerPlugins.Common
import WorkerPlugins.ReverseElab

/-!
`$/lean/corpusManifest`: a FileWorker request that returns, for each user
declaration in the elaborated file, the data a theorem/definition CORPUS needs —
fully-qualified name, kind, pretty-printed type and (for defs/theorems) value,
direct dependencies, transitive axioms, and a `hasSorry` flag.

This is a SIBLING of `WorkerPlugins.DeclManifest`, not an extension of it. They
share the per-file traversal scaffolding (`WorkerPlugins.Common`) but differ in
purpose and stability contract:

- `DeclManifest` is a DIFF FINGERPRINT: it emits an alpha-canonical `typeRepr`
  whose encoding is deliberately unstable (the baseline lives in consumer memory
  and is recomputed each run), and it includes auto-generated companions
  (`.sizeOf_spec`, `.casesOn`, `.rec`, …) because a diff wants everything.
- `CorpusManifest` is a DATASET SOURCE: it emits human-meaningful,
  pretty-printed types/values destined for a STABLE on-disk schema (JSONL), and
  it is the natural home for source signature/body (via parser-AST navigation)
  and premise/proof-script fields as those land.

Running inside the worker means the data is computed in the file's TRUE
elaboration context (section variables, `open`s, `set_option`s, registered
tactics), which the prior `importModules`-based extractor could not reproduce.
-/

namespace Lean.Lsp

/-- Parameters for `$/lean/corpusManifest`. -/
structure CorpusManifestParams where
  textDocument : TextDocumentIdentifier
  /-- Emit compiler-internal / auto-generated names (constructors, recursors,
  `.casesOn`, projections, `._proof_*`, …). Mirrors the extractor's
  `--include-internal`. Default `false`. Has a default so older callers (the
  spike) still decode. -/
  includeInternal : Bool := false
  /-- Emit declarations marked `private`. Mirrors the extractor's
  `--no-private` (inverted). Default `true`. -/
  includePrivate  : Bool := true
  /-- Reverse-elaborate each theorem's proof term into a verified tactic script
  (`proofScript`/`proofMethod`). OFF by default: it re-elaborates every proof
  (expensive — a single hard proof can burn unbounded CPU under the unlimited
  per-decl budget). Mirrors the extractor's `--reverse-elab`. -/
  reverseElab     : Bool := false
  /-- Enable closer-guessing during reverse-elaboration: at the whole goal and at
  structural leaves, try a fixed no-arg tactic menu (`simp`/`omega`/…) PLUS the
  `simp [..]` argument-lists harvested verbatim from the proof source, keeping the
  first that verifies. Pushes more proofs into the restricted, argument-bounded
  tactic vocabulary. Mirrors the extractor's `--closers`. Requires `reverseElab`. -/
  closers         : Bool := false
  /-- Wall-clock budget (ms) for the WHOLE reverse-elab fold, measured INSIDE the
  worker. `0` = unbounded (the historical behavior). When >0, the plugin processes
  theorems CHEAP-FIRST (ascending proof-term node count) and, once this many ms
  have elapsed, stops *attempting* reverse-elab for the remaining (expensive)
  theorems — emitting their records with `proofMethod := "deadline_skipped"` rather
  than losing them. The client sets this below its own request timeout so the whole
  fold returns a complete response instead of being killed mid-flight (which
  discards ALL of the file's proof scripts). Has a default so older callers decode. -/
  reverseDeadlineMs : Nat := 0
  /-- Collect per-theorem trace info showing which reverse-elab rungs were tried
  and why they failed. Emitted in `proofTrace`. Mirrors `--trace-reverse-elab`. -/
  traceReverseElab : Bool := false
  deriving FromJson, ToJson

instance : FileSource CorpusManifestParams where
  fileSource p := p.textDocument.uri

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
  /-- Trace log from reverse-elaboration: each entry records which rung was
  tried and whether it passed/failed. Populated only with `--trace-reverse-elab`. -/
  proofTrace  : Option (Array WorkerPlugins.ReverseElab.TraceEntry) := none
  /-- Structural decomposition tree, shared across the (delaborator-variant)
  `structural` attempts in `proofTrace` (see `ReverseElab.ScriptResult.structTree`).
  Populated only with `--trace-reverse-elab`, and only when a structural candidate
  was built. -/
  proofStructTree : Option (Array WorkerPlugins.ReverseElab.StructNode) := none
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

/-- Response payload for `$/lean/corpusManifest`. -/
structure CorpusManifest where
  entries : Array CorpusManifestEntry
  deriving FromJson, ToJson

end Lean.Lsp

namespace WorkerPlugins.CorpusManifest

open Lean Lean.Lsp Lean.Server Lean.Server.Snapshots Lean.PrettyPrinter

/-- Pretty-print an `Expr` at width 120 in the snapshot's `CoreM` (lifting the
`MetaM`-based `ppExpr`). -/
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
    (extraClosers : Array String := #[]) (enableTrace : Bool := false)
    : CoreM ReverseElab.ScriptResult := do
  let nodes := ReverseElab.distinctNodes v
  if nodes > reverseNodeCeiling then
    let traceLog := if enableTrace then
        #[{ rung := "pre_filter", result := s!"skipped: {nodes} nodes > ceiling {reverseNodeCeiling}" : WorkerPlugins.ReverseElab.TraceEntry }]
      else #[]
    return { script := "", method := "skipped_large", trace := traceLog }
  -- `tryCatchRuntimeEx` swallows a heartbeat/recursion blowup on an in-range
  -- proof to a null script (rather than aborting the whole request); genuine
  -- interrupts (worker shutdown) still propagate.
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
    tryCatchRuntimeEx
      (Lean.Meta.MetaM.run' (ReverseElab.reverseProof ty v enableClosers extraClosers enableTrace))
      (fun _ => do
        let traceLog := if enableTrace then
            #[{ rung := "runtime", result := "error (heartbeat/recursion blowup)" : WorkerPlugins.ReverseElab.TraceEntry }]
          else #[]
        pure { script := "", method := "error", trace := traceLog })

/-- Sorted, deduped fully-qualified names (excluding `self`). -/
private def fmtNames (self : Name) (ns : Array Name) : Array String :=
  let strs := ns.toList.map toString
  let uniq := strs.eraseDups.filter (· != self.toString)
  (uniq.mergeSort (· < ·)).toArray

/-! ## Corpus-eligibility filter (parity with the import-based extractor)

`Common.foldUserConstants` keeps every module-local non-internal-detail constant,
but the corpus schema (lean-extract `Corpus/Extract.lean`) drops more: auto-
generated companions, constructors/recursors (unless `--include-internal`),
private names (unless `--include-private`), and range-less synthetic theorems
(`.injEq`/`.sizeOf_spec`/`.brecOn`/… that survive but have no authored source).
Without this filter the worker corpus over-emits relative to the baseline, so we
port the predicates here (they need the `Environment`, which the thin client
lacks — hence server-side). Kept textually in sync with `Extract.lean:82-176`
and `Extract.lean:305-308`. -/

/-- Compiler-synthesized name fragments that slip past `isInternalDetail` but are
never corpus material. Mirrors `Extract.hasGeneratedTag`. -/
private def hasGeneratedTag (n : Name) : Bool :=
  let s := n.toString
  let containsTag (tag : String) : Bool := (s.splitOn tag).length > 1
  containsTag "._proof_" || containsTag "._eq_" || containsTag "._eqDef"
    || containsTag "._sunfold" || containsTag "._unfold"

/-- Auto-generated `def` equation-compiler theorems (`eq_def`/`induct` suffix).
Mirrors `Extract.isGeneratedTheoremSuffix`. -/
private def isGeneratedTheoremSuffix : Name → Bool
  | .str _ s => s == "eq_def" || s == "induct"
  | _        => false

/-- Names always dropped from the corpus. Mirrors `Extract.alwaysSkip`. -/
private def alwaysSkip (env : Environment) (n : Name) : Bool :=
  Lean.isAuxRecursor env n || Lean.isNoConfusion env n || n.isAnonymous
    || hasGeneratedTag n || isGeneratedTheoremSuffix n || env.isProjectionFn n

/-- The full corpus-eligibility test applied per constant inside the collector,
mirroring `Extract.shouldSkip` (minus the owned-module check — in the worker the
plugin already restricts to module-local user constants) plus
`Extract.isSyntheticTheorem` (drop range-less synthetic theorems). Returns
`true` to KEEP the constant. -/
private def corpusEligible (env : Environment) (includeInternal includePrivate : Bool)
    (name : Name) (info : ConstantInfo) : CoreM Bool := do
  if alwaysSkip env name then return false
  unless includeInternal do
    if name.isInternalDetail then return false
    match info with
    | .ctorInfo _ | .recInfo _ => return false
    | _ => pure ()
  if !includePrivate && Lean.isPrivateName name then return false
  -- Range-less synthetic theorems (`.injEq`, `.sizeOf_spec`, `.brecOn`, …).
  match info with
  | .thmInfo _ => return (← Lean.findDeclarationRanges? name).isSome
  | _          => return true

/-! ## Transitive premise cone (project-owned constants)

`premises` is the transitive cone of PROJECT-OWNED constants reachable from a
declaration's term, ported from the import-based extractor's `collectPremises`
(`lean-extract` `Corpus/Extract.lean`). The semantics differ from that port in
one essential way driven by the worker model: in the import-based extractor the
project's files are *imported* (they carry a module index) and the only
index-less constants are core builtins, so ownership keyed off the module name.
In the WORKER, the file under study is being *elaborated*, so ITS OWN constants
carry NO module index (`getModuleIdxFor? = none`) while everything else
(core/Std/Mathlib AND any imported project files) is indexed. Ownership here
therefore means: index-less (defined by this file) OR indexed under the project
root prefix (another file of the same project). The project root is the first
component of the worker's main module name (e.g. `LeanSQLite` for
`LeanSQLite.Basic`).

Note premises deliberately do NOT use the `Common.isUserConstant` record filter:
the cone legitimately includes private names (`_private.…`) and generated
companions (`.match_1`, `.proof_1`, `.rec`, …) — they are real owned premises of
a proof/definition even though they never get their own corpus record. -/

/-- The project root: the first component of the worker's main module name. For
`LeanSQLite.Basic` this is `LeanSQLite`. Used as the owned-module prefix. -/
private def projectRoot (env : Environment) : Name :=
  let rec firstComponent : Name → Name
    | .str .anonymous s => .str .anonymous s
    | .num .anonymous n => .num .anonymous n
    | .str p _          => firstComponent p
    | .num p _          => firstComponent p
    | .anonymous        => .anonymous
  firstComponent env.mainModule

/-- True iff `n` is owned by the project under study: either defined by the file
being elaborated (no module index) or by an imported module sharing the project
root prefix. Excludes core/Std/Mathlib. -/
private def isOwnedName (env : Environment) (root : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none     => true  -- defined by the file under elaboration
  | some idx =>
    match env.allImportedModuleNames[idx.toNat]? with
    | some m => root == m || root.isPrefixOf m
    | none   => false

/-- Transitive premise cone for `root`: BFS over `Environment.constants`
following only owned constants. The seed is the direct dep set of `root`; for
each owned constant popped we enqueue its own direct deps. External or absent
constants are skipped (we never drag Init/Std/Mathlib into the cone). The result
is owned-only and excludes `root`. Ported from `Corpus/Extract.lean`.

Termination: every popped name is inserted into `visited` before its deps are
enqueued, and names drawn from a finite environment form a finite set. -/
private partial def collectPremises (env : Environment) (owned : Name → Bool)
    (root : Name) : Array Name := Id.run do
  let some rootCi := env.find? root | return #[]
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
    if owned n then
      result := result.push n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet.toArray do
          unless visited.contains d do
            queue := queue.push d
  return result

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
SOURCE `(signature?, body?)`, by walking the per-command snapshots. The first
snapshot is the header (no declId) and is skipped naturally (no `Command.declId`
child). Positions are produced by `FileMap.toPosition` so they line up with
`findDeclarationRanges?`'s `Position`. -/
private def buildSourceMap (src : String) (snaps : Array Snapshots.Snapshot)
    : Std.HashMap (Nat × Nat) (Option String × Option String) := Id.run do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) (Option String × Option String) := {}
  for snap in snaps do
    let cmdStx := snap.stx
    if cmdStx.getKind == ``Lean.Parser.Command.declaration then
      if let some declId := findByKind cmdStx [``Lean.Parser.Command.declId] then
        if let some idPos := declId[0].getPos? then
          let p := fileMap.toPosition idPos
          m := m.insert (p.line, p.column) (sigBodyOf cmdStx src)
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
private def buildSimpArgMap (src : String) (snaps : Array Snapshots.Snapshot)
    : CoreM (Std.HashMap (Nat × Nat) (Array String)) := do
  let fileMap := src.toFileMap
  let mut m : Std.HashMap (Nat × Nat) (Array String) := {}
  for snap in snaps do
    let cmdStx := snap.stx
    if cmdStx.getKind == ``Lean.Parser.Command.declaration then
      if let some declId := findByKind cmdStx [``Lean.Parser.Command.declId] then
        if let some idPos := declId[0].getPos? then
          let p := fileMap.toPosition idPos
          let pool ← harvestSimpPool cmdStx
          m := m.insert (p.line, p.column) (simpPoolClosers pool)
  return m

private def buildEntry (srcMap : Std.HashMap (Nat × Nat) (Option String × Option String))
    (simpArgMap : Std.HashMap (Nat × Nat) (Array String))
    (reverseElab closers traceReverseElab : Bool) (info : ConstantInfo)
    (attemptReverse : Bool := true) : CoreM Lsp.CorpusManifestEntry := do
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
  let deps := fmtNames info.name info.getUsedConstantsAsSet.toArray
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
        let root := projectRoot env
        fmtNames info.name (collectPremises env (isOwnedName env root) info.name)
    | _ => #[]
  -- Reverse-elaborated tactic script (theorems only), via `reverseProofGuarded`:
  -- the proof-term SIZE FILTER (`reverseNodeCeiling`) skips obviously-pathological
  -- terms up front (→ `skipped_large`), and the heartbeat budget inside
  -- `reverseProof` bounds the rest; the client (`Corpus.WorkerExtract`) wraps the
  -- whole request in a per-file wall-clock fallback so a slow proof never loses
  -- the file's records. When `closers`, we also pass the `simp [..]` calls
  -- harvested verbatim from THIS proof's source as argument-bearing closer
  -- candidates (keyed, like sig/body, by the decl's selection position).
  let (proofScript, proofMethod, proofTrace, proofStructTree) ← match info with
    | .thmInfo _ =>
        if reverseElab then
          -- Once the fold's wall-clock deadline has passed, `attemptReverse` is
          -- false: emit the record with a `deadline_skipped` marker instead of
          -- running the expensive reverse-elab, so the theorem's record still
          -- survives (only its proof script is forgone).
          if !attemptReverse then
            pure (none, some "deadline_skipped", none, none)
          else match info.value? (allowOpaque := true) with
          | some v =>
              let extraClosers := if closers then
                  match ranges? with
                  | some r => simpArgMap.getD (r.selectionRange.pos.line, r.selectionRange.pos.column) #[]
                  | none   => #[]
                else #[]
              let r ← reverseProofGuarded info.type v closers extraClosers traceReverseElab
              let trace? := if traceReverseElab && !r.trace.isEmpty then some r.trace else none
              let tree? := if traceReverseElab then r.structTree else none
              pure (if r.script.isEmpty then none else some r.script, some r.method, trace?, tree?)
          | none => pure (none, none, none, none)
        else pure (none, none, none, none)
    | _ => pure (none, none, none, none)
  return {
    name := info.name.toString
    kind := Common.kindToString info
    module := modStr
    type := typeStr
    value? := value?
    doc? := doc?
    deps := deps
    axioms := axStrs
    hasSorry
    signature
    body
    premises
    proofScript
    proofMethod
    proofTrace
    proofStructTree
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
    (simpArgMap : Std.HashMap (Nat × Nat) (Array String))
    (includeInternal includePrivate reverseElab closers traceReverseElab : Bool)
    (deadlineMs : Nat := 0)
    : CoreM (Array Lsp.CorpusManifestEntry) := do
  let env ← getEnv
  -- Collect the eligible constants first so we can order them before building.
  let mut eligible : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if Common.isUserConstant env name then
      if (← corpusEligible env includeInternal includePrivate name info) then
        eligible := eligible.push (name, info)
  -- Cheap-first scheduling only matters when we actually reverse-elaborate under a
  -- deadline; otherwise keep the original (name) order to minimize behavior change.
  let scheduled :=
    if reverseElab && deadlineMs > 0 then
      eligible.qsort (fun a b => reverseCost a.2 < reverseCost b.2)
    else eligible
  let startMs ← IO.monoMsNow
  let mut out : Array Lsp.CorpusManifestEntry := #[]
  for (_, info) in scheduled do
    -- Past the budget, keep emitting records but stop attempting reverse-elab.
    let attemptReverse := deadlineMs == 0 || (← IO.monoMsNow) - startMs < deadlineMs
    out := out.push (← buildEntry srcMap simpArgMap reverseElab closers traceReverseElab info attemptReverse)
  return out.qsort (fun a b => a.name < b.name)

open RequestM in
def handleCorpusManifest (p : Lsp.CorpusManifestParams)
    : RequestM (RequestTask Lsp.CorpusManifest) :=
  Common.handleSnapshotRequestWithSource
    (collect := fun src snaps => do
      let srcMap := buildSourceMap src snaps
      -- Only build the simp-arg map when closers are on (it walks every proof's
      -- syntax); otherwise it is unused.
      let simpArgMap ← if p.closers then buildSimpArgMap src snaps else pure {}
      let entries ← foldCorpusEntries srcMap simpArgMap
        p.includeInternal p.includePrivate p.reverseElab p.closers p.traceReverseElab
        p.reverseDeadlineMs
      return { entries })
    (empty := { entries := #[] })

initialize
  registerLspRequestHandler
    "$/lean/corpusManifest"
    Lsp.CorpusManifestParams
    Lsp.CorpusManifest
    handleCorpusManifest

end WorkerPlugins.CorpusManifest
