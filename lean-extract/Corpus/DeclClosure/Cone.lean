/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.Discover
import Corpus.CollectCommon
import Corpus.Extract

/-!
Phase 1 of single-declaration extraction: resolve a target and compute its
dependency closure.

Everything here runs against an IMPORT-ONLY environment — `importModules` over the
`--modules` roots, no elaboration. That ordering is the point: the closure tells us
which source files matter, so only those get elaborated (phase 2, `Emit`).

## The two cones

Every closure member is annotated with its role relative to the target:

  * `statement` — reachable from the target's TYPE, so it is needed to *state* it.
  * `proof`     — reachable only through the target's proof/value.
  * `target`    — the requested declaration itself.

Both come from `CollectCommon.collectPremisesFrom` under different seeds, so the
graph walk is shared with the `premises` dataset field and cannot drift from it.
Because `getUsedConstantsAsSet` is `type ∪ value`, `statement ⊆ proof`, and a
proof-cone member is classified by testing statement-cone membership.

Ownership here is the root-prefix notion (`CollectCommon.isOwnedByRoots`) — the
same predicate the legacy import walk applies, and the only one available without
an elaborated file. Each record's own `premises` field was computed per-file
against `CollectCommon.projectRoot`; the two agree for a single-root project and
diverge for multi-root runs, which is why `metadata.json` records both.
-/

namespace Corpus.DeclClosure

open Lean


open Lean

/-- Which cone a closure member belongs to, relative to one target. -/
inductive Role where
  /-- The requested declaration itself. -/
  | target
  /-- Reachable from the target's type — needed to state it. -/
  | statement
  /-- Reachable only through the target's proof/value. -/
  | proof
  deriving Inhabited, BEq

def Role.toString : Role → String
  | .target    => "target"
  | .statement => "statement"
  | .proof     => "proof"

instance : ToString Role := ⟨Role.toString⟩

/-- One resolved target: the requested name, its constant info, and the module
that defines it. -/
structure Target where
  /-- The name as the user wrote it on the command line. -/
  requested : Name
  /-- The name as it resolves in the environment (may be the mangled `_private.…`
  form when the user asked for a private declaration by its user name). -/
  resolved  : Name
  /-- The display (unmangled) name — how the record's `name` field will read. -/
  display   : Name
  /-- The module that defines the target. -/
  module    : Name
  deriving Inhabited

/-- Why a closure member has no emitted record, as a plain category label.

A cone reaches every constant the elaborated term graph mentions, including
machinery the corpus deliberately excludes (`corpusEligible`). On a real proof
these OUTNUMBER the emitted records — `church_rosser` in the LambdaCalc corpus
reaches 83 of them — so they are grouped and counted rather than listed raw.

These are diagnostic labels: they are grouped on, sorted, printed, and written to
`dropped.json`, and nothing branches on them. A `String` is therefore the right
type; an enum would buy exhaustiveness checking over values that are only ever
displayed, at the cost of a constructor set plus a rendering table.

`unexplained` is the one category that matters operationally — it means a member
looked eligible but produced no record — so `dropIsUnexplained` names it rather
than leaving the string to be matched inline. -/
abbrev DropReason := String

/-- The category that signals a real gap rather than a deliberate exclusion. -/
def unexplainedDrop : DropReason := "unexplained"

def dropIsUnexplained (r : DropReason) : Bool := r == unexplainedDrop

/-- One target's computed closure: the role of every member, keyed by DISPLAY name
(the form records carry), plus the bookkeeping needed to disambiguate private
names and to explain members that will never resolve to a record. -/
structure Closure where
  target      : Target
  /-- Display name → role, for every closure member and the target. -/
  roles       : Std.HashMap String Role
  /-- Display name → (raw name, defining module) for private members, so a
  consumer can disambiguate names the dataset unmangles. -/
  privateMap  : Array (String × String × String)
  /-- Modules that define at least one closure member (including the target's). -/
  modules     : Array Name
  /-- Display name → why it can never resolve to a record, for members the
  eligibility filter excludes. A member absent from this map that still fails to
  resolve is `unexplained` — the case worth investigating. -/
  dropReasons : Std.HashMap String DropReason
  deriving Inhabited

/-- Fail with the tool's diagnostic prefix. Shared with `Emit`, so both phases
report the same way. -/
def fail {α} (message : String) : IO α :=
  throw <| IO.userError s!"corpus-extract: {message}"

/-! Ownership uses the shared root-prefix notion from `CollectCommon`
(`isOwnedModuleName` / `isOwnedByRoots` / `moduleOf?`) — the same predicate the
legacy import walk applies, and the only one available in an import-only
environment. See `CollectCommon.isOwnedModuleName` for how it differs from the
per-file collector's `isOwnedName`. -/

/-- Resolve one requested target name in an import-only environment.

A user may name a private declaration by its USER name (`Mod.helper`), while the
environment holds it mangled (`_private.Mod.0.helper`). We therefore try the name
as given, then scan for a constant whose display name matches. A scan that finds
several distinct constants is ambiguous and fails rather than guessing. -/
def resolveTarget (env : Environment) (requested : Name) : IO Target := do
  -- Fast path: the name resolves directly.
  if let some info := env.find? requested then
    let some modName := CollectCommon.moduleOf? env info.name
      | fail s!"--decl {requested} is a builtin with no defining module"
    return { requested
             resolved := info.name
             display  := CollectCommon.displayName info.name
             module   := modName }
  -- Slow path: the user may have named a private decl by its unmangled form.
  let wanted := requested.toString
  let mut hits : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (CollectCommon.displayName name).toString == wanted then
      unless hits.contains name do
        hits := hits.push name
  match hits.toList with
  | [] =>
      fail s!"--decl {requested} not found in the import closure of the \
        --modules roots. If it lives in a file no root module imports, it is an \
        orphan — check --list-orphans."
  | [only] =>
      let some info := env.find? only
        | fail s!"--decl {requested} resolved to {only}, which has no constant info"
      let some modName := CollectCommon.moduleOf? env info.name
        | fail s!"--decl {requested} is a builtin with no defining module"
      return { requested
               resolved := info.name
               display  := CollectCommon.displayName info.name
               module   := modName }
  | several =>
      let rendered := ", ".intercalate (several.map toString)
      fail s!"--decl {requested} is ambiguous: {several.length} constants share \
        that display name ({rendered}). Pass the raw name to disambiguate."

/-- Why `name` will be dropped by the corpus eligibility filter, or `none` if it
should produce a record.

Deliberately mirrors `CorpusManifest.corpusEligible` + `CollectCommon.alwaysSkip`,
but reports WHICH rule applies instead of a bare bool. Order matters: the most
specific structural reason wins, so a generated `match_1` is reported as
`internal` rather than the vaguer `generated`. -/
def dropReasonFor (env : Environment) (includeInternal includePrivate : Bool)
    (name : Name) : Option DropReason :=
  match env.find? name with
  | none => some unexplainedDrop
  | some info =>
    -- `alwaysSkip`, decomposed into its constituent rules.
    if Lean.isAuxRecursor env name then some "recursors"
    else if Lean.isNoConfusion env name then some "noConfusion_stubs"
    else if env.isProjectionFn name then some "projections"
    else if CollectCommon.hasGeneratedTag name
         || CollectCommon.isGeneratedTheoremSuffix name then some "generated_companions"
    else if !includePrivate && Lean.isPrivateName name then some "private_excluded"
    else if !includeInternal then
      -- The internal-detail rule, with private user decls exempted exactly as
      -- `corpusEligible` exempts them.
      let genuinePrivate :=
        Lean.isPrivateName name && !(Lean.privateToUserName name).isInternalDetail
      if name.isInternalDetail && !genuinePrivate then some "equation_compiler_helpers"
      else match info with
        | .ctorInfo _ => some "constructors"
        | .recInfo _  => some "recursors"
        | _           => none
    else none

/-- A synthetic theorem is one with no declaration range; that needs `CoreM`, so it
is checked separately from the pure rules in `dropReasonFor`. -/
private def isRangeless (name : Name) : CoreM Bool := do
  return (← Lean.findDeclarationRanges? name).isNone

/-- Compute one target's closure: both cones, the defining-module set, the
private-name map, and why each ineligible member will be dropped. Runs against
the import-only environment. -/
def computeClosure (env : Environment) (roots : Array Name) (target : Target)
    (includeInternal includePrivate : Bool) : IO Closure := do
  let owned := CollectCommon.isOwnedByRoots env roots
  let proofCone := CollectCommon.collectPremises env owned target.resolved
  let stmtCone := CollectCommon.collectStatementPremises env owned target.resolved
  -- Statement membership is decided on RAW names (the graph's vocabulary), so a
  -- private decl reached both ways is classified consistently.
  let stmtSet : Std.HashSet Name := stmtCone.foldl (·.insert ·) {}
  let mut roles : Std.HashMap String Role := {}
  let mut privateMap : Array (String × String × String) := #[]
  let mut dropReasons : Std.HashMap String DropReason := {}
  let mut moduleSet : Std.HashSet Name := {target.module}
  let mut modules : Array Name := #[target.module]
  let targetDisplay := target.display.toString
  -- Records are keyed by DISPLAY name, but the cone walks RAW names, and
  -- `displayName` is not injective (it unmangles `_private.Mod.N.foo` to `foo`, so
  -- two private constants in different modules can collide). Track which raw
  -- constant claimed each display name: a second, DISTINCT claimant means the
  -- closure cannot be keyed unambiguously, whatever the roles involved.
  let mut rawByDisplay : Std.HashMap String Name :=
    (({} : Std.HashMap String Name)).insert targetDisplay target.resolved
  -- The target's own role wins over any cone membership (a declaration can be
  -- reachable from itself through a mutual block).
  roles := roles.insert targetDisplay .target
  -- The union of both cones is just the proof cone: statement ⊆ proof, because
  -- `getUsedConstantsAsSet` is `type ∪ value` and the statement seed is `type`.
  for raw in proofCone do
    let display := (CollectCommon.displayName raw).toString
    if let some claimant := rawByDisplay[display]? then
      if claimant != raw then
        fail s!"closure for {target.display} is ambiguous: the distinct constants \
          {claimant} and {raw} both display as {display}, so their records cannot \
          be told apart. Extract them under their raw names, or exclude one."
      -- Same constant reached twice (the cone is deduped, so this is defensive).
      continue
    rawByDisplay := rawByDisplay.insert display raw
    -- The target reached through a cycle keeps its `target` role.
    if display == targetDisplay then
      continue
    roles := roles.insert display (if stmtSet.contains raw then .statement else .proof)
    -- Record up front why an ineligible member can never produce a record, so the
    -- projection can summarize rather than dump a raw name list.
    if let some reason := dropReasonFor env includeInternal includePrivate raw then
      dropReasons := dropReasons.insert display reason
    if Lean.isPrivateName raw then
      let modStr := (CollectCommon.moduleOf? env raw).map Lean.Name.toString |>.getD ""
      privateMap := privateMap.push (display, raw.toString, modStr)
    if let some m := CollectCommon.moduleOf? env raw then
      unless moduleSet.contains m do
        moduleSet := moduleSet.insert m
        modules := modules.push m
  -- Range-less synthetic theorems need `CoreM`; fold them in as a second pass over
  -- only the members not already explained by a pure rule.
  let synthetic ← runMetaOnEnv env do
    let mut out : Array String := #[]
    for (display, raw) in rawByDisplay.toList do
      unless display == targetDisplay || dropReasons.contains display do
        if let some (.thmInfo _) := env.find? raw then
          if (← isRangeless raw) then
            out := out.push display
    return out
  for display in synthetic do
    dropReasons := dropReasons.insert display "synthetic_theorems"
  return { target
           roles
           privateMap := privateMap.qsort (fun a b => a.1 < b.1)
           modules := modules.qsort (·.toString < ·.toString)
           dropReasons }

/-- Map module names to discovered source files. Modules with no file on disk are
reported separately: that happens when a closure reaches a dependency package
rather than the project under study. -/
def filesForModules (files : Array Discover.DiscoveredFile) (modules : Array Name)
    : Array Discover.DiscoveredFile × Array Name := Id.run do
  let mut byModule : Std.HashMap Name Discover.DiscoveredFile := {}
  for df in files do
    byModule := byModule.insert df.module df
  let mut selected : Array Discover.DiscoveredFile := #[]
  let mut missing : Array Name := #[]
  for m in modules do
    match byModule[m]? with
    | some df => selected := selected.push df
    | none    => missing := missing.push m
  return (selected.qsort (fun a b => a.relPath < b.relPath), missing)

end Corpus.DeclClosure
