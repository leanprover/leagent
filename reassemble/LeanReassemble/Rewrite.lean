import Corpus.Artifact
import Corpus.CollectCommon
import Corpus.Frontend
import Corpus.Records
import Corpus.SourceSyntax
import Corpus.Verify
import Workers

namespace LeanReassemble

open Lean

/-- What to do with each selected theorem.

`keep` is not a way of skipping the rewriter — it runs the SAME pipeline
(match records to declarations, agree on the proof range, check the recorded
`body` against the source) and only substitutes the original text for the
`sorry`. So a `keep` artifact is a *verified reference state*: proof of the
correspondence between records and source, in compilable form.

`delete` is the only mode that touches more than a proof: it erases the whole
declaration (doc comment, attributes, signature, and value). It carries no
`body` obligation — there is nothing to preserve — and removing a name that other
declarations reference will break the build. That is the caller's responsibility;
the reassembler does no dependency analysis. -/
inductive ProofMode where
  /-- Replace each selected proof with `by sorry` (the default). -/
  | replace
  /-- Preserve each selected proof verbatim; output is byte-identical to source. -/
  | keep
  /-- Erase the whole declaration from the source. -/
  | delete
  deriving Inhabited, BEq, ToJson, FromJson

def ProofMode.toString : ProofMode → String
  | .replace => "sorry"
  | .keep    => "keep"
  | .delete  => "delete"

instance : ToString ProofMode := ⟨ProofMode.toString⟩

/-- What to do when a theorem cannot be reassembled (it fails to match, its body
disagrees with the source, or the artifact it produces does not verify). -/
inductive FailurePolicy where
  /-- Abort the whole run on the first failure (the default, historical behavior). -/
  | fail
  /-- Omit the failing theorem from the artifact and record it in `skipped`. In
  repo mode this leaves the theorem's original proof in place; in units mode it
  emits no task. -/
  | skip
  /-- Degrade the failing theorem to `delete`, record it in `failed`, and retry. -/
  | backoff
  deriving Inhabited, BEq, ToJson, FromJson

def FailurePolicy.toString : FailurePolicy → String
  | .fail    => "fail"
  | .skip    => "skip"
  | .backoff => "backoff"

instance : ToString FailurePolicy := ⟨FailurePolicy.toString⟩

structure RewriteConfig where
  sourceRoot : System.FilePath
  records : System.FilePath
  file : String
  output : System.FilePath
  proofMode : ProofMode := .replace
  /-- Optional per-theorem action overrides; absent theorems use `proofMode`. -/
  manifestPath : Option System.FilePath := none
  /-- What to do when a theorem fails to reassemble. -/
  onFailure : FailurePolicy := .fail

structure Edit where
  declaration : String
  range : Lean.Syntax.Range
  expected : String
  replacement : String
  deriving Inhabited, Repr

structure RewriteResult where
  sourcePath : System.FilePath
  moduleName : Name
  text : String
  edits : Array Edit

private structure Candidate where
  name : String
  key : Nat × Nat
  start : Nat × Nat
  deriving Inhabited

/-- Fail with the tool's diagnostic prefix. Shared across the reassembler. -/
def fail {α} (message : String) : IO α :=
  throw <| IO.userError s!"lean-reassemble: {message}"

/-- Strip a leading `./` or `.\` so record paths and CLI `--file` compare equal. -/
def normalizeRelativePath (path : String) : String :=
  ((path.dropPrefix "./").copy.dropPrefix ".\\").copy

/-- True iff `path` is `root` or lives beneath it. Both sides are normalized, so
callers need not pre-`realPath`. -/
def isWithin (root path : System.FilePath) : Bool :=
  let root := root.normalize.toString
  let path := path.normalize.toString
  path == root || path.startsWith (root ++ "/") || path.startsWith (root ++ "\\")

/-- Read and decode one JSON object per nonempty input line. Shares the extractor's
JSONL conventions via `Corpus.Artifact`, so writer and reader cannot drift. -/
def readRecords (path : System.FilePath) : IO (Array Corpus.ConstRecord) := do
  match Corpus.Artifact.parseJsonl (α := Corpus.ConstRecord) (← IO.FS.readFile path) with
  | .ok records => return records
  | .error error => fail s!"{path}: {error}"

/-- Select theorem records for one source file and reject ambiguous input. -/
def selectTheorems (records : Array Corpus.ConstRecord) (file : String) :
    IO (Array Corpus.ConstRecord) := do
  let requested := normalizeRelativePath file
  let mut selected := #[]
  let mut names : Std.HashSet String := {}
  for record in records do
    if Corpus.Artifact.isTheoremRecord record then
      let some recordFile := record.file
        | fail s!"theorem record {record.name} has no file"
      if normalizeRelativePath recordFile == requested then
        if names.contains record.name then
          fail s!"duplicate theorem record for {record.name}"
        names := names.insert record.name
        selected := selected.push record
  if selected.isEmpty then
    fail s!"no theorem records found for {file}"
  return selected

private def declarationCandidates (frontendResult : Corpus.Frontend.ElabResult) :
    IO (Array Candidate) :=
  Corpus.Frontend.runCollectorOn frontendResult do
    let mut candidates := #[]
    for verified in (← Corpus.Verify.verifiedFileConstants) do
      match verified.info with
      | .thmInfo _ =>
          if let some ranges ← Lean.findDeclarationRanges? verified.info.name then
            candidates := candidates.push {
              name := (Corpus.CollectCommon.displayName verified.info.name).toString
              key := (ranges.selectionRange.pos.line, ranges.selectionRange.pos.column)
              start := (ranges.range.pos.line, ranges.range.pos.column)
            }
      | _ => pure ()
    return candidates

private def commandForKey? (source : String) (commands : Array Syntax)
    (key : Nat × Nat) : Option Syntax :=
  let fileMap := source.toFileMap
  -- Descend into `mutual … end` (via `declarationNodes`) so each member matches its OWN
  -- `Command.declaration` node, not the enclosing block. A `mutual` block's keys cover
  -- only its first member, so a top-level-command search would match the first member to
  -- the whole block and misclassify every later member as `auxiliary` — leaving them
  -- un-holed. For a mutually recursive group with termination that is a correctness bug:
  -- holing one member changes the group's recursion, so the survivors' `decreasing_by`
  -- then runs against goals that no longer exist ("No goals to be solved"). A plain
  -- top-level declaration is itself a `Command.declaration`, so `declarationNodes`
  -- returns it unchanged.
  let decls := commands.foldl
    (fun acc c => acc ++ Corpus.SourceSyntax.declarationNodes c) #[]
  decls.find? fun decl =>
    Corpus.SourceSyntax.declarationKeys fileMap decl |>.contains key

private def commandIndent (source : String) (command : Syntax) : String := Id.run do
  let some range := Corpus.SourceSyntax.commandRange? command | return ""
  let fileMap := source.toFileMap
  let position := fileMap.toPosition range.start
  let lineStart := fileMap.lineStart position.line
  let whitespace := String.Pos.Raw.extract source lineStart range.start
  if whitespace.all fun char => char == ' ' || char == '\t' then whitespace else ""

/-- The text that replaces one proof's source range.

Under `.keep` the replacement IS the original slice, so applying the edits is the
identity on the file. We deliberately keep it flowing through the edit machinery
rather than short-circuiting: the range still has to be found and validated, which
is what makes a kept artifact evidence that the records match the source. -/
private def replacementFor (mode : ProofMode)
    (kind : Corpus.SourceSyntax.DeclValueKind) (indent original : String) : String :=
  match mode with
  | .keep => original
  | .delete => ""  -- unused: delete replaces the whole command range, see `planEdits`.
  | .replace =>
    let proof := s!"by\n{indent}  sorry"
    match kind with
    | .simple => proof
    | .equations | .whereBody => s!":= {proof}"

/-- Validate edit bounds and reject overlapping source ranges. -/
def validateEdits (source : String) (edits : Array Edit) : IO Unit := do
  let sourceSize := source.rawEndPos.byteIdx
  for edit in edits do
    if edit.range.start.byteIdx > edit.range.stop.byteIdx ||
        edit.range.stop.byteIdx > sourceSize then
      fail s!"invalid proof range for {edit.declaration}"
    let actual := String.Pos.Raw.extract source edit.range.start edit.range.stop
    if actual != edit.expected then
      fail s!"source changed at proof range for {edit.declaration}"
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  for index in [1:ascending.size] do
    let previous := ascending[index - 1]!
    let current := ascending[index]!
    if current.range.start.byteIdx < previous.range.stop.byteIdx then
      fail s!"overlapping proof ranges for {previous.declaration} and {current.declaration}"

/-- Compute the single edit for one record's matched declaration `command`.

`.delete` erases the whole command (`commandRange?`) and carries no `body`
obligation. `.keep`/`.replace` operate on the proof range and verify the recorded
`body` against the source slice, so a wrong range is caught here rather than by the
build. -/
private def planEdit (source : String) (command : Syntax) (record : Corpus.ConstRecord)
    (mode : ProofMode) : IO Edit := do
  match mode with
  | .delete =>
    let some range := Corpus.SourceSyntax.commandRange? command
      | fail s!"declaration syntax range not found for {record.name}"
    let expected := String.Pos.Raw.extract source range.start range.stop
    return { declaration := record.name, range, expected, replacement := "" }
  | .keep | .replace =>
    let some (kind, proofRange) := Corpus.SourceSyntax.proofRange? command
      | fail s!"proof syntax not found for {record.name}"
    -- The recorded `body` is the bare proof span — exactly what the extractor slices
    -- from `proofRange?` — so verify it against that narrow range BEFORE widening below.
    let proofSlice := String.Pos.Raw.extract source proofRange.start proofRange.stop
    if let some body := record.body then
      if proofSlice.trimAsciiEnd.toString != body then
        fail s!"record body does not match source proof for {record.name}"
    -- Overwrite a WIDER range than the body span: for `.simple`, `proofReplacementRange?`
    -- extends past the proof term over any `termination_by`/`decreasing_by` suffix AND
    -- `where`/`let rec` helpers, which serve only this proof. Leaving them would strand
    -- termination hints on a now-non-recursive `by sorry` (Lean: "unused termination
    -- hints", then a leftover `decreasing_by` run against absent goals) and orphan dead
    -- `where` helpers. Under `.keep` the replacement is that widened slice verbatim, so
    -- the output stays byte-identical.
    let some (_, range) := Corpus.SourceSyntax.proofReplacementRange? command
      | fail s!"proof syntax not found for {record.name}"
    let expected := String.Pos.Raw.extract source range.start range.stop
    return {
      declaration := record.name
      range
      expected
      replacement := replacementFor mode kind (commandIndent source command) expected
    }

/-- The result of planning a set of records against one file. `edits` are the
records that matched and planned; `failures` pairs each record that could not be
planned with the reason; `auxiliaries` names records that are not reassembly targets
at all (see `RecordPlan.auxiliary`). The strict `planEdits` throws on the first
failure; the resilient policies (`skip`/`backoff`) inspect `failures` instead. -/
structure PlanOutcome where
  edits : Array Edit
  failures : Array (String × String)
  auxiliaries : Array String

/-- The outcome of planning one record against its file.

`auxiliary` is the case the corpus surfaced: a record that matches a real elaborated
constant, but whose declaration has NO standalone declaration syntax to edit — a
`where`/`let rec` helper, lifted to its own constant but written as a term-level
`letRecDecl` inside its parent's proof. The reassembler neither can nor needs to hole
such a constant on its own: under `keep` it rides along inside its parent's preserved
proof, and under `sorry`/`delete` the parent's edit already erases the whole value it
lives in (`proofReplacementRange?` extends over the parent's `where` clause). It is
therefore **informational** — excluded from the target set, not reported as a failure.
This is distinct from "did not match a declaration" (`failed`), which means the record
disagrees with the source (drift).

A `mutual … end` MEMBER is NOT auxiliary: `commandForKey?` descends into the block via
`declarationNodes`, so each member matches its own `Command.declaration` node and is
holed in its own right — required, because holing only some members of a mutually
recursive group breaks the survivors' termination proofs. -/
inductive RecordPlan where
  | planned (edit : Edit) (key : Nat × Nat)
  | auxiliary
  | failed (reason : String)

/-- One theorem the run could not reassemble, with the action taken. `action` is
`"skipped"` (its proof left as-is / no task emitted) or `"failed"` (backed off to a
delete). Collected so the artifact's report NAMES what did not reassemble, rather
than only tallying counts — a `skip`/`backoff` run is then auditable after the
fact. -/
structure FailureReport where
  name : String
  action : String
  reason : String
  deriving Inhabited, ToJson, FromJson

/-- Render collected failures as a JSON array of `{theorem, action, reason}`. -/
def failuresJson (failures : Array FailureReport) : Lean.Json :=
  Lean.Json.arr <| failures.map fun f => Lean.Json.mkObj [
    ("theorem", f.name), ("action", f.action), ("reason", f.reason)]

/-- Plan the edit for one record against `candidates`, classifying the record as
`planned`, `auxiliary` (no standalone syntax — see `RecordPlan`), or `failed`. Never
throws for a per-record problem — that is what makes it usable under `skip`. -/
private def planOneRecord (frontendResult : Corpus.Frontend.ElabResult)
    (candidates : Array Candidate) (matchedKeys : Std.HashSet (Nat × Nat))
    (record : Corpus.ConstRecord) (mode : ProofMode)
    : IO RecordPlan := do
  try
    if record.module != frontendResult.file.module.toString then
      fail s!"record module does not match source file for {record.name}"
    let matchingCandidates := candidates.filter fun candidate =>
      candidate.name == record.name &&
        (record.startLine.map (· == candidate.start.1)).getD true &&
        (record.startCol.map (· == candidate.start.2)).getD true
    if matchingCandidates.size == 0 then
      fail s!"theorem record did not match a declaration: {record.name}"
    if matchingCandidates.size != 1 then
      fail s!"theorem record matched {matchingCandidates.size} declarations: {record.name}"
    let candidate := matchingCandidates[0]!
    if matchedKeys.contains candidate.key then
      fail s!"multiple records matched declaration {record.name}"
    -- The record matched a real elaborated constant, but no declaration node covers its
    -- position: it is a `where`/`let rec` auxiliary, written as a term-level `letRecDecl`
    -- inside another declaration's proof. Such a constant has no declaration syntax to
    -- hole on its own — its parent's edit already governs the text it lives in — so it is
    -- an auxiliary, not a failure. (`mutual` members DO get their own node here, via
    -- `declarationNodes`. Contrast the zero-candidate case above: that is drift.)
    let some command :=
        commandForKey? frontendResult.source frontendResult.commands candidate.key
      | return .auxiliary
    let edit ← planEdit frontendResult.source command record mode
    return .planned edit candidate.key
  catch error =>
    -- Strip the shared prefix so a collected reason reads cleanly in a report.
    let message := error.toString
    return .failed ((message.dropPrefix "lean-reassemble: ").copy)

/-- Match records to declarations and compute non-overlapping source edits,
collecting per-record failures rather than aborting on the first.

`mode` is the run's default action; `modeFor` overrides it per record name (the
manifest hook). Cross-record invariants — one record per declaration, no
overlapping ranges — are still enforced over the records that DID plan. -/
def planEditsCollecting (frontendResult : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) (mode : ProofMode := .replace)
    (modeFor : String → ProofMode := fun _ => mode)
    : IO PlanOutcome := do
  let candidates ← declarationCandidates frontendResult
  let mut edits := #[]
  let mut failures := #[]
  let mut auxiliaries := #[]
  let mut matchedKeys : Std.HashSet (Nat × Nat) := {}
  for record in records do
    match ← planOneRecord frontendResult candidates matchedKeys record (modeFor record.name) with
    | .planned edit key =>
      matchedKeys := matchedKeys.insert key
      edits := edits.push edit
    | .auxiliary => auxiliaries := auxiliaries.push record.name
    | .failed reason => failures := failures.push (record.name, reason)
  validateEdits frontendResult.source edits
  return { edits, failures, auxiliaries }

/-- Match records to declarations and compute non-overlapping source edits.

`mode` is the run's default action. `modeFor`, when given, overrides it per record
name — this is the manifest hook: the resolver returns the manifest's action for a
named theorem or the default for everything else.

Strict: the first record that fails to plan aborts the whole call. Callers that
tolerate failures use `planEditsCollecting` instead. -/
def planEdits (frontendResult : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) (mode : ProofMode := .replace)
    (modeFor : String → ProofMode := fun _ => mode)
    : IO (Array Edit) := do
  let outcome ← planEditsCollecting frontendResult records mode modeFor
  if let some (_, reason) := outcome.failures[0]? then
    fail reason
  return outcome.edits

/-- Full names the run resolves to `.delete`. Only theorem records are deletable —
a `def`/`inductive`/`structure` is never holed or removed — so `modeFor` (which
returns the default action for any name it does not override) is only consulted for
theorem names here. `moduleFilter`, when set, restricts the set to one module:
`materialize-units` removes only a target's SAME-module neighbours. -/
def deletedNames (records : Array Corpus.ConstRecord)
    (modeFor : String → ProofMode) (moduleFilter : Option String := none)
    : Std.HashSet String := Id.run do
  let mut result : Std.HashSet String := {}
  for record in records do
    if Corpus.Artifact.isTheoremRecord record && moduleFilter.all (· == record.module) then
      if modeFor record.name == .delete then
        result := result.insert record.name
  return result

/-- `(dependent, deleted)` pairs where a SURVIVING declaration's `deps` names a
theorem the run deletes — the deletions that would break the build.

A survivor is any non-theorem record (defs/inductives/structures are never removed)
or a theorem resolved to `.keep`. A `.replace` (holed) theorem is deliberately NOT
a survivor: its proof becomes `by sorry`, which drops the references it carried, so
a holed dependent cannot dangle. Deleted names are always theorems, and theorems
are referenced from proofs, so this direct-`deps` check is complete over transitive
chains: every hop is itself a record we evaluate (S→M→D is caught as M→D if M
survives, or as S→M if M is itself deleted).

`moduleFilter` restricts BOTH the delete-set and the dependents to one module —
units prunes same-module neighbours only, and cross-module references resolve from
the prebuilt shared cache rather than the unit's file. -/
def danglingReferences (records : Array Corpus.ConstRecord)
    (modeFor : String → ProofMode) (moduleFilter : Option String := none)
    : Array (String × String) := Id.run do
  let deleted := deletedNames records modeFor moduleFilter
  if deleted.isEmpty then return #[]
  let mut pairs := #[]
  for record in records do
    unless moduleFilter.all (· == record.module) do continue
    let survives :=
      if Corpus.Artifact.isTheoremRecord record then modeFor record.name == .keep else true
    if survives then
      for dep in record.deps do
        if deleted.contains dep then
          pairs := pairs.push (record.name, dep)
  return pairs

/-- One fail-fast message naming every `dependent -> deleted` pair. -/
def dependencyConflictMessage (pairs : Array (String × String)) : String :=
  let lines := pairs.toList.map fun (dependent, deleted) => s!"  {dependent} -> {deleted}"
  s!"dependency conflict: {pairs.size} surviving declaration(s) reference deleted \
    theorem(s); deleting would break the build:\n{String.intercalate "\n" lines}"

/-- Delete-edits that erase every evaluation command (`#eval`, `#eval!`, `#reduce`,
`#guard`, `#guard_msgs`) in an elaborated file.

These commands abort the build once a proof they transitively depend on is holed
("Aborting evaluation since the expression depends on the 'sorry' axiom"), so a
`--proofs sorry` reassembly must remove them to build. Each edit covers the whole
command range — including a `#guard_msgs` block's leading `/-- info: … -/`
docstring — with an empty replacement, so no dangling docstring is left behind.

The ranges come from the SAME `frontendResult` a file's proof edits do, so both
sets share one coordinate space and compose in a single `applyEdits` pass. Every
`theorem`/`def` is left intact — only the evaluation commands are removed. -/
def evalStripEdits (frontendResult : Corpus.Frontend.ElabResult) : Array Edit := Id.run do
  let source := frontendResult.source
  let mut edits := #[]
  for cmd in frontendResult.commands do
    if Corpus.SourceSyntax.isEvaluationCommand cmd then
      if let some range := Corpus.SourceSyntax.commandRange? cmd then
        let expected := String.Pos.Raw.extract source range.start range.stop
        edits := edits.push {
          declaration := s!"«eval command @ {range.start.byteIdx}»"
          range, expected, replacement := "" }
  return edits

/-- Apply validated byte-range edits in one left-to-right pass. -/
def applyEdits (source : String) (edits : Array Edit) : IO String := do
  validateEdits source edits
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  let mut result := ""
  let mut cursor : String.Pos.Raw := 0
  for edit in ascending do
    result := result ++ String.Pos.Raw.extract source cursor edit.range.start
    result := result ++ edit.replacement
    cursor := edit.range.stop
  result := result ++ String.Pos.Raw.extract source cursor source.rawEndPos
  return result

/-- Reject edited text that produces an LSP error diagnostic. -/
def validateWithWorker (sourcePath : System.FilePath) (text : String)
    (timeoutMs : Nat := 60000) : IO Unit := do
  let absPath ← IO.FS.realPath sourcePath
  let uri := System.Uri.pathToUri absPath
  let pool ← Workers.WorkerPool.new (setsidWorkers := false)
  let worker ← Workers.Worker.spawn uri text pool.workerPath (setsid := false)
  try
    match (← worker.waitForDiagnostics timeoutMs) with
    | .timeout => fail s!"timed out validating {sourcePath}"
    | .workerExited => fail s!"Lean worker exited while validating {sourcePath}"
    | .done =>
        let some diagnostics ← worker.currentDiagnostics
          | fail s!"Lean worker returned no diagnostics for {sourcePath}"
        let errors := diagnostics.diagnostics.filter
          (·.severity? == some Lean.Lsp.DiagnosticSeverity.error)
        unless errors.isEmpty do
          let messages := "\n".intercalate (errors.toList.map (·.message))
          fail s!"Lean reported {errors.size} error(s) for {sourcePath}:\n{messages}"
  finally
    let _ ← worker.shutdown

/-- One source file, elaborated once, ready to be rewritten any number of ways.

Separated from `rewriteSourceFile` because `materialize-units` needs MANY rewrites
of the same file — one per target theorem — and elaboration is the expensive part.
Reusing this across targets keeps the cost one elaboration per file rather than one
per task. -/
structure PreparedFile where
  sourceAbs      : System.FilePath
  relFile        : String
  moduleName     : Name
  frontendResult : Corpus.Frontend.ElabResult

/-- Locate, validate, and elaborate one project-relative source file. -/
unsafe def prepareSourceFile (sourceRoot : System.FilePath) (file : String)
    : IO PreparedFile := do
  let root ← IO.FS.realPath sourceRoot
  let relFile := normalizeRelativePath file
  let requestedPath : System.FilePath := relFile
  if requestedPath.isAbsolute then
    fail s!"--file must be project-relative: {file}"
  let sourcePath := root / relFile
  if !(← sourcePath.pathExists) then
    fail s!"source file does not exist: {sourcePath}"
  let sourceAbs ← IO.FS.realPath sourcePath
  unless isWithin root sourceAbs do
    fail s!"source file escapes --source-root: {file}"
  let some moduleName := Corpus.Discover.filePathToModule root sourceAbs
    | fail s!"cannot derive module name for {sourcePath}"
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let frontendResult ← Corpus.Frontend.elaborateFile importLock {
    absPath := sourceAbs
    module := moduleName
    relPath := relFile
  }
  if frontendResult.hasErrors then
    fail s!"frontend elaboration failed for {sourcePath}"
  return { sourceAbs, relFile, moduleName, frontendResult }

/-- Rewrite an already-prepared file for a given set of records. `modeFor` is the
per-record action resolver (see `planEdits`); it defaults to the flat `mode`. -/
def rewritePreparedFile (prepared : PreparedFile)
    (selected : Array Corpus.ConstRecord) (mode : ProofMode := .replace)
    (validate : Bool := true) (modeFor : String → ProofMode := fun _ => mode)
    : IO RewriteResult := do
  let edits ← planEdits prepared.frontendResult selected mode modeFor
  let rewritten ← applyEdits prepared.frontendResult.source edits
  if validate then
    validateWithWorker prepared.sourceAbs rewritten
  return { sourcePath := prepared.sourceAbs, moduleName := prepared.moduleName,
           text := rewritten, edits }

/-- Rewrite one source file for every record that belongs to it. -/
unsafe def rewriteSourceFile (sourceRoot : System.FilePath)
    (records : Array Corpus.ConstRecord) (file : String)
    (mode : ProofMode := .replace) (modeFor : String → ProofMode := fun _ => mode)
    : IO RewriteResult := do
  let prepared ← prepareSourceFile sourceRoot file
  rewritePreparedFile prepared (← selectTheorems records prepared.relFile) mode
    (modeFor := modeFor)

end LeanReassemble
