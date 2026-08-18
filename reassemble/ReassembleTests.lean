import LeanReassemble
import Corpus.CorpusManifest
import Corpus.WorkerExtract

open Lean

namespace ReassembleTests

private def assertIO (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw <| IO.userError s!"reassemble test failed: {message}"

private def expectFailure (label : String) (action : IO Unit) : IO Unit := do
  let failed ←
    try
      action
      pure false
    catch _ =>
      pure true
  assertIO failed s!"expected failure: {label}"

private partial def legacyFindByKind (stx : Syntax)
    (kinds : List SyntaxNodeKind) : Option Syntax :=
  if kinds.contains stx.getKind then some stx
  else match stx with
    | .node _ _ args => args.findSome? (legacyFindByKind · kinds)
    | _ => none

private def legacySlice (stx : Syntax) (source : String) : Option String := do
  let range ← stx.getRange?
  pure (String.Pos.Raw.extract source range.start range.stop).trimAsciiEnd.copy

private def legacySignatureBody (command : Syntax) (source : String) :
    Option String × Option String :=
  let signatureKinds :=
    [``Lean.Parser.Command.declSig, ``Lean.Parser.Command.optDeclSig]
  let valueKinds :=
    [``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
     ``Lean.Parser.Command.whereStructInst]
  let signature := (legacyFindByKind command signatureKinds).bind (legacySlice · source)
  let body := (legacyFindByKind command valueKinds).bind fun value =>
    if value.getKind == ``Lean.Parser.Command.declValSimple then
      legacySlice value[1] source
    else
      legacySlice value source
  (signature, body)

private def legacySourceMap (source : String) (commands : Array Syntax) :
    Std.HashMap (Nat × Nat) (Option String × Option String) := Id.run do
  let fileMap := source.toFileMap
  let mut result := {}
  for command in commands do
    if command.getKind == ``Lean.Parser.Command.declaration then
      if let some declId := legacyFindByKind command [``Lean.Parser.Command.declId] then
        if let some rawPos := declId[0].getPos? then
          let pos := fileMap.toPosition rawPos
          result := result.insert (pos.line, pos.column)
            (legacySignatureBody command source)
  return result

private def legacyDeclarationKey? (fileMap : FileMap) (command : Syntax) :
    Option (Nat × Nat) := do
  let rawPos ← match legacyFindByKind command [``Lean.Parser.Command.declId] with
    | some declId => declId[0].getPos?
    | none => (command.getArg 1).getPos? <|> command.getPos?
  let pos := fileMap.toPosition rawPos
  return (pos.line, pos.column)

private def legacyDeclSourceMap (source : String) (commands : Array Syntax) :
    Std.HashMap (Nat × Nat) String := Id.run do
  let fileMap := source.toFileMap
  let mut result := {}
  for command in commands do
    if command.getKind == ``Lean.Parser.Command.declaration then
      if let some commandSource := legacySlice command source then
        if let some key := legacyDeclarationKey? fileMap command then
          result := result.insert key commandSource
  return result

private def sourceMapsEqual
    (left right : Std.HashMap (Nat × Nat) (Option String × Option String)) : Bool :=
  left.size == right.size &&
    left.toList.all fun (key, value) => right[key]? == some value

private def declSourceMapsEqual
    (left right : Std.HashMap (Nat × Nat) String) : Bool :=
  left.size == right.size &&
    left.toList.all fun (key, value) => right[key]? == some value

private def rangeSource (source : String) (edit : LeanReassemble.Edit) : String :=
  String.Pos.Raw.extract source edit.range.start edit.range.stop

private def bytesOutsideEditsUnchanged (source rewritten : String)
    (edits : Array LeanReassemble.Edit) : Bool := Id.run do
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  let mut sourcePos := 0
  let mut rewrittenPos := 0
  for edit in ascending do
    let unchangedSize := edit.range.start.byteIdx - sourcePos
    let sourceChunk := String.Pos.Raw.extract source ⟨sourcePos⟩ edit.range.start
    let rewrittenChunk := String.Pos.Raw.extract rewritten ⟨rewrittenPos⟩
      ⟨rewrittenPos + unchangedSize⟩
    if sourceChunk != rewrittenChunk then return false
    rewrittenPos := rewrittenPos + unchangedSize
    let replacementStop := rewrittenPos + edit.replacement.utf8ByteSize
    if String.Pos.Raw.extract rewritten ⟨rewrittenPos⟩ ⟨replacementStop⟩ !=
        edit.replacement then
      return false
    rewrittenPos := replacementStop
    sourcePos := edit.range.stop.byteIdx
  return String.Pos.Raw.extract source ⟨sourcePos⟩ source.rawEndPos ==
    String.Pos.Raw.extract rewritten ⟨rewrittenPos⟩ rewritten.rawEndPos

private unsafe def fixtureResult : IO Corpus.Frontend.ElabResult := do
  let root ← IO.FS.realPath "."
  let path ← IO.FS.realPath (root / "TestFixtures/RewriteFixture.lean")
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let result ← Corpus.Frontend.elaborateFile importLock {
    absPath := path
    module := `TestFixtures.RewriteFixture
    relPath := "TestFixtures/RewriteFixture.lean"
  }
  assertIO (!result.hasErrors) "fixture frontend elaboration"
  return result

private def testRewritePlan (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let selected ← LeanReassemble.selectTheorems records result.file.relPath
  let edits ← LeanReassemble.planEdits result selected
  assertIO (edits.size == selected.size) "one edit per selected theorem"
  for edit in edits do
    let proof := rangeSource result.source edit
    match edit.declaration with
    | "ReassemblyFixture.termProof" =>
        assertIO (proof == "True.intro") "term proof range"
    | "ReassemblyFixture.tacticProof" =>
        assertIO (proof.startsWith "by") "tactic proof range"
    | "ReassemblyFixture.equationProof" =>
        assertIO (proof.startsWith "| _ =>") "equation proof range"
    | "ReassemblyFixture.whereProof" =>
        assertIO (proof.startsWith "where") "where proof range"
    | "ReassemblyFixture.commentProof" =>
        assertIO (proof.contains "nested comment" && proof.contains "line comment")
          "comment proof range"
    | "ReassemblyFixture.unicodeProof" =>
        assertIO (proof.contains "αβγ") "Unicode proof range"
    | "ReassemblyFixture.attributedProof" | "ReassemblyFixture.privateProof" =>
        assertIO (proof.startsWith "by") s!"proof range for {edit.declaration}"
    | name =>
        throw <| IO.userError s!"unexpected edit: {name}"
  let rewritten ← LeanReassemble.applyEdits result.source edits
  let expected ← IO.FS.readFile "TestFixtures/RewriteFixture.expected.lean"
  assertIO (rewritten == expected) "golden rewritten source"
  assertIO (bytesOutsideEditsUnchanged result.source rewritten edits)
    "bytes outside proof ranges"

/-- `--proofs keep` must locate and validate every proof exactly as `sorry` mode
does, then write the file back unchanged. Byte-identical output is the assertion
that matters: it means the edit ranges were right, since a wrong range would
splice the wrong slice back. -/
private def testKeepProofs (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let selected ← LeanReassemble.selectTheorems records result.file.relPath
  let keepEdits ← LeanReassemble.planEdits result selected .keep
  let sorryEdits ← LeanReassemble.planEdits result selected .replace
  -- Same declarations, same ranges — only the replacement text differs.
  assertIO (keepEdits.size == selected.size) "keep mode plans one edit per theorem"
  assertIO (keepEdits.size == sorryEdits.size) "keep and sorry plan the same edits"
  for index in [:keepEdits.size] do
    let keep := keepEdits[index]!
    let repl := sorryEdits[index]!
    assertIO (keep.declaration == repl.declaration) "keep edit order matches"
    assertIO (keep.range.start.byteIdx == repl.range.start.byteIdx &&
              keep.range.stop.byteIdx == repl.range.stop.byteIdx)
      s!"keep and sorry select the same range for {keep.declaration}"
    -- The kept replacement IS the original slice, and the sorry one is not.
    assertIO (keep.replacement == keep.expected)
      s!"keep replacement is not the original proof for {keep.declaration}"
    assertIO (repl.replacement.contains "sorry")
      s!"sorry mode did not produce a sorry for {repl.declaration}"
  -- Applying kept edits is the identity, across every proof form the fixture
  -- covers (term, tactic, equations, where, comments, Unicode, private).
  let kept ← LeanReassemble.applyEdits result.source keepEdits
  assertIO (kept == result.source) "keep mode output is byte-identical to source"
  -- And it is genuinely different from what sorry mode produces.
  let sorried ← LeanReassemble.applyEdits result.source sorryEdits
  assertIO (kept != sorried) "keep and sorry produced the same output"

/-- `--proofs delete` erases the WHOLE declaration, not just the proof. Each delete
edit's range must cover the command (so its slice starts at the `theorem`/attribute
keyword and ends past the proof), the replacement must be empty, and applying the
edits must leave none of the deleted names in the output. -/
private def testDeleteProofs (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let selected ← LeanReassemble.selectTheorems records result.file.relPath
  let deleteEdits ← LeanReassemble.planEdits result selected .delete
  assertIO (deleteEdits.size == selected.size) "delete plans one edit per theorem"
  for edit in deleteEdits do
    assertIO (edit.replacement == "") s!"delete replacement empty for {edit.declaration}"
    -- The command range is wider than a proof range: it includes the signature, so
    -- the slice contains the declared name.
    let slice := rangeSource result.source edit
    let short := edit.declaration.splitOn "." |>.getLast!
    assertIO (slice.contains short)
      s!"delete range covers the declaration for {edit.declaration}"
  let deleted ← LeanReassemble.applyEdits result.source deleteEdits
  -- Every deleted theorem's `theorem <name>` header is gone from the output.
  for record in selected do
    let short := record.name.splitOn "." |>.getLast!
    assertIO (!deleted.contains s!"theorem {short}")
      s!"deleted declaration {record.name} still present"
  assertIO (deleted != result.source) "delete produced unchanged source"

/-- The manifest is a sparse override: named theorems take its action, the rest
follow the default. Planning with a resolver must select the right range machinery
per theorem (delete → whole command; keep/sorry → proof range). -/
private def testManifestOverride (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let selected ← LeanReassemble.selectTheorems records result.file.relPath
  -- Delete one theorem, keep another; the remainder default to sorry.
  let deleteName := "ReassemblyFixture.termProof"
  let keepName := "ReassemblyFixture.tacticProof"
  let json := Lean.Json.mkObj [("theorems", Lean.Json.mkObj [
    (deleteName, Lean.Json.str "delete"), (keepName, Lean.Json.str "keep")])]
  let manifest ← match LeanReassemble.Manifest.fromJson? json with
    | .ok m => pure m
    | .error e => throw <| IO.userError s!"manifest parse failed: {e}"
  let modeFor := fun name => manifest.actionFor name .replace
  let edits ← LeanReassemble.planEdits result selected .replace modeFor
  assertIO (edits.size == selected.size) "manifest plans one edit per theorem"
  for edit in edits do
    let slice := rangeSource result.source edit
    if edit.declaration == deleteName then
      assertIO (edit.replacement == "" && slice.contains "termProof")
        "manifest delete override erases the declaration"
    else if edit.declaration == keepName then
      assertIO (edit.replacement == edit.expected)
        "manifest keep override preserves the proof"
    else
      assertIO (edit.replacement.contains "sorry")
        s!"manifest default (sorry) for {edit.declaration}"
  -- Typo guard: a manifest key naming no eligible theorem is rejected.
  let eligible := Std.HashSet.ofArray (selected.map (·.name))
  expectFailure "manifest typo guard" do
    let bogus ← match LeanReassemble.Manifest.fromJson?
      (Lean.Json.mkObj [("theorems", Lean.Json.mkObj [("No.Such.Thm", Lean.Json.str "keep")])]) with
      | .ok m => pure m
      | .error e => throw <| IO.userError e
    bogus.validateKeys eligible

/-- `planEditsCollecting` collects per-record failures instead of aborting — the
foundation of `--on-failure skip|backoff`. A record whose body disagrees with the
source is reported as a failure while its well-formed siblings still plan. -/
private def testCollectingFailures (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let selected ← LeanReassemble.selectTheorems records result.file.relPath
  assertIO (selected.size ≥ 2) "fixture has at least two theorems"
  -- Corrupt one record's body so exactly it fails to plan.
  let victim := selected[0]!.name
  let corrupted := selected.map fun r =>
    if r.name == victim then { r with body := some "by\n  admit -- wrong body" } else r
  let outcome ← LeanReassemble.planEditsCollecting result corrupted .replace
  assertIO (outcome.failures.size == 1) "exactly one record failed to plan"
  assertIO (outcome.failures[0]!.1 == victim) "the corrupted record is the failure"
  assertIO (outcome.edits.size == selected.size - 1) "every other record still planned"
  -- Backoff retries the failed record as a delete, which succeeds (declaration exists).
  let retry ← LeanReassemble.planEditsCollecting result
    (corrupted.filter (·.name == victim)) .delete
  assertIO (retry.edits.size == 1 && retry.edits[0]!.replacement == "")
    "backoff re-plans the failed record as a delete"

/-- A `where`/`let rec` helper is lifted to its own theorem constant, but has no
standalone command syntax — it lives inside its parent's proof. Its record must be
classified `auxiliary` (excluded), NOT a failure: the parent's edit already governs
the text it lives in. Distinct from drift (a record that matches no constant at all),
which stays a failure. -/
private unsafe def testAuxiliaryRecords : IO Unit := do
  let root ← IO.FS.realPath "."
  let path ← IO.FS.realPath (root / "TestFixtures/AuxiliaryFixture.lean")
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let result ← Corpus.Frontend.elaborateFile importLock {
    absPath := path, module := `TestFixtures.AuxiliaryFixture
    relPath := "TestFixtures/AuxiliaryFixture.lean" }
  assertIO (!result.hasErrors) "auxiliary fixture frontend elaboration"
  let entries ← Corpus.corpusManifestCore result
    { includeInternal := false, includePrivate := false, reverseElab := false,
      reverseClosers := false, reverseSkip := #[] }
  let records := entries.map fun e =>
    Corpus.entryToRecord e result.file.relPath Corpus.TagConfig.empty
  let theorems := records.filter Corpus.Artifact.isTheoremRecord
  -- Both the parent and its lifted helper are theorem records for this file.
  let hasParent := theorems.any (·.name == "AuxiliaryFixture.parent")
  let hasHelper := theorems.any (·.name == "AuxiliaryFixture.parent.helper")
  assertIO (hasParent && hasHelper)
    "fixture should yield both the parent and its lifted where-helper as records"
  let outcome ← LeanReassemble.planEditsCollecting result theorems .replace
  -- The helper is auxiliary; the parent (and any other real theorem) plans; nothing
  -- is a failure.
  assertIO (outcome.auxiliaries.contains "AuxiliaryFixture.parent.helper")
    "the where-helper is classified auxiliary"
  assertIO (outcome.failures.isEmpty)
    "an auxiliary is not reported as a failure"
  assertIO (outcome.edits.any (·.declaration == "AuxiliaryFixture.parent"))
    "the parent theorem still plans an edit"
  -- Drift (a record naming no real constant) stays a failure, not an auxiliary.
  let bogus := { theorems[0]! with name := "AuxiliaryFixture.doesNotExist" }
  let driftOutcome ← LeanReassemble.planEditsCollecting result #[bogus] .replace
  assertIO (driftOutcome.auxiliaries.isEmpty && driftOutcome.failures.size == 1)
    "a record matching no declaration is a failure, not an auxiliary"

/-- A recursive `.simple` theorem (`:= by …`) carries its `termination_by` /
`decreasing_by` in a `Termination.suffix` SIBLING of the proof term, which
`SourceSyntax.proofRange?` excludes. Overwriting only the proof term with `by sorry`
would strand those hints on a body that is no longer recursive — the exact break the
Cedar corpus hit: an "unused termination hints" warning, then a leftover
`decreasing_by` block run against decreasing goals that no longer exist ("No goals" /
"tactic failed on all goals"). The `.replace` edit must therefore widen over the
suffix, and the rewritten file must elaborate clean. `.keep` must stay byte-identical,
suffix and all. -/
private unsafe def testTerminationSuffix : IO Unit := do
  let root ← IO.FS.realPath "."
  let path ← IO.FS.realPath (root / "TestFixtures/TerminationFixture.lean")
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let result ← Corpus.Frontend.elaborateFile importLock {
    absPath := path, module := `TestFixtures.TerminationFixture
    relPath := "TestFixtures/TerminationFixture.lean" }
  assertIO (!result.hasErrors) "termination fixture frontend elaboration"
  -- Build the records the way the extractor does, so `body` is the real proof slice.
  let entries ← Corpus.corpusManifestCore result
    { includeInternal := false, includePrivate := false, reverseElab := false,
      reverseClosers := false, reverseSkip := #[] }
  let records := (entries.map fun e =>
    Corpus.entryToRecord e result.file.relPath Corpus.TagConfig.empty).filter
    Corpus.Artifact.isTheoremRecord
  -- Both the standalone recursive theorem and EVERY member of the `mutual` block must
  -- be present as records — the mutual members are matched to their own declaration
  -- nodes, not classified auxiliary.
  for name in ["TerminationFixture.rec_le", "TerminationFixture.ping_nonneg",
               "TerminationFixture.pong_nonneg"] do
    assertIO (records.any (·.name == name)) s!"fixture yields a record for {name}"
  -- Sorry mode: one edit per theorem (no mutual member left un-holed as auxiliary),
  -- each edit's range covering that theorem's termination hints.
  let sorryEdits ← LeanReassemble.planEdits result records .replace
  assertIO (sorryEdits.size == records.size)
    "one edit per theorem, including every mutual member"
  for edit in sorryEdits do
    assertIO (edit.expected.contains "termination_by" && edit.expected.contains "decreasing_by")
      s!"the replaced range must cover the termination suffix for {edit.declaration}"
  let sorried ← LeanReassemble.applyEdits result.source sorryEdits
  assertIO (!sorried.contains "termination_by" && !sorried.contains "decreasing_by")
    "sorry-mode rewrite must leave no dangling termination hints"
  assertIO ((sorried.splitOn "sorry").length - 1 == 3)
    "sorry-mode rewrite holed all three theorems"
  -- The holed file must actually elaborate: no unused-termination-hint error, no
  -- leftover `decreasing_by` run against absent goals, and — critically for the mutual
  -- block — no "No goals to be solved" from a survivor whose group-mate was holed.
  -- (A `sorry` warning is allowed; `validateWithWorker` rejects only errors.)
  LeanReassemble.validateWithWorker result.file.absPath sorried
  -- Keep mode preserves every proof AND its hints, byte-identically.
  let keepEdits ← LeanReassemble.planEdits result records .keep
  let kept ← LeanReassemble.applyEdits result.source keepEdits
  assertIO (kept == result.source)
    "keep mode must be byte-identical over termination suffixes and a mutual block"

/-- `evalStripEdits` erases exactly the evaluation commands (`#eval`, `#eval!`,
`#reduce`, `#guard`, `#guard_msgs`) — including a `#guard_msgs` block's leading
docstring — and leaves every declaration (`def`, `theorem`) and `#check` untouched.
These are the commands that abort a `--proofs sorry` build. -/
private unsafe def testEvalStrip : IO Unit := do
  let root ← IO.FS.realPath "."
  let path ← IO.FS.realPath (root / "TestFixtures/EvalFixture.lean")
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let result ← Corpus.Frontend.elaborateFile importLock {
    absPath := path, module := `TestFixtures.EvalFixture
    relPath := "TestFixtures/EvalFixture.lean" }
  assertIO (!result.hasErrors) "eval fixture frontend elaboration"
  let edits := LeanReassemble.evalStripEdits result
  -- Five evaluation commands in the fixture: #eval, #eval!, #reduce, #guard, #guard_msgs.
  assertIO (edits.size == 5) s!"expected 5 eval-strip edits, got {edits.size}"
  for edit in edits do
    assertIO (edit.replacement == "") "eval-strip replacement is empty"
  let stripped ← LeanReassemble.applyEdits result.source edits
  -- Every evaluation command is gone (including the docstring that fed #guard_msgs).
  for token in ["#eval", "#eval!", "#reduce", "#guard", "#guard_msgs", "info: 42"] do
    assertIO (!stripped.contains token) s!"eval-strip left `{token}` behind"
  -- Declarations and #check survive: they never evaluate, so a sorry can't break them.
  assertIO (stripped.contains "def answer : Nat := 42") "eval-strip removed a definition"
  assertIO (stripped.contains "theorem answer_eq : answer = 42 := rfl")
    "eval-strip removed a theorem"
  assertIO (stripped.contains "#check answer") "eval-strip removed #check"

private def testManifestParity (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let shared := Corpus.SourceSyntax.buildSourceMap result.source result.commands
  let legacy := legacySourceMap result.source result.commands
  assertIO (sourceMapsEqual shared legacy) "source map changed during refactor"
  let sharedDecl := Corpus.SourceSyntax.buildDeclSourceMap result.source result.commands
  let legacyDecl := legacyDeclSourceMap result.source result.commands
  assertIO (declSourceMapsEqual sharedDecl legacyDecl)
    "declaration source map changed during refactor"
  -- Defaults except `includePrivate`, which the fixture relies on: it contains a
  -- `private` theorem whose manifest entry the loop below requires.
  let manifest ← Corpus.corpusManifestCore result
    { includeInternal := false, includePrivate := true, reverseElab := false,
      reverseClosers := false, reverseSkip := #[] }
  for record in records do
    let some entry := manifest.find? (·.name == record.name)
      | throw <| IO.userError s!"manifest entry missing: {record.name}"
    assertIO entry.body.isSome s!"manifest body missing: {record.name}"

private unsafe def testFailures (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  expectFailure "malformed JSONL" do
    let _ ← LeanReassemble.readRecords "TestFixtures/malformed.jsonl"
  let first := records[0]!
  expectFailure "missing file" do
    let _ ← LeanReassemble.selectTheorems #[{ first with file := none }]
      result.file.relPath
  expectFailure "duplicate record" do
    let _ ← LeanReassemble.selectTheorems #[first, first] result.file.relPath
  expectFailure "absent record" do
    let _ ← LeanReassemble.selectTheorems records "TestFixtures/Absent.lean"
  expectFailure "unmatched theorem" do
    let _ ← LeanReassemble.planEdits result #[{ first with name := "Missing.theorem" }]
  expectFailure "stale declaration location" do
    let _ ← LeanReassemble.planEdits result #[{ first with startLine := some 999 }]
  let overlapping : Array LeanReassemble.Edit := #[
    { declaration := "first", range := ⟨⟨0⟩, ⟨4⟩⟩, expected := "abcd",
      replacement := "x" },
    { declaration := "second", range := ⟨⟨3⟩, ⟨5⟩⟩, expected := "de",
      replacement := "y" }
  ]
  expectFailure "overlapping edits" do
    let _ ← LeanReassemble.applyEdits "abcdef" overlapping
  let stale : Array LeanReassemble.Edit := #[
    { declaration := "stale", range := ⟨⟨0⟩, ⟨3⟩⟩, expected := "xyz",
      replacement := "x" }
  ]
  expectFailure "stale edit source" do
    let _ ← LeanReassemble.applyEdits "abcdef" stale
  expectFailure "LSP errors" do
    LeanReassemble.validateWithWorker result.file.absPath
      "theorem invalid : True := 1\n"
  expectFailure "frontend errors" do
    LeanReassemble.rewriteFile {
      sourceRoot := "."
      records := "TestFixtures/frontend-error-records.jsonl"
      file := "TestFixtures/FrontendError.lean"
      output := "/tmp/lean-reassemble-frontend-error.lean"
    }

private def removeDirIfExists (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then
    IO.FS.removeDirAll path

private unsafe def testMaterializers : IO Unit := do
  let pid ← IO.Process.getPID
  let repoOutput : System.FilePath := s!"/tmp/lean-reassemble-materialize-repo-{pid}"
  let unitsOutput : System.FilePath := s!"/tmp/lean-reassemble-materialize-units-{pid}"
  let movedOutput : System.FilePath := s!"/tmp/lean-reassemble-materialize-moved-{pid}"
  removeDirIfExists repoOutput
  removeDirIfExists unitsOutput
  removeDirIfExists movedOutput
  let sourceRoot : System.FilePath := "TestProject"
  let records : System.FilePath := sourceRoot / "records.jsonl"
  let sourcePath := sourceRoot / "Fixture" / "Basic.lean"
  let original ← IO.FS.readFile sourcePath
  try
    LeanReassemble.materializeRepo {
      sourceRoot
      records
      output := repoOutput
    }
    let repoRoot := repoOutput / "repos" / "TestProject"
    let rewritten ← IO.FS.readFile (repoRoot / "Fixture" / "Basic.lean")
    assertIO ((rewritten.splitOn "sorry").length == 3)
      "repository replacement count"
    assertIO (← (repoRoot / ".lake" / "build" / "lib" / "lean" /
      "Fixture" / "Basic.olean").pathExists) "repository clean build"
    assertIO (← (repoRoot / "rewrite-report.json").pathExists)
      "repository rewrite report"
    -- The eval-strip pass (default under sorry) reaches the record-free `Examples`
    -- module via its second pass: its evaluation commands are gone and the report
    -- records the strip, while its imports/namespace survive.
    let examples ← IO.FS.readFile (repoRoot / "Fixture" / "Examples.lean")
    assertIO (!examples.contains "#eval" && !examples.contains "#guard")
      "eval-strip removed evaluation commands from the Examples module"
    assertIO (examples.contains "namespace Fixture.Examples")
      "eval-strip preserved the Examples module's declarations"
    let repoReport ← IO.FS.readFile (repoRoot / "rewrite-report.json")
    assertIO (repoReport.contains "\"eval_stripped\"" && repoReport.contains "Examples.lean")
      "rewrite report records the eval strip"
    expectFailure "existing materialization output" do
      LeanReassemble.materializeRepo {
        sourceRoot
        records
        output := repoOutput
      }
    LeanReassemble.materializeUnits {
      sourceRoot
      records
      output := unitsOutput
    }
    let firstTask := unitsOutput / "units" / "0-Fixture.first"
    let secondTask := unitsOutput / "units" / "1-Fixture.second"
    let firstSource ← IO.FS.readFile (firstTask / "src" / "Fixture" / "Basic.lean")
    let secondSource ← IO.FS.readFile (secondTask / "src" / "Fixture" / "Basic.lean")
    -- A unit is a task for ONE theorem: exactly its own proof is holed out, and
    -- every neighbour in the module keeps its real proof. (The whole-file rewrite
    -- `rewritten` sorries BOTH, which is right for materialize-repo and wrong here.)
    assertIO ((firstSource.splitOn "sorry").length == 2)
      "first unit holes exactly one proof"
    assertIO ((secondSource.splitOn "sorry").length == 2)
      "second unit holes exactly one proof"
    assertIO (firstSource != secondSource)
      "units for different targets must differ"
    assertIO (firstSource != rewritten && secondSource != rewritten)
      "a unit must not be the whole-file rewrite"
    -- The target is holed and the neighbour is intact, in each direction.
    assertIO (firstSource.contains "theorem second : preserved = 7 := rfl")
      "first unit preserved the neighbour's proof"
    assertIO (secondSource.contains "trivial")
      "second unit preserved the neighbour's proof"
    let taskJson ← IO.FS.readFile (firstTask / "task.json")
    assertIO (taskJson.contains "\"target\": \"Fixture.first\"")
      "unit target metadata"
    assertIO (taskJson.contains "\"command\"") "unit replay command"
    assertIO (!taskJson.contains unitsOutput.toString)
      "artifact-relative task metadata"
    let environment ← IO.FS.readFile (unitsOutput / "cache" / "environment.json")
    assertIO (environment.contains "\"cache/roots/0\"") "unit cache root"
    assertIO (!environment.contains ".work") "artifact-relative cache metadata"
    assertIO (!(← (unitsOutput / ".work").pathExists)) "temporary build removal"
    IO.FS.rename unitsOutput movedOutput
    let movedSrcRoot := movedOutput / "units" / "0-Fixture.first" / "src"
    let sysroot ← Lean.findSysroot
    let replay ← IO.Process.output {
      cmd := (sysroot / "bin" / "lean").toString
      args := #["-R", movedSrcRoot.toString,
        (movedSrcRoot / "Fixture" / "Basic.lean").toString]
      cwd := some movedOutput
      env := #[
        ("LEAN_PATH", some ((movedOutput / "cache" / "roots" / "0").toString)),
        ("LD_LIBRARY_PATH", some ((movedOutput / "cache" / "native" / "0").toString))
      ]
    }
    assertIO (replay.exitCode == 0) "moved unit replay"
    assertIO ((← IO.FS.readFile sourcePath) == original) "source tree unchanged"
    assertIO (!(← (sourceRoot / ".lake").pathExists)) "source build cache unchanged"
  finally
    removeDirIfExists repoOutput
    removeDirIfExists unitsOutput
    removeDirIfExists movedOutput

/-- End-to-end failure policy over the buildable `TestProject`. One record's body
is corrupted so it cannot plan; the whole artifact then hinges on `--on-failure`:
`fail` aborts, `skip` leaves that theorem's proof intact, `backoff` deletes it.
Each surviving artifact must still `lake build`. -/
private unsafe def testFailurePolicies : IO Unit := do
  let pid ← IO.Process.getPID
  let sourceRoot : System.FilePath := "TestProject"
  let sourcePath := sourceRoot / "Fixture" / "Basic.lean"
  let original ← IO.FS.readFile sourcePath
  -- Corrupt `Fixture.first`'s body; `Fixture.second` stays well-formed. `first` is a
  -- leaf, so deleting it keeps the project buildable.
  let records ← LeanReassemble.readRecords (sourceRoot / "records.jsonl")
  let corrupted := records.map fun r =>
    if r.name == "Fixture.first" then { r with body := some "by\n  admit" } else r
  let recordsPath : System.FilePath := s!"/tmp/lean-reassemble-badrecords-{pid}.jsonl"
  Corpus.Artifact.writeJsonl recordsPath corrupted
  let skipOut : System.FilePath := s!"/tmp/lean-reassemble-skip-{pid}"
  let backoffOut : System.FilePath := s!"/tmp/lean-reassemble-backoff-{pid}"
  let failOut : System.FilePath := s!"/tmp/lean-reassemble-failpolicy-{pid}"
  removeDirIfExists skipOut
  removeDirIfExists backoffOut
  removeDirIfExists failOut
  try
    -- `fail` (default) aborts on the corrupted record.
    expectFailure "on-failure fail aborts" do
      LeanReassemble.materializeRepo { sourceRoot, records := recordsPath, output := failOut }
    -- `skip`: `first` keeps its real proof; `second` is sorried; project builds.
    LeanReassemble.materializeRepo {
      sourceRoot, records := recordsPath, output := skipOut, onFailure := .skip }
    let skipFile ← IO.FS.readFile (skipOut / "repos" / "TestProject" / "Fixture" / "Basic.lean")
    assertIO (skipFile.contains "trivial") "skip keeps the failed theorem's real proof"
    assertIO (skipFile.contains "sorry") "skip still sorries the good theorem"
    assertIO (← (skipOut / "repos" / "TestProject" / ".lake" / "build" / "lib" / "lean" /
      "Fixture" / "Basic.olean").pathExists) "skip artifact builds"
    -- The report must NAME the skipped theorem and its reason, not just count it.
    let skipReport ← IO.FS.readFile (skipOut / "repos" / "TestProject" / "rewrite-report.json")
    assertIO (skipReport.contains "\"Fixture.first\"" && skipReport.contains "\"skipped\"")
      "skip report names the skipped theorem"
    -- `backoff`: `first` is deleted; project still builds.
    LeanReassemble.materializeRepo {
      sourceRoot, records := recordsPath, output := backoffOut, onFailure := .backoff }
    let backoffFile ← IO.FS.readFile
      (backoffOut / "repos" / "TestProject" / "Fixture" / "Basic.lean")
    assertIO (!backoffFile.contains "theorem first") "backoff deletes the failed theorem"
    assertIO (backoffFile.contains "sorry") "backoff still sorries the good theorem"
    assertIO (← (backoffOut / "repos" / "TestProject" / ".lake" / "build" / "lib" / "lean" /
      "Fixture" / "Basic.olean").pathExists) "backoff artifact builds"
    let backoffReport ← IO.FS.readFile
      (backoffOut / "repos" / "TestProject" / "rewrite-report.json")
    assertIO (backoffReport.contains "\"Fixture.first\"" && backoffReport.contains "\"failed\"")
      "backoff report names the failed theorem"
    assertIO ((← IO.FS.readFile sourcePath) == original) "source tree unchanged by policies"
  finally
    removeDirIfExists skipOut
    removeDirIfExists backoffOut
    removeDirIfExists failOut
    if ← recordsPath.pathExists then IO.FS.removeFile recordsPath

unsafe def run : IO Unit := do
  let result ← fixtureResult
  let records ← LeanReassemble.readRecords "TestFixtures/records.jsonl"
  testRewritePlan result records
  testKeepProofs result records
  testDeleteProofs result records
  testManifestOverride result records
  testCollectingFailures result records
  testAuxiliaryRecords
  testTerminationSuffix
  testEvalStrip
  testManifestParity result records
  testFailures result records
  let output := "/tmp/lean-reassemble-rewrite-test.lean"
  LeanReassemble.rewriteFile {
    sourceRoot := "."
    records := "TestFixtures/records.jsonl"
    file := result.file.relPath
    output
  }
  let actual ← IO.FS.readFile output
  let expected ← IO.FS.readFile "TestFixtures/RewriteFixture.expected.lean"
  assertIO (actual == expected) "end-to-end rewrite output"
  -- End-to-end keep mode: the written file reproduces the source exactly.
  let keepOutput := "/tmp/lean-reassemble-keep-test.lean"
  LeanReassemble.rewriteFile {
    sourceRoot := "."
    records := "TestFixtures/records.jsonl"
    file := result.file.relPath
    output := keepOutput
    proofMode := .keep
  }
  let keptFile ← IO.FS.readFile keepOutput
  let original ← IO.FS.readFile "TestFixtures/RewriteFixture.lean"
  assertIO (keptFile == original) "end-to-end keep output matches the source file"
  testMaterializers
  testFailurePolicies
  IO.println "reassemble tests passed"

end ReassembleTests

unsafe def main (args : List String) : IO UInt32 := do
  -- `materialize-repo` defaults to isolated mode, spawning `<self> --internal-rewrite-one`
  -- per file. Here `<self>` is this test binary, so it must handle that flag too — which
  -- also gives the isolated child path real coverage from `testMaterializers`.
  match args with
  | flag :: payload :: _ =>
    if flag == LeanReassemble.rewriteOneFlag then
      match (Lean.Json.parse payload >>= Lean.fromJson? (α := LeanReassemble.RewriteOneRequest)) with
      | .ok request => LeanReassemble.rewriteOneChild request; return 0
      | .error error => IO.eprintln error; return 2
  | _ => pure ()
  try
    ReassembleTests.run
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
