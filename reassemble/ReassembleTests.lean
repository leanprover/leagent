import LeanReassemble
import Corpus.CorpusManifest

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

private def testManifestParity (result : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO Unit := do
  let shared := Corpus.SourceSyntax.buildSourceMap result.source result.commands
  let legacy := legacySourceMap result.source result.commands
  assertIO (sourceMapsEqual shared legacy) "source map changed during refactor"
  let sharedDecl := Corpus.SourceSyntax.buildDeclSourceMap result.source result.commands
  let legacyDecl := legacyDeclSourceMap result.source result.commands
  assertIO (declSourceMapsEqual sharedDecl legacyDecl)
    "declaration source map changed during refactor"
  let manifest ← Corpus.corpusManifestCore result false true false false
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
    { declaration := "first", range := ⟨⟨0⟩, ⟨4⟩⟩, replacement := "x" },
    { declaration := "second", range := ⟨⟨3⟩, ⟨5⟩⟩, replacement := "y" }
  ]
  expectFailure "overlapping edits" do
    let _ ← LeanReassemble.applyEdits "abcdef" overlapping
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

unsafe def run : IO Unit := do
  let result ← fixtureResult
  let records ← LeanReassemble.readRecords "TestFixtures/records.jsonl"
  testRewritePlan result records
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
  IO.println "reassemble tests passed"

end ReassembleTests

unsafe def main : IO UInt32 := do
  try
    ReassembleTests.run
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
