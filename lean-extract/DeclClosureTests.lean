import Corpus.DeclClosure
import Corpus.TestAssert

/-!
Unit tests for single-declaration extraction (`--decl`).

These cover the pure, environment-free parts of the closure machinery: the
topological order (including its cycle tolerance, which matters for mutual
blocks), record reordering, and the closure→output projection performed by
`writeTarget` — role annotation, target isolation into `target.jsonl`, the
non-owned import union, and the unresolved-member policy.

Cone computation itself (`collectPremisesFrom` under the two seeds) needs a real
`Environment`, so it is covered by the end-to-end fixture run documented in
`docs/single-decl-extraction.md` rather than here.
-/

open Lean

namespace DeclClosureTests

open Corpus Corpus.DeclClosure
open Corpus.Artifact (safeName)
open Corpus.TestAssert (assert)

/-- A minimal record; tests override only the fields they exercise. -/
private def rec (name : String) (kind : String := "theorem")
    (deps : List String := []) (imports : List String := [])
    : ConstRecord :=
  { name, kind, module := "Fix.Base", file := some "Fix/Base.lean"
    startLine := none, startCol := none, endLine := none, endCol := none
    signature := none, body := none, declSource := none, declNamespace := ""
    scopePrelude := [], fileImports := imports
    type := "True", value := none, proofScript := none, proofMethod := none
    doc := none, deps, premises := [], axioms := []
    isProtected := false, isPrivate := false, tags := [] }

private def indexOf (order : Array String) (name : String) : Nat :=
  (order.findIdx? (· == name)).getD order.size

/-- Dependencies must precede the records that use them. -/
private def testTopoOrder : IO Unit := do
  -- box <- bump <- target, declared in an order that is NOT already topological.
  let records := #[
    rec "Fix.bump_pos" (deps := ["Fix.Box.bump", "Fix.bump_val"]),
    rec "Fix.bump_val" (deps := ["Fix.Box.bump"]),
    rec "Fix.Box.bump" (kind := "def") (deps := ["Fix.Box"]),
    rec "Fix.Box" (kind := "structure")
  ]
  let order := topoOrder records
  assert (order.size == 4) s!"topoOrder dropped records: {order}"
  assert (indexOf order "Fix.Box" < indexOf order "Fix.Box.bump")
    s!"structure must precede the def using it: {order}"
  assert (indexOf order "Fix.Box.bump" < indexOf order "Fix.bump_val")
    s!"def must precede the theorem using it: {order}"
  assert (indexOf order "Fix.bump_pos" == 3)
    s!"the dependent theorem must come last: {order}"
  -- Deps pointing outside the closure are ignored, not treated as members.
  let external := #[rec "A" (deps := ["Std.something", "B"]), rec "B"]
  let order2 := topoOrder external
  assert (order2.size == 2) s!"external deps leaked into the order: {order2}"
  assert (indexOf order2 "B" < indexOf order2 "A")
    s!"closure-internal dep ignored: {order2}"

/-- A mutual block is cyclic; the order must stay total and deterministic. -/
private def testTopoCycle : IO Unit := do
  let cyclic := #[
    rec "Fix.even" (deps := ["Fix.odd"]),
    rec "Fix.odd"  (deps := ["Fix.even"])
  ]
  let order := topoOrder cyclic
  assert (order.size == 2) s!"cycle lost a record: {order}"
  assert (order.toList.eraseDups.length == 2) s!"cycle duplicated a record: {order}"
  -- Deterministic across runs: same input, same output.
  assert (topoOrder cyclic == order) "topoOrder is not deterministic for cycles"
  -- A self-loop must not hang or vanish.
  let selfLoop := #[rec "Fix.loop" (deps := ["Fix.loop"])]
  assert (topoOrder selfLoop == #["Fix.loop"]) "self-dependency mishandled"

/-- `applyOrder` follows the given order and never drops a record. -/
private def testApplyOrder : IO Unit := do
  let records := #[rec "A", rec "B", rec "C"]
  let ordered := applyOrder records #["C", "A", "B"]
  assert (ordered.map (·.name) == #["C", "A", "B"]) "applyOrder ignored the order"
  -- Names absent from the order are appended, not lost.
  let partial_ := applyOrder records #["B"]
  assert (partial_.size == 3) "applyOrder dropped unordered records"
  assert (partial_[0]!.name == "B") "applyOrder mislaid the ordered prefix"
  -- An order naming an unknown record must not fabricate one.
  let unknown := applyOrder records #["Z", "A", "B", "C"]
  assert (unknown.map (·.name) == #["A", "B", "C"]) "applyOrder invented a record"

private def target (display : String) : Target :=
  { requested := display.toName, resolved := display.toName
    display := display.toName, module := `Fix.Base }

private def closureOf (targetName : String) (members : List (String × Role))
    (drops : List (String × DropReason) := []) : Closure :=
  let roles := members.foldl (init := ({} : Std.HashMap String Role))
    (fun m (n, r) => m.insert n r)
  let dropReasons := drops.foldl (init := ({} : Std.HashMap String DropReason))
    (fun m (n, r) => m.insert n r)
  { target := target targetName
    roles := roles.insert targetName .target
    privateMap := #[], modules := #[`Fix.Base], dropReasons }

/-- A config carrying only what the projection and metadata read; the driver-only
fields (paths, jobs, timeouts) are irrelevant here. -/
private def writeOpts : RunConfig :=
  { targets := #[`Fix.bump_pos], projectRoot := ".", outDir := "."
    roots := #[`Fix], tagConfig := Corpus.TagConfig.empty, configPath? := none
    opts := { includeInternal := false, includePrivate := true
              reverseElab := false, reverseClosers := false, reverseSkip := #[] }
    reverseTimeoutMs := 0, jobs := 1, isolateFiles := true, resume := false
    strictClosure := false, toolVersion := "test" }

/-- The record pool a closure projects out of. `Fix.unrelated` is deliberately
present and out of closure; `Fix.Base` is an owned import that must be filtered
out of the import union while non-owned `Init` survives. -/
private def samplePool : Array ConstRecord := #[
  rec "Fix.bump_pos" (deps := ["Fix.Box.bump", "Fix.bump_val"])
    (imports := ["Init", "Fix.Base"]),
  rec "Fix.bump_val" (deps := ["Fix.Box.bump"]) (imports := ["Init"]),
  rec "Fix.Box.bump" (kind := "def") (deps := ["Fix.Box"]) (imports := ["Init"]),
  rec "Fix.Box" (kind := "structure") (imports := ["Init"]),
  rec "Fix.unrelated" (imports := ["Init"])
]

private def sampleClosure : Closure :=
  closureOf "Fix.bump_pos"
    [("Fix.Box", .statement), ("Fix.Box.bump", .statement), ("Fix.bump_val", .proof)]

private def roleOf (p : Projection) (name : String) : Option String :=
  (p.ordered.find? (·.name == name)).bind (·.closureRole)

/-- Selection, role annotation, ordering, and the import union — asserted on the
pure projection rather than through the filesystem. -/
private def testProjectClosure : IO Unit := do
  let p ← projectClosure sampleClosure samplePool writeOpts
  assert (p.ordered.size == 4) s!"expected 4 selected records, got {p.ordered.size}"
  assert (!p.ordered.any (·.name == "Fix.unrelated"))
    "a record outside the closure was selected"
  assert p.unresolved.isEmpty s!"unexpected unresolved: {p.unresolved}"
  -- Roles, including the target's own.
  assert (roleOf p "Fix.Box" == some "statement") "Box should be statement"
  assert (roleOf p "Fix.Box.bump" == some "statement") "Box.bump should be statement"
  assert (roleOf p "Fix.bump_val" == some "proof") "bump_val should be proof"
  assert (roleOf p "Fix.bump_pos" == some "target") "bump_pos should be target"
  -- Config split, each ordered dependencies-first.
  assert (p.theorems.map (·.name) == #["Fix.bump_val", "Fix.bump_pos"])
    s!"theorems out of dependency order: {p.theorems.map (·.name)}"
  assert (p.definitions.map (·.name) == #["Fix.Box", "Fix.Box.bump"])
    s!"definitions out of dependency order: {p.definitions.map (·.name)}"
  -- target.jsonl content: the target ALONE. A premise leaking in here would
  -- silently hole out a premise proof in the assembled unit.
  assert (p.target.size == 1) s!"target must be exactly one record, got {p.target.size}"
  assert (p.target[0]!.name == "Fix.bump_pos") "wrong record selected as target"
  -- Only non-owned imports survive.
  assert (p.imports == #["Init"])
    s!"import union should keep only non-owned modules, got {p.imports}"

/-- Metadata is derived from the projection, not recomputed. -/
private def testRenderMetadata : IO Unit := do
  let p ← projectClosure sampleClosure samplePool writeOpts
  let json := renderMetadata sampleClosure p writeOpts p.target[0]!
    #["Fix/Base.lean"] #[]
  let getStr (key : String) : IO String := do
    IO.ofExcept (json.getObjVal? key >>= Json.getStr?)
  assert ((← getStr "target") == "Fix.bump_pos") "metadata target wrong"
  assert ((← getStr "mode") == "decl-closure") "metadata mode wrong"
  assert ((← getStr "targetKind") == "theorem") "metadata targetKind wrong"
  let order ← IO.ofExcept (json.getObjVal? "assemblyOrder" >>= Json.getArr?)
  assert (order.size == 4) s!"assemblyOrder should span both configs: {order.size}"
  let counts ← IO.ofExcept (json.getObjVal? "closureCounts")
  assert ((counts.getObjVal? "statement").toOption == some (Json.num 2))
    "closureCounts.statement wrong"
  assert ((counts.getObjVal? "proof").toOption == some (Json.num 1))
    "closureCounts.proof wrong"
  assert ((counts.getObjVal? "target").toOption == some (Json.num 1))
    "closureCounts.target wrong"

/-- The writer lays down the expected layout and re-readable JSONL. -/
private def testWriteTarget (root : System.FilePath) : IO Unit := do
  let (targetDir, p) ← writeTarget (root / "out") sampleClosure samplePool writeOpts
    #["Fix/Base.lean"] #[]
  assert (p.theorems.size == 2) s!"expected 2 theorems, got {p.theorems.size}"
  assert (p.definitions.size == 2) s!"expected 2 definitions, got {p.definitions.size}"
  let dataDir := targetDir / "data"
  for name in ["definitions.jsonl", "target.jsonl"] do
    assert (← (dataDir / name).pathExists) s!"missing {name}"
  assert (← (dataDir / "theorems" / "train.jsonl").pathExists) "missing theorems/train.jsonl"
  assert (← (targetDir / "metadata.json").pathExists) "missing metadata.json"
  -- Round-trip through the shared reader the reassembler uses, so the artifact is
  -- consumable by `materialize-units` as written.
  let targetRecords ← Corpus.Artifact.readJsonl (α := ConstRecord) (dataDir / "target.jsonl")
  assert (targetRecords.size == 1)
    s!"target.jsonl must hold one record, got {targetRecords.size}"
  assert (targetRecords[0]!.name == "Fix.bump_pos") "target.jsonl holds the wrong record"
  assert (targetRecords[0]!.closureRole == some "target") "target role lost in round-trip"

/-- Closure members with no record are reported, and `--strict-closure` escalates.
An absent TARGET is always fatal. -/
private def testUnresolved : IO Unit := do
  let closure := closureOf "Fix.thm" [("Fix.Box.mk", .statement)]
    [("Fix.Box.mk", "constructor")]
  let pool := #[rec "Fix.thm"]
  -- Lenient: warn and continue.
  let p ← projectClosure closure pool writeOpts
  assert (p.unresolved == #["Fix.Box.mk"])
    s!"unresolved member not reported: {p.unresolved}"
  assert (p.ordered.size == 1) "lenient mode dropped the target"
  -- Classified into its category, not lumped into a raw list.
  assert (p.dropped.size == 1) s!"expected one drop category, got {p.dropped.size}"
  assert (p.dropped[0]!.1 == "constructor") "drop category misclassified"
  assert (p.dropped[0]!.2.1 == 1) "drop count wrong"
  -- Strict: fail.
  let failed ← try
    let _ ← projectClosure closure pool { writeOpts with strictClosure := true }
    pure false
  catch _ => pure true
  assert failed "--strict-closure accepted an unresolved closure member"
  -- A missing target is fatal regardless of strictness: a closure without its
  -- target cannot be materialized.
  let targetMissing ← try
    let _ ← projectClosure (closureOf "Fix.absent" [("Fix.thm", .proof)]) pool writeOpts
    pure false
  catch _ => pure true
  assert targetMissing "a closure whose target produced no record was accepted"

/-- Drops are grouped by reason, `unexplained` first, and rendered into
`dropped.json` with counts that account for every unresolved member. -/
private def testDropClassification : IO Unit := do
  -- A member with no recorded reason must surface as `unexplained` — the case
  -- that means a record we expected went missing.
  let closure := closureOf "Fix.thm"
    [("Fix.Box.mk", .statement), ("Fix.Box.rec", .proof),
     ("Fix.gen._proof_1", .proof), ("Fix.missing", .proof)]
    [("Fix.Box.mk", "constructor"), ("Fix.Box.rec", "recursor"),
     ("Fix.gen._proof_1", "generated")]
  let p ← projectClosure closure #[rec "Fix.thm"] writeOpts
  assert (p.unresolved.size == 4) s!"expected 4 unresolved, got {p.unresolved.size}"
  -- `unexplained` sorts first so it cannot be missed in the summary line.
  assert (p.dropped[0]!.1 == unexplainedDrop)
    s!"unexplained must sort first, got {p.dropped[0]!.1}"
  assert (p.dropped[0]!.2.2 == #["Fix.missing"]) "wrong member marked unexplained"
  -- Every unresolved member lands in exactly one category.
  let total := p.dropped.foldl (fun acc (_, n, _) => acc + n) 0
  assert (total == p.unresolved.size)
    s!"category counts {total} do not account for {p.unresolved.size} members"
  assert (p.dropped.size == 4) s!"expected 4 categories, got {p.dropped.size}"
  -- dropped.json shape.
  let json := renderDropped p
  let getNat (key : String) : IO Nat := do
    IO.ofExcept (json.getObjVal? key >>= Json.getNat?)
  assert ((← getNat "total") == 4) "dropped.json total wrong"
  let cats ← IO.ofExcept (json.getObjVal? "categories" >>= Json.getArr?)
  assert (cats.size == 4) s!"dropped.json should list 4 categories, got {cats.size}"
  let firstReason ← IO.ofExcept ((cats[0]!).getObjVal? "reason" >>= Json.getStr?)
  assert (firstReason == "unexplained") "dropped.json should list unexplained first"

/-- Two modules emitting the same record name make selection ambiguous. -/
private def testAmbiguousPool : IO Unit := do
  let closure := closureOf "Fix.thm" [("Fix.dup", .proof)]
  let pool := #[
    rec "Fix.thm",
    rec "Fix.dup",
    { rec "Fix.dup" with module := "Fix.Other" }
  ]
  let failed ← try
    let _ ← projectClosure closure pool writeOpts
    pure false
  catch _ => pure true
  assert failed "a record-name collision across modules was accepted"
  -- The same name from the SAME module is just the pool being deduped, not a
  -- conflict: it must be accepted.
  let sameModule := #[rec "Fix.thm", rec "Fix.dup", rec "Fix.dup"]
  let p ← projectClosure closure sameModule writeOpts
  assert (p.ordered.size == 2) s!"same-module duplicate rejected: {p.ordered.size}"

/-- Directory names must be filesystem-safe while metadata keeps the true name.
Shared with the reassembler's unit task ids, so both artifacts correspond. -/
private def testSafeName : IO Unit := do
  assert (safeName "Fix.bump_pos" == "Fix.bump_pos") "safeName mangled a plain name"
  assert (safeName "Fix.«odd name»" == "Fix._odd_name_") "safeName left unsafe chars"
  assert (safeName "A/B" == "A_B") "safeName left a path separator"

def run : IO UInt32 := do
  testTopoOrder
  testTopoCycle
  testApplyOrder
  testSafeName
  testProjectClosure
  testRenderMetadata
  testUnresolved
  testDropClassification
  testAmbiguousPool
  IO.FS.withTempDir fun root => do
    testWriteTarget root
  IO.println "decl closure tests passed"
  return (0 : UInt32)

end DeclClosureTests

def main : IO UInt32 :=
  DeclClosureTests.run
