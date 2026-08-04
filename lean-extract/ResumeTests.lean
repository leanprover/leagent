import Corpus.WorkerExtract
import Corpus.TestAssert

open Lean

namespace ResumeTests

open Corpus.TestAssert (assert)

private def writeProject (root : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (root / "A")
  IO.FS.createDirAll (root / "A__B")
  IO.FS.writeFile (root / "lakefile.lean") "import Lake\nopen Lake DSL\npackage ResumeFixture\n"
  IO.FS.writeFile (root / "lean-toolchain") "leanprover/lean4:v4.31.0\n"
  IO.FS.writeFile (root / "A" / "B__C.lean") "theorem left : True := by trivial\n"
  IO.FS.writeFile (root / "A__B" / "C.lean") "theorem right : True := by trivial\n"

private def testShardPaths (root : System.FilePath) : IO Unit := do
  let shards := root / ".shards"
  let left : Corpus.Discover.DiscoveredFile := {
    absPath := root / "A" / "B__C.lean"
    module := `A.B__C
    relPath := "A/B__C.lean"
  }
  let right : Corpus.Discover.DiscoveredFile := {
    absPath := root / "A__B" / "C.lean"
    module := `A__B.C
    relPath := "A__B/C.lean"
  }
  assert (Corpus.Resume.shardPath shards left != Corpus.Resume.shardPath shards right)
    "distinct relative paths produced the same shard path"
  let sourceHash ← Lake.computeFileHash left.absPath
  Corpus.Resume.writeShard shards left sourceHash #[]
  let some records ← Corpus.Resume.readValidShard shards left sourceHash
    | throw <| IO.userError "fresh shard was not reusable"
  assert records.isEmpty "empty shard decoded with records"
  IO.FS.writeFile (Corpus.Resume.shardPath shards left) "{not-json}\n"
  let corrupt ← Corpus.Resume.readValidShard shards left sourceHash
  assert corrupt.isNone "corrupt shard was reused"
  Corpus.Resume.writeShard shards left sourceHash #[]
  IO.FS.writeFile left.absPath "theorem left : False := by contradiction\n"
  let changedHash ← Lake.computeFileHash left.absPath
  let stale ← Corpus.Resume.readValidShard shards left changedHash
  assert stale.isNone "shard was reused after its source content changed"

/-- The collector options these tests fingerprint against. The fingerprint must
vary with the tag config, the reverse timeout, and project source content, none of
which live in here — so one fixed bundle is enough, and holding it constant is
what makes those three assertions meaningful. -/
private def testOpts : Corpus.CollectOptions :=
  { includeInternal := false, includePrivate := true, reverseElab := false,
    reverseClosers := false, reverseSkip := #[] }

private def testFingerprint (root : System.FilePath) : IO Unit := do
  let config := root / "tags.json"
  IO.FS.writeFile config "{\"rules\":[]}\n"
  let fp1 ← Corpus.Resume.runFingerprint root (some config) testOpts 300000
  IO.FS.writeFile config "{\"rules\":[{\"match\":\"A\",\"tags\":{\"set\":\"new\"}}]}\n"
  let fp2 ← Corpus.Resume.runFingerprint root (some config) testOpts 300000
  assert (fp1 != fp2) "tag config content did not affect the resume fingerprint"
  let outDir := root / "out"
  let shardsDir ← Corpus.Resume.prepareShardsDir outDir false fp1
  let marker := shardsDir / "marker"
  IO.FS.writeFile marker "keep"
  let _ ← Corpus.Resume.prepareShardsDir outDir true fp1
  assert (← marker.pathExists) "matching fingerprint discarded staged shards"
  let _ ← Corpus.Resume.prepareShardsDir outDir true fp2
  assert (!(← marker.pathExists)) "changed fingerprint retained staged shards"
  let fp3 ← Corpus.Resume.runFingerprint root (some config) testOpts 1000
  assert (fp2 != fp3) "reverse timeout did not affect the resume fingerprint"
  Corpus.Resume.checkRunFingerprint root (some config) testOpts 1000 fp3
  IO.FS.writeFile (root / "A__B" / "C.lean") "theorem changed : True := by trivial\n"
  let fp4 ← Corpus.Resume.runFingerprint root (some config) testOpts 1000
  assert (fp3 != fp4) "project source content did not affect the resume fingerprint"
  let rejected ← try
    Corpus.Resume.checkRunFingerprint root (some config) testOpts 1000 fp3
    pure false
  catch _ =>
    pure true
  assert rejected "changed run inputs passed the final fingerprint check"

private unsafe def testFrontendErrors (root : System.FilePath) : IO Unit := do
  let path := root / "Bad.lean"
  IO.FS.writeFile path "theorem broken : True := by\n  exact missing\n"
  let df : Corpus.Discover.DiscoveredFile := {
    absPath := path
    module := `Bad
    relPath := "Bad.lean"
  }
  let rejected ← try
    let _ ← Corpus.extractOneFileViaFrontend df Corpus.TagConfig.empty testOpts
    pure false
  catch _ =>
    pure true
  assert rejected "a file with Lean errors was accepted for shard publication"

unsafe def run : IO UInt32 := do
  IO.FS.withTempDir fun root => do
    writeProject root
    testShardPaths root
    testFingerprint root
    testFrontendErrors root
    IO.println "resume tests passed"
    return (0 : UInt32)

end ResumeTests

unsafe def main : IO UInt32 :=
  ResumeTests.run
