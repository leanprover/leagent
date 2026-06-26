import Lean

/-!
Orphan-safe file discovery for the worker-driven extraction path.

The import-based extractor (`Corpus.Extract`) only ever sees declarations in the
transitive import closure of the `--modules` roots, so a `.lean` file that no
imported module pulls in ("orphan") is invisible. The worker path drives one
`lean --worker` per *source file*, so it must enumerate files from what is ON
DISK under the project's library roots — NOT the import graph.

We enumerate every `.lean` file beneath the project root (hard-excluding any
`.lake/` build directory), keep those whose derived module name sits under one
of the declared library roots, and convert each path to its module `Name`. A
`--list-orphans` diagnostic reports the modules on disk that are not in the
import closure of the declared roots.
-/

namespace Corpus.Discover

open Lean System

/-- Every `.lean` file beneath `root`, with any `.lake/` subtree pruned (we never
descend into build output). Uses `walkDir`'s `enter` predicate so the prune
happens during traversal, not after. -/
def enumerateLeanFiles (root : FilePath) : IO (Array FilePath) := do
  let all ← root.walkDir (enter := fun p => pure (p.fileName != some ".lake"))
  return all.filter (fun p => p.extension == some "lean")

/-- Convert a `.lean` file path to its module `Name`, relative to `projectRoot`.
`projectRoot/LeanSQLite/Journal/Program.lean` → `LeanSQLite.Journal.Program`.
Returns `none` if the path is not under `projectRoot` or is not a `.lean` file.
The top-level `projectRoot/LeanSQLite.lean` maps to the single-component
`LeanSQLite`. -/
def filePathToModule (projectRoot : FilePath) (file : FilePath) : Option Name := do
  let rootStr := projectRoot.toString
  let fileStr := file.toString
  -- Strip the project-root prefix and the leading separator.
  let rel0 := (fileStr.dropPrefix rootStr).copy
  let rel := ((rel0.dropPrefix "/").copy.dropPrefix "\\").copy
  guard (rel.endsWith ".lean")
  let noExt := (rel.dropEnd 5).copy  -- ".lean"
  -- Path separators (POSIX `/`, Windows `\`) → name dots.
  let parts := (noExt.splitOn "/").flatMap (·.splitOn "\\")
  let comps := parts.filter (!·.isEmpty)
  match comps with
  | []      => none
  | c :: cs => some (cs.foldl (fun n s => Name.mkStr n s) (Name.mkStr Name.anonymous c))

/-- A discovered source file: its absolute path, module `Name`, and the path
relative to the project root (the form the corpus `file` field stores, e.g.
`LeanSQLite/Btree/Helpers.lean`). -/
structure DiscoveredFile where
  absPath : FilePath
  module  : Name
  relPath : String
  deriving Inhabited

/-- Discover the source files of the project at `projectRoot` whose module name
falls under one of `libRoots` (e.g. `#[`LeanSQLite]`). Results are sorted by
`relPath` for deterministic output. If `libRoots` is empty, every discovered
`.lean` module is kept (caller passes the `--modules` roots). -/
def discoverFiles (projectRoot : FilePath) (libRoots : Array Name)
    : IO (Array DiscoveredFile) := do
  let root ← IO.FS.realPath projectRoot
  let files ← enumerateLeanFiles root
  let mut out : Array DiscoveredFile := #[]
  for f in files do
    let abs ← IO.FS.realPath f
    let some mod := filePathToModule root abs | continue
    let underRoot := libRoots.isEmpty ||
      libRoots.any (fun r => r == mod || r.isPrefixOf mod)
    if underRoot then
      let relPath := ((abs.toString.dropPrefix root.toString).copy.dropPrefix "/").copy
      out := out.push { absPath := abs, module := mod, relPath }
  return out.qsort (fun a b => a.relPath < b.relPath)

/-- Orphans = discovered modules on disk that are NOT in `importClosure` (the set
of modules transitively imported by the declared roots). Sorted. -/
def findOrphans (discovered : Array Name) (importClosure : Array Name) : Array Name :=
  let closure : Std.HashSet Name := importClosure.foldl (·.insert ·) {}
  (discovered.filter (!closure.contains ·)).qsort (·.toString < ·.toString)

end Corpus.Discover
