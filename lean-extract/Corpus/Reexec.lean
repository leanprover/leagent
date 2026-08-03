/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
`Corpus.Reexec` — re-exec the running tool under `lake env`.

Both CLIs (`corpus-extract` and `lean-reassemble`) need the same trick: when the
`--source-root` is a Lake project, re-exec the process under `lake env` from inside
that project so `LEAN_PATH` resolves to its built `.oleans`. A marker env var breaks
the loop on the second pass. This is the one implementation of that, shared so the
path-absolutization parity fix below lives in exactly one place.
-/

namespace Corpus.Reexec

/-- Resolve a path against `base` if it isn't already absolute. -/
def absolutize (base : System.FilePath) (p : System.FilePath) : System.FilePath :=
  if p.isAbsolute then p else base / p

/-- True if `dir` looks like a Lake project root (has a `lakefile.lean`
or `lakefile.toml`). -/
def isLakeProject (dir : System.FilePath) : IO Bool := do
  pure ((← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists))

/-- Re-exec ourselves under `lake env` from inside `project`, with relative user
paths absolutized against the original cwd. `marker` is set in the child's env so
the caller can detect the second pass; `pathFlags` names the flags whose values are
filesystem paths. Returns the child's exit code.

The arg walk advances ONE token at a time, consuming a value only for a flag known
to take one. An earlier version stepped in pairs, which silently broke parity after
any bare flag (`--no-private`, `--reverse-elab`, …): a following `--output out` was
then read as a (value, flag) pair, so `out` was never absolutized and the run wrote
into the source tree instead of the cwd. -/
unsafe def reexecUnderLake (marker : String) (pathFlags : List String)
    (project : System.FilePath) (rawArgs : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let self ← IO.appPath
  let projectAbs := absolutize cwd project
  let rec rebuild : List String → List String
    | [] => []
    | f :: v :: xs =>
      if pathFlags.contains f then
        f :: (absolutize cwd v).toString :: rebuild xs
      else
        f :: rebuild (v :: xs)
    | [x] => [x]
  let child ← IO.Process.spawn {
    cmd  := "lake"
    args := #["env", self.toString] ++ (rebuild rawArgs).toArray
    cwd  := some projectAbs
    env  := #[(marker, some "1")]
  }
  child.wait

end Corpus.Reexec
