/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Corpus.Records

/-!
`Corpus.Artifact` — the shared conventions for reading and writing corpus
artifacts on disk.

These are small, but each one is a CONTRACT between the extractor and its
consumers (the corpus writer, single-declaration extraction, and the
`reassemble` package). Keeping one implementation of each is what stops the two
sides of the pipeline from drifting:

  * `writeJsonl` / `parseJsonl` — the JSONL line format.
  * `partitionByConfig` — which records belong to the `theorems` config versus
    the `definitions` config. Both writers must agree, or a record silently
    changes config between modes.
  * `safeName` — how a declaration name becomes a filesystem path component.
    The extractor names a `--decl` output directory with it and the reassembler
    names a unit task id with it; if they diverge, the two artifacts stop
    corresponding.
-/

namespace Corpus.Artifact

open Lean

/-- Write JSON-serializable records as JSONL, one compact object per line.
Truncates any existing file. -/
def writeJsonl [ToJson α] (path : System.FilePath) (records : Array α) : IO Unit := do
  IO.FS.writeFile path ""
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for r in records do
    h.putStrLn (toJson r).compress
  h.flush

/-- Decode one JSON object per nonempty line. Errors name the 1-based line. -/
def parseJsonl [FromJson α] (content : String) : Except String (Array α) := do
  let mut out : Array α := #[]
  let mut lineNumber := 0
  for line in content.splitOn "\n" do
    lineNumber := lineNumber + 1
    let line := line.trimAscii.toString
    unless line.isEmpty do
      let json ← (Json.parse line).mapError
        (fun e => s!"malformed JSONL at line {lineNumber}: {e}")
      let value ← (fromJson? json : Except String α).mapError
        (fun e => s!"invalid record at line {lineNumber}: {e}")
      out := out.push value
  return out

/-- Read and decode a JSONL file. -/
def readJsonl [FromJson α] (path : System.FilePath) : IO (Array α) := do
  match parseJsonl (α := α) (← IO.FS.readFile path) with
  | .ok values => return values
  | .error e   => throw <| IO.userError s!"{path}: {e}"

/-- True iff a record belongs to the `theorems` config. The kind carries an
optional `private ` prefix, so this is a suffix test. -/
def isTheoremRecord (r : ConstRecord) : Bool :=
  r.kind.endsWith "theorem"

/-- Partition records into `(theorems, definitions)`. Order within each bucket
follows the input, so a caller that pre-sorted its records keeps that order. -/
def partitionByConfig (rs : Array ConstRecord) :
    Array ConstRecord × Array ConstRecord :=
  rs.foldl (init := (#[], #[])) fun (thms, defs) r =>
    if isTheoremRecord r then (thms.push r, defs) else (thms, defs.push r)

/-- Sanitize a declaration name into a single filesystem path component.

Used for BOTH the extractor's `--decl` output directory and the reassembler's
unit task id, so the two artifacts correspond by construction. Metadata always
carries the true, unsanitized name; this only has to be filesystem-safe. -/
def safeName (name : String) : String :=
  name.map fun char =>
    if char.isAlphanum || char == '.' || char == '_' || char == '-' then char else '_'

end Corpus.Artifact
