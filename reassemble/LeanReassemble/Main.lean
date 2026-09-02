import LeanReassemble
import Corpus.Reexec

namespace LeanReassemble

open Lean (Json fromJson?)

private def usage : String := "\
Usage:
  lean_reassemble rewrite-file --source-root <lake-project>
    --records <declarations.jsonl> --file <relative.lean>
    --output <rewritten.lean> [--proofs sorry|keep|delete]

  lean_reassemble materialize-repo --source-root <lake-project>
    --records <declarations.jsonl> --output <artifact-dir>
    [--build-target <target>] [--proofs sorry|keep|delete] [--keep-eval]

  lean_reassemble materialize-units --source-root <lake-project>
    --records <declarations.jsonl> --output <artifact-dir>
    [--build-target <target>] [--proofs sorry|keep|delete]
    [--manifest <manifest.json>] [--on-failure fail|skip|backoff]

--proofs sorry (default) replaces each selected theorem's proof with `by sorry`.
--proofs keep preserves the proofs verbatim, producing the compilable REFERENCE
state of the same records: every record is still matched to its declaration and
its proof range validated, so the artifact is evidence that the extraction agrees
with the source. Use it to get an intermediate, fully-compiling checkout from an
extractor run, or as the oracle to diff a sorried artifact against.
--proofs delete erases each selected declaration outright. materialize-repo and
materialize-units check the records' `deps` BEFORE building and fail — naming each
`dependent -> deleted` pair — when a surviving declaration would be left referencing
a deleted theorem, rather than deferring to an opaque build break. (A --proofs sorry
dependent is safe: its proof, and the references in it, are holed out. Deletes
introduced by --on-failure backoff are not covered by this pre-flight and still
surface at the final build.)

--manifest <path> is a sparse per-theorem override: a JSON object mapping theorem
names to keep|sorry|delete. Theorems it does not name follow --proofs.

In materialize-units the manifest does double duty: the action on a UNIT'S TARGET
theorem selects whether that unit is emitted (sorry -> hole and emit; keep/delete ->
excluded), while a `delete` on a SAME-MODULE neighbour removes that neighbour from
the emitted unit's file. A run that emits no task at all (e.g. a whole-run
--proofs delete or keep) is an error, not an empty success. --build-target in
materialize-units scopes only the pristine warm-up build that fills the shared
cache, not the per-unit builds.

--on-failure fail (default) aborts on the first theorem that fails to reassemble.
skip omits it (recorded as skipped); backoff deletes it (recorded as failed) and
continues. Both recover from PLANNING failures; a post-rewrite build break in
materialize-repo still aborts, since it usually points at a dependent rather than
the holed theorem. Under skip/backoff the run's report NAMES each skipped/failed
theorem and its reason, not just a count.

--keep-eval (materialize-repo only) preserves #eval/#eval!/#reduce/#guard/#guard_msgs
commands verbatim. By default, once the run holes or deletes any proof, those
commands are stripped from the reassembled tree: Lean refuses to evaluate an
expression that transitively depends on `sorry`, so a #eval reaching a holed proof
would otherwise fail the build. Stripping erases only the evaluation commands (a
#guard_msgs block with its docstring included); every theorem and definition is
kept and still holed. A pure --proofs keep run holes nothing, so it never strips."

private def requireArg (name : String) : Option String → Except String String
  | some value => .ok value
  | none => .error s!"{name} is required"

private inductive Command where
  | rewriteFile (config : RewriteConfig)
  | materializeRepo (config : MaterializeConfig)
  | materializeUnits (config : MaterializeConfig)

private def Command.sourceRoot : Command → System.FilePath
  | .rewriteFile config => config.sourceRoot
  | .materializeRepo config => config.sourceRoot
  | .materializeUnits config => config.sourceRoot

private def Command.requiresManifest : Command → Bool
  | .rewriteFile _ => false
  | .materializeRepo _ | .materializeUnits _ => true

/-- Parse `--proofs sorry|keep|delete`. -/
private def parseProofMode : String → Except String ProofMode
  | "sorry"  => .ok .replace
  | "keep"   => .ok .keep
  | "delete" => .ok .delete
  | value    => .error s!"--proofs expects sorry|keep|delete, got: {value}"

/-- Parse `--on-failure fail|skip|backoff`. -/
private def parseFailurePolicy : String → Except String FailurePolicy
  | "fail"    => .ok .fail
  | "skip"    => .ok .skip
  | "backoff" => .ok .backoff
  | value     => .error s!"--on-failure expects fail|skip|backoff, got: {value}"

private def parseRewriteArgs (args : List String) : Except String RewriteConfig := do
  let rec go (remaining : List String) (sourceRoot records output : Option String)
      (file manifest : Option String) (mode : ProofMode) (onFailure : FailurePolicy)
      : Except String RewriteConfig :=
    match remaining with
    | [] => return {
        sourceRoot := ← requireArg "--source-root" sourceRoot
        records := ← requireArg "--records" records
        file := ← requireArg "--file" file
        output := ← requireArg "--output" output
        proofMode := mode
        manifestPath := manifest.map System.FilePath.mk
        onFailure
      }
    | "--source-root" :: value :: tail => go tail (some value) records output file manifest mode onFailure
    | "--records" :: value :: tail => go tail sourceRoot (some value) output file manifest mode onFailure
    | "--file" :: value :: tail => go tail sourceRoot records output (some value) manifest mode onFailure
    | "--output" :: value :: tail => go tail sourceRoot records (some value) file manifest mode onFailure
    | "--manifest" :: value :: tail => go tail sourceRoot records output file (some value) mode onFailure
    | "--proofs" :: value :: tail => do
        go tail sourceRoot records output file manifest (← parseProofMode value) onFailure
    | "--on-failure" :: value :: tail => do
        go tail sourceRoot records output file manifest mode (← parseFailurePolicy value)
    | flag :: _ => throw s!"unknown or incomplete argument: {flag}"
  go args none none none none none .replace .fail

/-- Parse the shared `materialize-{repo,units}` arguments. `allowRepoFlags` gates the
two flags that only `materialize-repo` honors: `--keep-eval` (eval-strip opt-out) and
`--in-process` (isolation off). Both are inert in units mode — a unit is a single
standalone module with its own build model — so they are rejected there as unknown
arguments rather than silently accepted. -/
private def parseMaterializeArgs (allowRepoFlags : Bool) (args : List String)
    : Except String MaterializeConfig := do
  let rec go (remaining : List String) (sourceRoot records output buildTarget : Option String)
      (manifest : Option String) (mode : ProofMode) (onFailure : FailurePolicy)
      (keepEval : Bool) (isolated : Bool)
      : Except String MaterializeConfig :=
    match remaining with
    | [] => return {
        sourceRoot := ← requireArg "--source-root" sourceRoot
        records := ← requireArg "--records" records
        output := ← requireArg "--output" output
        buildTarget
        proofMode := mode
        manifestPath := manifest.map System.FilePath.mk
        onFailure
        keepEval
        isolated
      }
    | "--source-root" :: value :: tail =>
        go tail (some value) records output buildTarget manifest mode onFailure keepEval isolated
    | "--records" :: value :: tail =>
        go tail sourceRoot (some value) output buildTarget manifest mode onFailure keepEval isolated
    | "--output" :: value :: tail =>
        go tail sourceRoot records (some value) buildTarget manifest mode onFailure keepEval isolated
    | "--build-target" :: value :: tail =>
        go tail sourceRoot records output (some value) manifest mode onFailure keepEval isolated
    | "--manifest" :: value :: tail =>
        go tail sourceRoot records output buildTarget (some value) mode onFailure keepEval isolated
    | "--proofs" :: value :: tail => do
        go tail sourceRoot records output buildTarget manifest (← parseProofMode value) onFailure keepEval isolated
    | "--on-failure" :: value :: tail => do
        go tail sourceRoot records output buildTarget manifest mode (← parseFailurePolicy value) keepEval isolated
    | "--keep-eval" :: tail =>
        if allowRepoFlags then
          go tail sourceRoot records output buildTarget manifest mode onFailure true isolated
        else throw "--keep-eval is not valid for materialize-units (nothing to strip: a \
          unit is a single standalone module); it applies to materialize-repo"
    | "--in-process" :: tail =>
        if allowRepoFlags then
          go tail sourceRoot records output buildTarget manifest mode onFailure keepEval false
        else throw "--in-process is not valid for materialize-units (units have their own \
          per-target build model); it applies to materialize-repo"
    | flag :: _ => throw s!"unknown or incomplete argument: {flag}"
  go args none none none none none .replace .fail false true

private def parseArgs : List String → Except String Command
  | "rewrite-file" :: rest => .rewriteFile <$> parseRewriteArgs rest
  | "materialize-repo" :: rest => .materializeRepo <$> parseMaterializeArgs (allowRepoFlags := true) rest
  | "materialize-units" :: rest => .materializeUnits <$> parseMaterializeArgs (allowRepoFlags := false) rest
  | command :: _ => .error s!"unknown command: {command}"
  | [] => .error "command is required"

private def reexecMarker := "LEAN_REASSEMBLE_REEXEC"

private def reexecPathFlags := ["--source-root", "--records", "--output", "--manifest"]

private unsafe def execute : Command → IO Unit
  | .rewriteFile config => rewriteFile config
  | .materializeRepo config => LeanReassemble.materializeRepo config
  | .materializeUnits config => LeanReassemble.materializeUnits config

unsafe def runCli (args : List String) : IO UInt32 := do
  -- Internal per-file worker for isolated `materialize-repo`: the parent spawns
  -- `<self> --internal-rewrite-one <json>` once per source file so each file's Lean
  -- environment dies with its child. Handled before help/parse/reexec: it is not a
  -- user command, and it must NOT re-exec under `lake env` (the parent already did, and
  -- this child inherits that environment). See `rewriteOneChild`.
  match args with
  | flag :: payload :: _ =>
    if flag == rewriteOneFlag then
      match (Json.parse payload >>= fromJson? (α := RewriteOneRequest)) with
      | .ok request =>
          try
            rewriteOneChild request
            return 0
          catch error =>
            -- A per-file failure (module no longer elaborates, or `--on-failure fail`
            -- hit a genuine failure): exit nonzero so the parent aborts the run. The
            -- message goes to the inherited stderr for the root cause.
            IO.eprintln error.toString
            return 1
      | .error error =>
          IO.eprintln s!"lean-reassemble: bad {rewriteOneFlag} payload: {error}"
          return 2
  | _ => pure ()
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  let command ← match parseArgs args with
    | .ok command => pure command
    | .error error =>
        IO.eprintln s!"lean-reassemble: {error}\n{usage}"
        return 2
  try
    if (← IO.getEnv reexecMarker).isNone then
      if command.requiresManifest then
        let cwd ← IO.currentDir
        let root := Corpus.Reexec.absolutize cwd command.sourceRoot
        if !(← (root / "lake-manifest.json").pathExists) then
          throw <| IO.userError s!"lean-reassemble: lake-manifest.json does not exist in {root}"
      return (← Corpus.Reexec.reexecUnderLake reexecMarker reexecPathFlags command.sourceRoot args)
    execute command
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end LeanReassemble

unsafe def main (args : List String) : IO UInt32 :=
  LeanReassemble.runCli args
