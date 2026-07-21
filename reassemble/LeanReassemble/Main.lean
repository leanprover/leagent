import LeanReassemble

namespace LeanReassemble

private def usage : String := "\
Usage: lean_reassemble rewrite-file --source-root <lake-project>
       --records <declarations.jsonl> --file <relative.lean>
       --output <rewritten.lean>"

private def requireArg (name : String) : Option String → Except String String
  | some value => .ok value
  | none => .error s!"{name} is required"

private def parseArgs (args : List String) : Except String RewriteConfig := do
  let ("rewrite-file" :: rest) := args
    | throw "expected rewrite-file command"
  let rec go (remaining : List String) (sourceRoot records output : Option String)
      (file : Option String) : Except String RewriteConfig :=
    match remaining with
    | [] => do
        let sourceRoot ← requireArg "--source-root" sourceRoot
        let records ← requireArg "--records" records
        let file ← requireArg "--file" file
        let output ← requireArg "--output" output
        return {
          sourceRoot
          records
          file
          output
        }
    | "--source-root" :: value :: tail => go tail (some value) records output file
    | "--records" :: value :: tail => go tail sourceRoot (some value) output file
    | "--file" :: value :: tail => go tail sourceRoot records output (some value)
    | "--output" :: value :: tail => go tail sourceRoot records (some value) file
    | flag :: _ => throw s!"unknown or incomplete argument: {flag}"
  go rest none none none none

private def reexecMarker := "LEAN_REASSEMBLE_REEXEC"

private def absolutize (cwd : System.FilePath) (path : System.FilePath) : System.FilePath :=
  if path.isAbsolute then path else cwd / path

private unsafe def reexecUnderLake (config : RewriteConfig) : IO UInt32 := do
  let cwd ← IO.currentDir
  let self ← IO.appPath
  let root := absolutize cwd config.sourceRoot
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #[
      "env", self.toString, "rewrite-file",
      "--source-root", root.toString,
      "--records", (absolutize cwd config.records).toString,
      "--file", config.file,
      "--output", (absolutize cwd config.output).toString
    ]
    cwd := some root
    env := #[(reexecMarker, some "1")]
    setsid := false
  }
  child.wait

unsafe def runCli (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  let config ← match parseArgs args with
    | .ok config => pure config
    | .error error =>
        IO.eprintln s!"lean-reassemble: {error}\n{usage}"
        return 2
  try
    if (← IO.getEnv reexecMarker).isNone then
      return (← reexecUnderLake config)
    rewriteFile config
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end LeanReassemble

unsafe def main (args : List String) : IO UInt32 :=
  LeanReassemble.runCli args
