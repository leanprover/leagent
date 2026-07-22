import LeanReassemble

namespace LeanReassemble

private def usage : String := "\
Usage:
  lean_reassemble rewrite-file --source-root <lake-project>
    --records <declarations.jsonl> --file <relative.lean>
    --output <rewritten.lean>

  lean_reassemble materialize-repo --source-root <lake-project>
    --records <declarations.jsonl> --output <artifact-dir>
    [--build-target <target>]

  lean_reassemble materialize-units --source-root <lake-project>
    --records <declarations.jsonl> --output <artifact-dir>
    [--build-target <target>]"

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

private def parseRewriteArgs (args : List String) : Except String RewriteConfig := do
  let rec go (remaining : List String) (sourceRoot records output : Option String)
      (file : Option String) : Except String RewriteConfig :=
    match remaining with
    | [] => return {
        sourceRoot := ← requireArg "--source-root" sourceRoot
        records := ← requireArg "--records" records
        file := ← requireArg "--file" file
        output := ← requireArg "--output" output
      }
    | "--source-root" :: value :: tail => go tail (some value) records output file
    | "--records" :: value :: tail => go tail sourceRoot (some value) output file
    | "--file" :: value :: tail => go tail sourceRoot records output (some value)
    | "--output" :: value :: tail => go tail sourceRoot records (some value) file
    | flag :: _ => throw s!"unknown or incomplete argument: {flag}"
  go args none none none none

private def parseMaterializeArgs (args : List String) : Except String MaterializeConfig := do
  let rec go (remaining : List String) (sourceRoot records output buildTarget : Option String) :
      Except String MaterializeConfig :=
    match remaining with
    | [] => return {
        sourceRoot := ← requireArg "--source-root" sourceRoot
        records := ← requireArg "--records" records
        output := ← requireArg "--output" output
        buildTarget
      }
    | "--source-root" :: value :: tail =>
        go tail (some value) records output buildTarget
    | "--records" :: value :: tail =>
        go tail sourceRoot (some value) output buildTarget
    | "--output" :: value :: tail =>
        go tail sourceRoot records (some value) buildTarget
    | "--build-target" :: value :: tail =>
        go tail sourceRoot records output (some value)
    | flag :: _ => throw s!"unknown or incomplete argument: {flag}"
  go args none none none none

private def parseArgs : List String → Except String Command
  | "rewrite-file" :: rest => .rewriteFile <$> parseRewriteArgs rest
  | "materialize-repo" :: rest => .materializeRepo <$> parseMaterializeArgs rest
  | "materialize-units" :: rest => .materializeUnits <$> parseMaterializeArgs rest
  | command :: _ => .error s!"unknown command: {command}"
  | [] => .error "command is required"

private def reexecMarker := "LEAN_REASSEMBLE_REEXEC"

private def absolutize (cwd : System.FilePath) (path : System.FilePath) : System.FilePath :=
  if path.isAbsolute then path else cwd / path

private unsafe def reexecUnderLake (sourceRoot : System.FilePath)
    (rawArgs : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let self ← IO.appPath
  let root := absolutize cwd sourceRoot
  let pathFlags := ["--source-root", "--records", "--output"]
  let rec rebuild : List String → List String
    | [] => []
    | flag :: value :: rest =>
        if pathFlags.contains flag then
          flag :: (absolutize cwd value).toString :: rebuild rest
        else
          flag :: rebuild (value :: rest)
    | [value] => [value]
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["env", self.toString] ++ (rebuild rawArgs).toArray
    cwd := some root
    env := #[(reexecMarker, some "1")]
    setsid := false
  }
  child.wait

private unsafe def execute : Command → IO Unit
  | .rewriteFile config => rewriteFile config
  | .materializeRepo config => LeanReassemble.materializeRepo config
  | .materializeUnits config => LeanReassemble.materializeUnits config

unsafe def runCli (args : List String) : IO UInt32 := do
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
        let root := absolutize cwd command.sourceRoot
        if !(← (root / "lake-manifest.json").pathExists) then
          throw <| IO.userError s!"lean-reassemble: lake-manifest.json does not exist in {root}"
      return (← reexecUnderLake command.sourceRoot args)
    execute command
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1

end LeanReassemble

unsafe def main (args : List String) : IO UInt32 :=
  LeanReassemble.runCli args
