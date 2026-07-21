import Lake
open Lake DSL

package reassemble

require LeanExtract from "../lean-extract"
require workers from "../workers"

lean_lib LeanReassemble where
  roots := #[`LeanReassemble]

@[default_target]
lean_exe lean_reassemble where
  root := `LeanReassemble.Main
  supportInterpreter := true

lean_exe reassemble_tests where
  root := `ReassembleTests
  supportInterpreter := true
