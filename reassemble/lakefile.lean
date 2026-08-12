import Lake
open Lake DSL

package reassemble

require LeanExtract from "../lean-extract"
require workers from "../workers"

lean_lib LeanReassemble where
  roots := #[`LeanReassemble]

/--
Link args that make the shipped exe load the Lean runtime dynamically — the same
scheme as `lean-extract/lakefile.lean` (see its `runtimeLinkArgs` for the full
rationale): link `-lleanshared` so the static Lean archives drop out (~215 MB ->
a few MB), and bake a `DT_RUNPATH` (new dtags, so `LD_LIBRARY_PATH` overrides it)
of `$ORIGIN` entries plus the build-time `-K libdir=…` the Makefile injects for
local builds (release builds pass an empty `libdir` and omit the absolute entry).
-/
def runtimeLinkArgs : Array String :=
  let originRunpath := "$ORIGIN:$ORIGIN/../lib/lean"
  -- An empty `libdir` (release builds) is treated as absent, leaving only the
  -- `$ORIGIN` entries — no meaningless build-machine path baked into the binary.
  let runpath :=
    match (get_config? libdir : Option String) with
    | some dir => if dir.isEmpty then originRunpath else s!"{originRunpath}:{dir}"
    | none     => originRunpath
  #["-lleanshared", "-Wl,--enable-new-dtags", s!"-Wl,-rpath,{runpath}"]

@[default_target]
lean_exe lean_reassemble where
  root := `LeanReassemble.Main
  supportInterpreter := true
  -- Dynamically link the Lean runtime rather than statically embedding it; see
  -- `runtimeLinkArgs` above. `supportInterpreter` is unaffected.
  moreLinkArgs := runtimeLinkArgs

lean_exe reassemble_tests where
  root := `ReassembleTests
  supportInterpreter := true
