-- Lake build configuration for the LeanExtract package.
import Lake
open Lake DSL

package LeanExtract where

-- The extractor now drives Lean's frontend directly, in-process, so it no longer
-- depends on the sibling `workers` package (the `lean --worker` driver + LSP
-- plugins). The extraction logic that used to live in `WorkerPlugins`
-- (reverse-elaboration, the corpus/grind collectors) was absorbed into `Corpus.*`.

lean_lib Corpus where
  globs := #[.submodules `Corpus]

/--
Link args that make the shipped exe load the Lean runtime dynamically.

On Linux Lake always links Lean statically (`sharedLean` is hardwired to
Windows-only), baking a ~100 MB copy of the runtime into every binary. Naming
`-lleanshared` makes the linker resolve every Lean/Std/Init symbol from the shared
library first, so the static Lean archives Lake still appends contribute nothing
and drop out — shrinking the binary from ~215 MB to a few MB. The library itself
is found at link time via the `-L <toolchain>/lib/lean` Lake already passes.

At RUN time the loader must find `libleanshared.so` before `main`, so we bake a
`DT_RUNPATH` (NOT `DT_RPATH` — `--enable-new-dtags` selects RUNPATH, which the
loader searches *after* `LD_LIBRARY_PATH`, so a user can always override it):
  * `$ORIGIN` and `$ORIGIN/../lib/lean` — always baked; a binary placed beside a
    toolchain (upstream-`lean` style) finds the runtime with zero environment;
  * the build-time absolute library directory, injected only when `lake` is given
    `-K libdir=…`. The Makefile passes `lean --print-libdir` for LOCAL builds, so a
    locally-built binary runs with zero environment. The release workflow builds
    with an empty `libdir` (see `.github/workflows/release.yml`) and omits this
    entry, because a RELEASED binary's absolute path would be the CI builder's
    `$HOME/.elan/…` — meaningless on a user's machine (rpath cannot expand `$HOME`,
    only `$ORIGIN`/`$LIB`/`$PLATFORM`, so there is no portable absolute default).
    Consumers of a released binary co-locate it with a toolchain (the `$ORIGIN`
    entries above) or point at one with `LD_LIBRARY_PATH=$(lean --print-libdir)`.
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
lean_exe lean_extract where
  root := `Corpus.Main
  supportInterpreter := true
  -- Dynamically link the Lean runtime instead of statically embedding it; see the
  -- shared note on `runtimeLinkArgs` below. `supportInterpreter` is unaffected:
  -- the interpreter resolves against the app's exported dynamic symbols, exactly
  -- as the upstream `lean` binary (itself dynamically linked) does.
  moreLinkArgs := runtimeLinkArgs

lean_exe resume_tests where
  root := `ResumeTests

lean_exe decl_closure_tests where
  root := `DeclClosureTests

lean_exe proof_states_tests where
  root := `ProofStatesTests
  supportInterpreter := true

lean_exe proof_metrics_tests where
  root := `ProofMetricsTests
  supportInterpreter := true
