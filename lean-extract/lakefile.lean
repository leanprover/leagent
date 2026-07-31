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

@[default_target]
lean_exe lean_extract where
  root := `Corpus.Main
  supportInterpreter := true

lean_exe resume_tests where
  root := `ResumeTests

lean_exe decl_closure_tests where
  root := `DeclClosureTests

lean_exe proof_states_tests where
  root := `ProofStatesTests
  supportInterpreter := true
