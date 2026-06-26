-- Lake build configuration for the LeanSQLite package.
import Lake
open Lake DSL

package LeanExtract where

-- `WorkerPlugins.ReverseElab` (the verified proof-term → tactic-script reverse
-- elaborator) lives in the sibling `workers` package so the worker plugin and
-- this import-based extractor share ONE copy of the soundness-critical code.
require workers from "../workers"

lean_lib Corpus where
  globs := #[.submodules `Corpus]

@[default_target]
lean_exe lean_extract where
  root := `Corpus.Main
  supportInterpreter := true
