/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
`Corpus.TestAssert` — the assertion used by the package's test executables.

Each test target (`resume_tests`, `decl_closure_tests`, `proof_states_tests`) is
its own `lean_exe` root, so they cannot share a `private` helper; this module is
the one place the assertion lives.
-/

namespace Corpus.TestAssert

/-- Fail the test run with `message` unless `condition` holds. -/
def assert (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw <| IO.userError message

end Corpus.TestAssert
