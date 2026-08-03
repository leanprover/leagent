# Agentic Tools for Lean

Tools for using Lean from agents and for training agents to use Lean.

## Build

```bash
make              # lean_extract + lean_reassemble, symlinked into bin/
make example      # build examples/tree-project, needed to run the walkthrough
make help         # all targets
```

Everything pins Lean 4.31.0 (`make toolchain` installs it via elan). Each package
also builds on its own with `lake build`; the Makefile only names the targets and
gives the binaries a stable path.

New here? [`examples/README.md`](examples/README.md) is a guided tour of the whole
toolchain on a four-file example project — extract a corpus, reverse-elaborate
proofs into tactic scripts, capture per-tactic goal states, slice one theorem's
dependency closure, and assemble both a sorried repository and standalone
single-theorem tasks.

## Packages

- `lean-extract/`: corpus extraction from Lean projects.
- `workers/`: Lean language-server worker utilities.
- `reassemble/`: materialize extracted corpus records back into repository or
  per-theorem unit artifacts. See `reassemble/README.md`.
- `examples/`: a small self-contained Lean project plus a walkthrough of every
  mode. See `examples/README.md`.

## Docs

- [`docs/single-decl-extraction.md`](docs/single-decl-extraction.md): extracting
  one declaration with its dependency closure, and assembling it into a single
  standalone Lean unit.
- [`docs/proof-state-extraction.md`](docs/proof-state-extraction.md): capturing
  the interior of every tactic proof — the nested tactic tree with the goal state
  before and after each step.
- [`docs/corpus-reassembly.md`](docs/corpus-reassembly.md): the design behind
  repository and per-theorem unit materialization.
- [`workers/docs/proof-simplification.md`](workers/docs/proof-simplification.md):
  how proof terms become verified tactic scripts.
