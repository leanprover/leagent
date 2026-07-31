# Agentic Tools for Lean

Tools for using Lean from agents and for training agents to use Lean.

## Packages

- `lean-extract/`: corpus extraction from Lean projects.
- `workers/`: Lean language-server worker utilities.
- `reassemble/`: materialize extracted corpus records back into repository or
  per-theorem unit artifacts. See `reassemble/README.md`.

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
