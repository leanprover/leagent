# Proof-Complexity Metrics

## Goals

The corpus record describes a proof by its source (`body` / `decl_source`), its
reverse-elaborated script (`proof_script` / `proof_method`, under `--reverse-elab`),
and its dependency cones (`deps` / `premises`). None of these is a *measure* of how
big or how intricate the proof is. `--proof-metrics` adds that measure, so a
consumer can estimate proof complexity — and, downstream, down-sample a dataset by
it — without joining against the `--proof-states` dataset.

Unlike the grind / proof-states / decl modes, `--proof-metrics` does **not** replace
corpus extraction: it *augments* the regular run, adding columns to the same
`theorems` / `definitions` records. That is deliberate. The output goes to a wide
table (Aurora), where the design goal is to avoid joins — one row per constant, with
every metric as its own scalar or small-array column, and the consumer selects the
columns it wants.

## Contract

```bash
lean_extract \
  --modules     Project \
  --source-root ../project \
  --proof-metrics \
  --output      ./out
```

The output layout is exactly the plain run's (`data/theorems/train.jsonl`,
`data/definitions.jsonl`, `metadata.json`); only the record schema grows. The metric
columns are **always present** in the schema — a run *without* `--proof-metrics`
emits them as `null`/`[]`, so a reader never has to branch on whether the flag was
set. The flag only decides whether they carry real values.

`--proof-metrics` composes with `--reverse-elab` and with `--split-by-tag`. It is
not one of the mutually-exclusive modes.

## The two families

The columns split into two families that measure **different things** and are
populated on **different rows**. Conflating them is the one mistake the schema is
built to prevent.

### Tactic family

Computed from the author's `by`-block **syntax** — never from the elaborated term.
It measures the human-written tactic script:

| Column | Meaning |
|---|---|
| `tactic_step_count` | top-level author tactics |
| `tactic_total_count` | all author tactics, nested children included |
| `max_tactic_depth` | deepest tactic nesting (0 for a flat proof) |
| `tactic_kinds` | sorted distinct tactic-kind strings |
| `tactic_histogram` | kind → occurrence count |
| `case_split_count` | `induction` / `cases` / `rcases` / `obtain` / `match` / `split` / `by_cases` |
| `rewrite_count` | `rw` / `rewrite` (`simp` counts as automation, not a rewrite) |
| `have_count` | `have` / `suffices` / `let` |
| `calc_steps` | steps inside `calc` blocks |
| `automation_tactics` | sorted short names of automation used (`simp`, `omega`, `grind`, `aesop`, …) |

For a **term-mode proof** (`:= rfl`, `:= fun …` — no `by`) every one of these is
`null`/`[]`. There is no author tactic script to measure. The `is_term_proof` flag
is what makes those nulls interpretable: `true` means "not a tactic proof", not "a
zero-step tactic proof".

### Semantic family

Computed from the elaborated proof `Expr`, so it is populated for **every** theorem
— including term-mode ones, which is exactly the set the tactic family leaves null.

| Column | Meaning |
|---|---|
| `proof_term_size` | distinct sub-expressions of the proof term (`ReverseElab.distinctNodes`) |
| `proof_term_depth` | approximate depth of the proof term (`Expr.approxDepth`) |

Both are `null` for non-theorems (a `def`'s value is not a proof).

### Attributes

`attributes` lists the declaration's `@[…]` names (`@[simp]` → `"simp"`), sorted.
It is read from the declaration modifiers, so it is present for term and tactic
proofs alike.

## Why syntax, not the InfoTree

`--proof-states` walks the InfoTree and renders every goal, which is bounded by a
step ceiling (`ProofStates.stepCeiling`) precisely because rendering is the cost
centre. The tactic family needs none of that: counting syntax nodes is `O(tree)`
and allocates nothing per node, so it has **no ceiling** and reports honest numbers
for exactly the large, intricate proofs a complexity estimate cares most about.

The two paths must nonetheless agree on *what counts as a tactic*. They share one
definition — `CollectCommon.tacticKindSet`, the `tactic` + `conv` parser categories
read from the file's own environment — so `--proof-metrics`' `tactic_total_count`
equals `--proof-states`' `step_count` and `max_tactic_depth` equals its `max_depth`,
theorem for theorem. Reading the set from the environment (rather than a hard-coded
list) is also what makes the classifiers pick up project-defined and Mathlib tactics
for free; the automation / case-split / rewrite recognizers match on the kind
*string*, so they recognize `aesop` / `linarith` / `norm_num` without the extractor
depending on Mathlib.

## Orthogonality with reverse-elaboration

`--reverse-elab` fills `proof_script` / `proof_method` by re-elaborating the proof
term into a synthesized tactic script. The proof-metric columns are computed from
the author's syntax and the elaborated term directly, so they are **byte-identical**
whether or not `--reverse-elab` is passed. A `--proof-metrics --reverse-elab` run is
just the metric columns plus the two reverse-elab columns; the metrics never reflect
the machine reconstruction. This keeps provenance clean: the tactic family is always
what the author wrote in tactic mode, the semantic family is always the elaborated
term, and neither blurs into the other.

## Implementation

- `lean-extract/Corpus/ProofMetrics.lean` — the pure, syntax-only analysis
  (`analyzeTacticProof`, `attributesOf`, `buildMetricsMap`). `Info`-free, so it is
  unit-testable without an `Environment`.
- `CollectCommon.tacticKindSet` — the shared tactic-kind selection set (also used by
  `Corpus.ProofStates`, so the two cannot drift).
- `CorpusManifest.buildEntry` — looks up the tactic family by the declaration's
  selection position and sizes the semantic family from the proof term.
- `Corpus.Records.ConstRecord` — the wire columns and their `null`-tolerant decoder.
