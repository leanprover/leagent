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

Computed from a proof's tactic-script **syntax** — never from the elaborated term.
It measures the script's shape:

| Column | Meaning |
|---|---|
| `tactic_step_count` | top-level tactics |
| `tactic_total_count` | all tactics, nested children included |
| `max_tactic_depth` | deepest tactic nesting (0 for a flat proof) |
| `tactic_kinds` | sorted distinct tactic-kind strings |
| `tactic_histogram` | kind → occurrence count |
| `case_split_count` | `induction` / `cases` / `rcases` / `obtain` / `match` / `split` / `by_cases` |
| `rewrite_count` | `rw` / `rewrite` (`simp` counts as automation, not a rewrite) |
| `have_count` | `have` / `suffices` / `let` |
| `calc_steps` | steps inside `calc` blocks |
| `automation_tactics` | sorted short names of automation used (`simp`, `omega`, `grind`, `aesop`, …) |
| `tactic_metrics_source` | which body was measured: `"author"` / `"reverse_elab"` / `null` |

**Which script is measured depends on the run** (see
[Reverse-elaboration](#reverse-elaboration), below). On a plain run it is the
author's source `by` block; on a `--reverse-elab` run it is the reverse-elaborated
body. `tactic_metrics_source` records which, so every row is self-describing — a
consumer that merges plain and rev-elab extractions can filter on it.

The family is `null`/`[]` when there is no tactic script to measure: a **term-mode
proof** (`:= rfl`, `:= fun …` — no `by`) on a plain run, or a proof that failed to
reverse-elaborate on a `--reverse-elab` run. In both cases `tactic_metrics_source`
is `null`. The `is_term_proof` flag always reports the **original** proof — `true`
means "the author wrote a term proof" — so it disambiguates the nulls even on a
rev-elab run, where a term-proved theorem's synthesized `by exact …` script *does*
get measured (the row is then `is_term_proof = true` with a non-null tactic family
sourced from `reverse_elab`).

### Semantic family

Computed from the elaborated proof `Expr`, so it is populated for **every** theorem
— including term-mode ones, which is exactly the set the tactic family leaves null.

| Column | Meaning |
|---|---|
| `proof_term_size` | distinct sub-expressions of the proof term (`ReverseElab.distinctNodes`) |
| `proof_term_depth` | approximate depth of the proof term (`Expr.approxDepth`) |

Both are `null` for non-theorems (a `def`'s value is not a proof). Unlike the
tactic family, the semantic family is **unaffected by `--reverse-elab`**: the
reverse-elaborated term is defeq to the original, so its size and depth are the same
body either way.

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
read from the file's own environment — so on a plain (`author`-sourced) run
`--proof-metrics`' `tactic_total_count` equals `--proof-states`' `step_count` and
`max_tactic_depth` equals its `max_depth`, theorem for theorem. (On a
`--reverse-elab` run the tactic family measures a different body — the synthesized
script — so it no longer tracks proof-states, which always walks the author's
proof.) Reading the set from the environment (rather than a hard-coded list) is also
what makes the classifiers pick up project-defined and Mathlib tactics for free; the
automation / case-split / rewrite recognizers match on the kind *string*, so they
recognize `aesop` / `linarith` / `norm_num` without the extractor depending on
Mathlib.

## Interaction with reverse-elaboration

`--reverse-elab` re-elaborates each proof term into a synthesized tactic script,
recorded in `proof_script` / `proof_method`. On such a run, the tactic family
measures **that script** rather than the author's source proof — the run's purpose
is the reconstruction, so its metrics are what the run reports. Concretely:

- **Plain run** — tactic family from the author's `by` block; `tactic_metrics_source
  = "author"`. Term-mode proofs get a null tactic family.
- **`--reverse-elab` run** — tactic family re-parsed from the synthesized script;
  `tactic_metrics_source = "reverse_elab"`. A proof that produced no script
  (`fail` / `skipped_large` / `timeout` / `deadline_skipped`) gets a null tactic
  family with a `null` source.

Two things are held invariant across the two runs, so provenance stays legible:
`is_term_proof` and `attributes` always describe the **original** declaration, and
the **semantic family** always measures the elaborated term (defeq under
reverse-elaboration). Only the tactic family switches which body it reflects, and
`tactic_metrics_source` records the switch per row — a single wide-table row cannot
see the run's flags, so it carries its own provenance.

## Implementation

- `lean-extract/Corpus/ProofMetrics.lean` — the pure, syntax-only analysis
  (`analyzeTacticProof`, `attributesOf`, `buildMetricsMap`), plus `metricsFromScript`
  (re-parse a rendered `by …` script and measure it) and `withNullTactics` (null the
  tactic family while keeping `isTermProof`/`attributes`). `Info`-free, so it is
  unit-testable without an `Environment`.
- `CollectCommon.tacticKindSet` — the shared tactic-kind selection set (also used by
  `Corpus.ProofStates`, so the two cannot drift).
- `CorpusManifest.buildEntry` — resolves the tactic family (author metrics, or the
  reverse-elab body under `--reverse-elab`), sets `metricsSource`, and sizes the
  semantic family from the proof term.
- `Corpus.Records.ConstRecord` — the wire columns and their `null`-tolerant decoder.
