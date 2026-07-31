# lean-extract

A Lean 4 **corpus extractor**: it walks a Lean project and emits a JSONL dataset
— one record per theorem/definition — capturing the type, value, source
signature and body, dependencies, transitive premises, axioms, and a verified
reverse-elaborated tactic `proof_script`. The output is laid out for direct
upload as a HuggingFace dataset (modeled after NuminaMath-LEAN with LeanDojo-style
premise tracking).

The tool is **project-agnostic**: the modules to extract, the source root, and
any tagging rules are all supplied on the command line.

## Extraction modes

Four things the tool can produce. They are mutually exclusive:

- **Corpus** (default) — one record per theorem/definition across the whole
  project, split into `theorems` and `definitions` configs.
- **Single declaration** (`--decl`) — one named declaration plus its transitive
  owned dependency closure, in its own directory, with each record annotated by
  cone. Composes with `reassemble` into a standalone Lean unit. See
  [Single-declaration mode](#single-declaration-mode).
- **Proof states** (`--proof-states`) — the *interior* of every tactic proof: one
  record per tactic-proved theorem holding the nested tactic tree with the goal
  state before and after each step. See [Proof-state mode](#proof-state-mode).
- **Grind** (`--grind-manifest` / `--grind-in-proof`) — AlphaGrind datasets;
  each replaces corpus extraction with its own schema and output directory.

## Two ways it runs

Within corpus and single-declaration mode, `lean-extract` has two extraction
backends, selected with `--enumerate`:

- **`glob` (default)** — the **frontend** path. The tool discovers the project's
  source files on disk and drives Lean's frontend directly, using one isolated
  child process per file by default, then folds a collector over each file's
  post-elaboration environment. `--no-isolate-files` uses one shared process.
  This sees each file in its *true elaboration context* (section variables,
  `open`s, `set_option`s, registered tactics) and finds **orphan** declarations
  in files that no other module imports.
- **`import` (fallback)** — the legacy path: `importModules` the root modules
  and walk the resulting `Environment`. Cannot reconstruct source
  signatures/bodies (its byte-slicer was removed in the 4.31 port) and misses
  orphan files.

Both backends write the **same JSONL schema**, so datasets stay comparable.

> The extraction logic lives in `Corpus.*`: the corpus/grind collectors
> (`Corpus.CorpusManifest`, `Corpus.GrindManifest`, `Corpus.GrindInProof`), the
> reverse-elaborator (`Corpus.ReverseElab`), and the frontend driver
> (`Corpus.Frontend`). See [Architecture](#architecture) below.

> **History.** The `glob` path formerly drove a pool of `lean --worker`
> subprocesses and pulled per-declaration data back over LSP from a Lean plugin
> (in a sibling `workers` package). It now drives the frontend directly; the plugin
> logic was absorbed into `Corpus.*` and the `workers` dependency dropped.
> The output is unchanged except that compiler-generated auxiliary names
> (`match_*`, `_proof_*`) may be attributed differently — the worker elaborated
> with `Elab.async := true` (the LSP default) while the frontend path uses the
> synchronous default; no real declaration, statement, or proof differs.

## Build

```bash
lake build
```

The binary lands at `.lake/build/bin/lean_extract`. No plugin `.so`s or sibling
package build are needed.

Toolchain: the package pins Lean **4.31.0** via `lean-toolchain`.

## Run

Both backends need `LEAN_PATH` pointing at the project-under-study's built
`.olean`s (the frontend imports each file's dependencies). The tool handles this:
if `--source-root` (or the current directory) is a Lake project, it re-execs
itself under `lake env` from there, so frontend elaboration inherits the
right search path. You never need to wrap the call in `lake env` yourself.

Because the child runs with its working directory set to the project, relative
path arguments (`--output`, `--config`, `--source-root`,
`--dataset-card-config`) are rewritten to absolute paths against your original
working directory first. (Before this was fixed, a bare flag such as
`--no-private` appearing *before* a relative `--output` shifted the rewriter's
parity and the output silently landed inside the source tree instead.)

```bash
./.lake/build/bin/lean_extract \
    --modules     LeanSQLite \
    --source-root ../sqlite \
    --output      ./corpus-output \
    --config      ./tags.json        # optional
```

Make sure the target project is built first (`cd ../sqlite && lake build`) so the
`.olean`s exist.

### CLI flags

| Flag | Required | Notes |
|------|----------|-------|
| `--modules <Name>` | yes | Root module to extract. Repeat for several. Also defines the **owned prefix tree** — constants outside it (Mathlib/Init/Std) are filtered out, and premises follow only owned constants. |
| `--output <dir>` | yes* | Output directory (HF Hub-ready layout). *Not required with `--list-orphans`. |
| `--enumerate glob\|import` | no | Extraction backend. Default `glob` (frontend path). `import` is the legacy Environment walk. |
| `--list-orphans` | no | Print the modules on disk (under `--modules`) that are **not** in the import closure of the roots, then exit. A diagnostic — writes no dataset. |
| `--source-root <dir>` | no | Project root: resolves module↔file paths and triggers the `lake env` re-exec. Defaults to `.`. |
| `--config <path>` | no | Tags-config JSON (see [Tags](#tags-config)). Default: no tags. |
| `--reverse-elab` | no | Reverse-elaborate each theorem's proof term into a verified tactic `proof_script`. **Off by default** — it re-elaborates every proof (slower). |
| `--closers` | no | With `--reverse-elab`, also try goal-closing tactics (`simp`/`omega`/…) to recover high-level proofs for automation-heavy bodies. ~20× slower; off by default. |
| `--skip-reverse <decl>` | no | Skip reverse-elaboration for a theorem declaration, matching either the corpus display name or raw Lean internal name. Repeatable; emits `proof_method=skipped_requested`. |
| `--jobs <n>` | no | Extraction concurrency. Isolated mode defaults to half the available hardware threads, capped at `4`; in-process mode defaults to `1`. |
| `--no-isolate-files` | no | Elaborate files in one shared process instead of the default per-file child processes. |
| `--resume` | no | Reuse valid per-file shards from an interrupted default (`glob`, isolated) run. Changed inputs invalidate the staging directory. |
| `--reverse-timeout <seconds>` | no | Hard timeout for an isolated file when reverse elaboration is enabled. Default `300`; `0` disables it. A timed-out file is retried without reverse elaboration. |
| `--include-internal` | no | Emit compiler-internal names (`_aux.*`, `match_*`, constructors, recursors). Default: false. |
| `--no-private` | no | Skip `private` declarations. Default: include them. |
| `--decl <Name>` | no | **Single-declaration mode.** Extract this declaration plus its transitive owned dependency closure into its own per-target directory. Repeatable; the union of needed files is elaborated once. See [Single-declaration mode](#single-declaration-mode). |
| `--strict-closure` | no | With `--decl`, fail instead of warning when a closure member has no emitted record (constructors, recursors, generated lemmas). |
| `--proof-states` | no | **Proof-state mode.** Emit one record per tactic-proved theorem with the nested tactic tree and per-step goal states, to `data/proof-states/train.jsonl`. Replaces corpus extraction. See [Proof-state mode](#proof-state-mode). |
| `--split-by-tag <key>` | no | Stratified 80/10/10 train/valid/test split of theorems keyed on a tag value. Definitions are always one split. |
| `--seed <n>` | no | Deterministic split seed (default 0). |
| `--dataset-card-config <path>` | no | JSON describing dataset identity; generates the HF dataset card (`README.md`). |
| `--help`, `-h` | no | Print usage and exit. |

### Examples

```bash
# Default frontend-driven extraction.
lean_extract --modules LeanSQLite --source-root ../sqlite --output ./out

# With verified proof scripts and four concurrent file jobs.
lean_extract --modules LeanSQLite --source-root ../sqlite --output ./out --reverse-elab --jobs 4

# Resume an interrupted isolated extraction.
lean_extract --modules Project --source-root ../project --output ./out --reverse-elab --resume

# Use the shared in-process frontend.
lean_extract --modules Project --source-root ../project --output ./out --no-isolate-files

# One theorem plus its whole dependency closure, in its own directory.
lean_extract --modules LeanSQLite --source-root ../sqlite \
    --decl LeanSQLite.Btree.insert_sound --output ./decl-out

# Find files no imported module pulls in.
lean_extract --modules LeanSQLite --source-root ../sqlite --list-orphans

# Legacy import-based path (signature/body will be null).
lean_extract --modules LeanSQLite --source-root ../sqlite --output ./out --enumerate import
```

## Output

```
<output>/
  README.md                  # HF dataset card (only with --dataset-card-config)
  metadata.json              # extractor summary (counts, modules, version)
  data/
    definitions.jsonl        # all definitions (single split)
    theorems/
      train.jsonl            # all theorems  (or train/valid/test with --split-by-tag)
```

The dataset is published as two HuggingFace configs: **`theorems`** (proof-bearing
items) and **`definitions`** (context items — defs, structures, inductives,
abbrevs, axioms, opaques).

### Record schema

One JSON object per line, snake_case keys, stable field order. The same schema
is used for both configs; fields not applicable to a record are `null`/`[]`.

| Field | Type | Meaning |
|-------|------|---------|
| `name` | string | Fully-qualified constant name. |
| `kind` | string | `theorem`/`def`/`axiom`/`opaque`/`quot`/`inductive`/`structure`/`ctor`/`rec`, prefixed `private ` when applicable. |
| `module` | string | The `.lean` module that elaborated the constant. |
| `file` | string\|null | Source path relative to `--source-root`. |
| `start_line`/`start_col`/`end_line`/`end_col` | int\|null | Declaration source range (doc-comment-inclusive). |
| `signature` | string\|null | Source text of the statement (binders + `: type`), excluding the `:=`/body and the leading doc comment. **Worker path only** (import path emits null). |
| `body` | string\|null | Source text of the value/proof (the `declVal`; for `:= term`, just the term). **Worker path only.** |
| `type` | string | Pretty-printed elaborated type. |
| `value` | string\|null | Pretty-printed term value for defs/theorems. |
| `proof_script` | string\|null | Verified reverse-elaborated tactic script (`--reverse-elab` only; theorems). See the [proof-simplification doc](../workers/docs/proof-simplification.md). |
| `proof_method` | string\|null | Which reverse-elaboration rung produced the script (`structural`/`rfl`/`exact`/`*_opaque`/…). |
| `doc` | string\|null | Docstring, if any. |
| `deps` | string[] | Direct dependencies (constants in `type ∪ value`), sorted, self excluded. |
| `premises` | string[] | Transitive cone of **owned** constants reachable through the value. Sorted. Non-empty for theorems/defs. |
| `axioms` | string[] | Transitive axioms (`collectAxioms`). Theorems only. |
| `is_protected` / `is_private` | bool | `Lean.isProtected` / `Lean.isPrivateName`. |
| `tags` | object(str→str) | Tags from `--config`. |
| `closure_role` | string\|null | `--decl` mode only: `target`, `statement` (needed to state the target), or `proof` (used only by its proof). Null in every other mode. |

Constants are filtered before emit to match a stable dataset: non-owned modules,
auxiliary recursors / noConfusion stubs, generated companions, ctors/recs (unless
`--include-internal`), private names (unless kept), and range-less synthetic
theorems (`.injEq`, `.sizeOf_spec`, …) are dropped.

### Premise-augmented training

Each theorem's `premises` is the transitive cone of in-project constants its
proof depends on — designed for premise-selection training (given the statement
plus the premise definitions, predict the proof):

```python
from datasets import load_dataset
theorems = load_dataset("user/name", "theorems")["train"]
defs     = load_dataset("user/name", "definitions")["train"]
def_by_name = {r["name"]: r for r in defs}

t = theorems[0]
premise_defs = [def_by_name[n] for n in t["premises"] if n in def_by_name]
```

Names in `premises` not found among definitions are other theorems (lemmas) in
the project — look them up in the `theorems` config if you need the full cone.

## Single-declaration mode

`--decl <Name>` extracts one declaration together with everything it depends on,
rather than walking the whole project. Design details and edge-case policy live
in [`docs/single-decl-extraction.md`](../docs/single-decl-extraction.md).

```bash
lean_extract \
    --modules     LeanSQLite \
    --source-root ../sqlite \
    --decl        LeanSQLite.Btree.insert_sound \
    --decl        LeanSQLite.Btree.split_len \
    --output      ./decl-out
```

`--decl` is repeatable and `--output` is a directory. Targets need not be
theorems — a `def` target lands in `definitions.jsonl` — but only a theorem
target has a [unit form](#assembling-one-unit).

`--modules` is still required: it defines the owned prefix tree, which is what
makes the closure finite. Non-owned constants (Init/Std/Mathlib) are not emitted
as records; they are recovered through imports.

### Per-target output

Each target gets a directory mirroring the corpus layout, so existing consumers
read it unchanged:

```text
decl-out/
  LeanSQLite.Btree.insert_sound/
    metadata.json              # target identity, cone counts, imports, order
    dropped.json               # what the closure could not represent, by reason
    data/
      definitions.jsonl        # closure defs/inductives/structures/axioms
      target.jsonl             # the target record alone
      theorems/
        train.jsonl            # premise lemmas + the target
```

Records are written dependencies-first; `metadata.json` carries the
`assemblyOrder` spanning both data files, plus the union of non-owned
`file_imports` needed to make the closure resolvable.

Every record carries `closure_role`:

| Role | Meaning |
|------|---------|
| `target` | The requested declaration. |
| `statement` | Needed to *state* the target (reachable from its type). |
| `proof` | Used only by the target's *proof*. |

The role is a property of a record within one target's closure, not of the
constant — the same lemma can be `statement` for one target and `proof` for
another, so each target directory carries its own copy.

### Assembling one unit

`data/target.jsonl` exists because `materialize-units` replaces the proof of
*every* theorem record it receives. Pass it the target file — not the whole
closure — so the target is the only hole:

```bash
cd ../reassemble
lake exe lean_reassemble materialize-units \
    --source-root ../../sqlite \
    --records     ../lean-extract/decl-out/LeanSQLite.Btree.insert_sound/data/target.jsonl \
    --output      /tmp/insert-sound-unit
```

That yields one standalone task, verified by invoking `lean` directly against a
pristine `.olean` cache. The rest of the closure is the **context payload** — the
premise statements and proofs available to whatever fills the hole, with
`closure_role` separating what states the target from what its original proof
used.

Passing `theorems/train.jsonl` instead would sorry the premise lemmas too. The
result still typechecks through `sorryAx`, but the premises the target is meant
to build on have themselves become holes.

Unit assembly needs the same source checkout the records came from: the
reassembler verifies each record's module, name, position, and `body` against the
elaborated source and fails rather than guessing if they drifted.

Adding `--proofs keep` writes the proofs back verbatim instead of holing them out,
giving a compilable reference state for the same records — useful as an
intermediate checkout, or as the oracle to diff a sorried artifact against. See
[Proof Modes](../reassemble/README.md#proof-modes).

### Cost

Closure size is not bounded — a deep theorem can reach most of the project, so
this mode is not inherently fast. The way to amortize is to pass several `--decl`
flags in **one** invocation: the union of needed files is elaborated once and each
target is projected out of the shared record pool. Batching beats repeated runs.

`--resume` does not make separate invocations cheap: a successful run removes its
`.shards/` staging, so resume only helps after an *interrupted* run.

`--reverse-elab` applies per file, so it multiplies cost by the closure's file
count even though usually only the target's `proof_script` is wanted.

### Caveats

- `--no-private` leaves structurally incomplete closures: proofs routinely use
  `private` lemmas that imports cannot recover. The mode warns.
- Constructors, recursors, projections, generated companions, and
  equation-compiler helpers appear in a closure but never have records — on a real
  proof they outnumber the emitted records. They are classified by reason and
  summarized in one line, with per-category names in `dropped.json`:

  ```
  corpus-extract: closure for LambdaCalc.Term.church_rosser: 83 member(s) not
  representable as records (15 constructors, 9 equation_compiler_helpers, 42
  generated_companions, 2 noConfusion_stubs, 13 recursors, 2
  synthetic_theorems); see dropped.json
  ```

  Only the `unexplained` category signals a problem (eligible, but no record was
  produced); it gets its own warning and sorts first. `--strict-closure` makes any
  drop an error.
- A target in an orphan file (one no root module imports) is rejected — check
  `--list-orphans`.
- Mutually exclusive with the grind modes, `--proof-states`, and
  `--list-orphans`; `--split-by-tag` and `--dataset-card-config` are rejected as
  meaningless per-target.

## Proof-state mode

`--proof-states` captures the **interior** of every tactic proof. The corpus's two
proof representations are both whole-proof — `body` is a source slice,
`proof_script` is a reverse-elaborated string — so neither can express *given this
goal, the author applied this tactic, and the goal became that*. This mode does.

```bash
./.lake/build/bin/lean_extract \
    --modules      LambdaCalc \
    --source-root  ../LambdaCalc \
    --proof-states \
    --output       ./ps-out
```

```text
ps-out/
  metadata.json                      # mode: "proof-states", run counters
  data/proof-states/train.jsonl      # one record per tactic-proved theorem
```

One record per theorem, joining to the `theorems` config by `name`:

| Field | Meaning |
|---|---|
| `steps` | The tactic tree. Each step: verbatim `tactic` text, `tactic_kind`, line/col **and byte** range, `goals_before` / `goals_after`, `invocations`, and `children`. |
| `goals` | Interned goal table. Each goal: `hyps` (`names`/`type`/`value`/`is_let`), `target`, and a `pretty` block. Steps reference goals by index. |
| `initial_goals` | The state the proof opened in — always goal `0`. |
| `parent_decl` | For a `where` / `let rec` **auxiliary**, the enclosing declaration; `null` for a top-level theorem. An auxiliary is a separately-checked constant and gets its own record — often it is the substantive lemma, the parent's proof being one `exact`. |
| `proof_source`, `proof_start_byte`, `proof_end_byte` | The proof's verbatim text and file byte span. |
| `step_count`, `max_depth`, `tactic_kinds` | Shape summary, for filtering without walking. |
| `outcome` | `ok` / `skipped_large` / `deadline_skipped` / `error`. Non-`ok` means `steps` is empty. |

Combinators become **parent** steps whose children are the tactics they composed,
so `induction … with`, `<;>`, `all_goals`, and `·` keep their source structure. A
combinator that re-runs one tactic per goal yields a single step with
`invocations > 1` and the union of the goals it ran on.

Each step's byte offsets locate it inside the corpus schema without re-elaborating:

```text
step.start_byte - record.proof_start_byte  =  offset within ConstRecord.body
```

Theorems proved by a bare term (`:= rfl`) have no tactics; they are **counted**
(`theoremsTermProved`), not emitted as empty rows.

On `ProofBenchData/generated/LambdaCalc` (11 files): 64 records, 480 steps (max 53
in one theorem), 447 distinct goals from 735 references, depth up to 5, 511 KB, no
errors and no unhandled-form warnings.

Mutually exclusive with `--decl` and the grind modes. `--resume` does not apply.
Design and validation: [`docs/proof-state-extraction.md`](../docs/proof-state-extraction.md).

## Architecture

Everything is one package; `lean-extract` hosts Lean's frontend directly:

```
 lean-extract
 ├─ Corpus/Main.lean            CLI parsing; --enumerate branch; JSONL pipeline
 ├─ Corpus/Discover.lean        orphan-safe file discovery (walk, prune .lake/, path↔Name)
 ├─ Corpus/Frontend.lean        elaborate one file through Lean's frontend
 │                              (parseHeader→processHeader→IO.processCommands), run a
 │                              CoreM collector on the resulting environment
 ├─ Corpus/CollectCommon.lean   shared collector helpers (kindToString, isUserConstant)
 ├─ Corpus/Artifact.lean        artifact conventions shared with reassemble
 ├─ Corpus/CorpusManifest.lean  the corpus collector (corpusManifestCore)
 ├─ Corpus/DeclClosure.lean     --decl mode: the driver sequencing its two phases
 ├─ Corpus/DeclClosure/Cone.lean   phase 1: resolve targets, both cones, drop
 │                                 classification, file selection (import-only env)
 ├─ Corpus/DeclClosure/Emit.lean   phase 2: order, project, render, write
 ├─ Corpus/GrindManifest.lean   the grind-manifest collector (grindManifestCore)
 ├─ Corpus/GrindInProof.lean    the in-proof grind collector (grindInProofCore)
 ├─ Corpus/ProofStates.lean     --proof-states: the InfoTree walk, tree algebra,
 │                              goal rendering + interning (proofStatesCore)
 ├─ Corpus/ReverseElab.lean     proof-term → verified tactic script
 ├─ Corpus/WorkerExtract.lean   isolated/shared driver, resume staging, record mapping
 ├─ Corpus/GrindExtract.lean    the grind-manifest driver
 ├─ Corpus/GrindInProofExtract.lean  the in-proof grind driver
 ├─ Corpus/ProofStatesExtract.lean   the proof-state driver
 ├─ Corpus/Extract.lean         the legacy import-and-walk backend (--enumerate=import)
 ├─ Corpus/Records.lean         the ConstRecord / grind / proof-state schemas + encoders
 ├─ Corpus/Tags.lean            tag-rule matching
 └─ Corpus/Card.lean            HF dataset-card rendering
```

### The frontend path (default)

1. **Discover** (`Discover.lean`): walk the project tree, prune `.lake/`, map each
   `.lean` file to its module `Name`, keep those under the `--modules` roots.
2. **Drive** (`WorkerExtract.lean` → `Frontend.lean`): by default, files run in
   bounded batches of isolated child processes. `--no-isolate-files` instead uses
   `elaborateFiles` in one process, warming external imports before parallel work
   and serializing each file's import phase. In either mode, `elaborateFile` does
   `parseHeader` → `processHeader` → `IO.processCommands`, yielding the final
   `Environment`, command `Syntax`, and `InfoTree`s.
3. **Collect** (`CorpusManifest.lean` via `Frontend.runCollectorOn`): fold over the
   module-local user constants in the post-elaboration environment. Per constant it
   computes the type/value (pretty-printed), `deps`, `axioms`, `premises`
   (transitive owned cone), `signature`/`body` (by navigating the parsed command
   `Syntax`), and — when requested — the reverse-elaborated `proof_script`. An
   eligibility filter matches the dataset's record set.
4. **Map & write** (`WorkerExtract.lean` → `Main.lean`): each
   `CorpusManifestEntry` becomes a `ConstRecord`; the shared pipeline splits and
   writes the JSONL.

**Why this design.** Driving the frontend directly runs each file in its real
elaboration context, with registered tactics and project options,
which is what makes in-context source reconstruction and `proof_script`
re-elaboration possible, and finds orphan files the import graph misses. The
import-based path cannot reproduce that context, so it is kept only as a
`--enumerate=import` fallback. (This replaced an earlier `lean --worker` +
LSP-plugin design; the collector logic is unchanged, only its host.)

#### Timeouts

With `--reverse-elab`, isolated mode enforces a hard per-file deadline and, where
process groups are supported, kills the full worker group on expiry. It retries
baseline extraction without reverse elaboration under the same deadline. Reverse
elaboration also applies proof-size filters, heartbeat limits, and per-theorem
child-process bounds. `--no-isolate-files` has no hard file-level process
deadline, so its per-file tail bound remains cooperative.

### Reverse-elaboration / proof simplification

The `proof_script` field is produced by `Corpus.ReverseElab`, which turns
a proof *term* (`Expr`) into a short, **verified** tactic script. Its algorithm
— the candidate ladder, the two-stage verification, and the soundness guards
that keep `sorry`-laced scripts out — is documented separately in
[`workers/docs/proof-simplification.md`](../workers/docs/proof-simplification.md).

## Tags config

A JSON file of substring rules; each rule matching a constant's module name
contributes `(key, value)` tags to that record.

```json
{
  "rules": [
    { "match": "LeanSQLite.Btree",   "tags": { "workstream": "B" } },
    { "match": "LeanSQLite.Storage",  "tags": { "workstream": "C+T" } }
  ]
}
```

`match` is a plain substring test against the dotted module name (no globs/regex).

## Pushing to the Hub

The extractor never pushes. After a run, upload the output directory as-is:

```bash
huggingface-cli upload <user>/<dataset> <output> . --repo-type dataset
```
