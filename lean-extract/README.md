# lean-extract

A Lean 4 **corpus extractor**: it walks a Lean project and emits a JSONL dataset
— one record per theorem/definition — capturing the type, value, source
signature and body, dependencies, transitive premises, axioms, and a verified
reverse-elaborated tactic `proof_script`. The output is laid out for direct
upload as a HuggingFace dataset (modeled after NuminaMath-LEAN with LeanDojo-style
premise tracking).

The tool is **project-agnostic**: the modules to extract, the source root, and
any tagging rules are all supplied on the command line.

## Two ways it runs

`lean-extract` has two extraction backends, selected with `--enumerate`:

- **`glob` (default)** — the **worker/frontend** path. The tool discovers the
  project's source files on disk, drives a pool of `lean --worker` subprocesses
  (one real frontend elaboration per file), and pulls structured per-declaration
  data back over LSP from a Lean **plugin**. This sees each file in its *true
  elaboration context* (section variables, `open`s, `set_option`s, registered
  tactics) and finds **orphan** declarations in files that no other module
  imports.
- **`import` (fallback)** — the legacy path: `importModules` the root modules
  and walk the resulting `Environment`. Needs no worker/plugin, but cannot
  reconstruct source signatures/bodies (its byte-slicer was removed in the 4.31
  port) and misses orphan files.

Both backends write the **same JSONL schema**, so datasets stay comparable.

> The extraction logic lives in a sibling package, `workers` (the Lean plugin
> `WorkerPlugins.CorpusManifest` and the reverse-elaborator
> `WorkerPlugins.ReverseElab`). `lean-extract` `require`s it. See
> [Architecture](#architecture) below.

## Build

```bash
# 1. Build the worker-side plugin .so files (the glob path loads these).
cd ../workers
lake build WorkerPlugins.CorpusManifest:dynlib \
           WorkerPlugins.ReverseElab:dynlib \
           WorkerPlugins.Common:dynlib

# 2. Build the extractor binary.
cd ../lean-extract
lake build
```

The binary lands at `.lake/build/bin/lean_extract`. The plugin `.so`s land at
`../workers/.lake/build/lib/lean/workers_WorkerPlugins_*.so`; the extractor
locates them automatically (override with `LEAN_EXTRACT_PLUGIN_DIR`).

Toolchain: both packages pin Lean **4.31.0** via `lean-toolchain`.

## Run

The workers (glob mode) and the importer (import mode) both need `LEAN_PATH`
pointing at the project-under-study's built `.olean`s. The tool handles this: if
`--source-root` (or the current directory) is a Lake project, it re-execs itself
under `lake env` from there, so spawned workers inherit the right search path.
You never need to wrap the call in `lake env` yourself.

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
| `--enumerate glob\|import` | no | Extraction backend. Default `glob` (worker path). `import` is the legacy Environment walk. |
| `--list-orphans` | no | Print the modules on disk (under `--modules`) that are **not** in the import closure of the roots, then exit. A diagnostic — writes no dataset. |
| `--source-root <dir>` | no | Project root: resolves module↔file paths and triggers the `lake env` re-exec. Defaults to `.`. |
| `--config <path>` | no | Tags-config JSON (see [Tags](#tags-config)). Default: no tags. |
| `--reverse-elab` | no | Reverse-elaborate each theorem's proof term into a verified tactic `proof_script`. **Off by default** — it re-elaborates every proof (slower). |
| `--closers` | no | With `--reverse-elab`, also try goal-closing tactics (`simp`/`omega`/…) to recover high-level proofs for automation-heavy bodies. ~20× slower; off by default. |
| `--include-internal` | no | Emit compiler-internal names (`_aux.*`, `match_*`, constructors, recursors). Default: false. |
| `--no-private` | no | Skip `private` declarations. Default: include them. |
| `--split-by-tag <key>` | no | Stratified 80/10/10 train/valid/test split of theorems keyed on a tag value. Definitions are always one split. |
| `--seed <n>` | no | Deterministic split seed (default 0). |
| `--dataset-card-config <path>` | no | JSON describing dataset identity; generates the HF dataset card (`README.md`). |
| `--help`, `-h` | no | Print usage and exit. |

### Examples

```bash
# Default worker-driven extraction.
lean_extract --modules LeanSQLite --source-root ../sqlite --output ./out

# With verified proof scripts (slower).
lean_extract --modules LeanSQLite --source-root ../sqlite --output ./out --reverse-elab

# Find files no imported module pulls in.
lean_extract --modules LeanSQLite --source-root ../sqlite --list-orphans

# Legacy import-based path (no workers; signature/body will be null).
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

## Architecture

The system spans two Lake packages:

```
 lean-extract  (this package — the CLI / dataset writer)
 ├─ Corpus/Main.lean          CLI parsing; --enumerate branch; JSONL pipeline
 ├─ Corpus/Discover.lean      orphan-safe file discovery (walk, prune .lake/, path↔Name)
 ├─ Corpus/WorkerExtract.lean the worker-pool driver + CorpusManifestEntry → ConstRecord
 ├─ Corpus/Extract.lean       the legacy import-and-walk backend (--enumerate=import)
 ├─ Corpus/Records.lean       the ConstRecord JSONL schema + encoder
 ├─ Corpus/Tags.lean          tag-rule matching
 └─ Corpus/Card.lean          HF dataset-card rendering
        │  require workers from "../workers"
        ▼
 workers  (the worker/plugin infrastructure — the extraction logic)
 ├─ Workers/Worker.lean       drive one `lean --worker`: spawn, LSP send/await, shutdown
 ├─ Workers/WorkerPool.lean   LRU pool of workers keyed by file URI
 ├─ WorkerPlugins/Common.lean shared plugin scaffolding (snapshot/CoreM plumbing)
 ├─ WorkerPlugins/CorpusManifest.lean  the corpus plugin ($/lean/corpusManifest)
 └─ WorkerPlugins/ReverseElab.lean     proof-term → verified tactic script
```

### The worker/frontend path (default)

1. **Discover** (`Discover.lean`): walk the project tree, prune `.lake/`, map each
   `.lean` file to its module `Name`, keep those under the `--modules` roots.
2. **Drive** (`WorkerExtract.lean`): build a `WorkerPool`. For each file:
   `acquire` a worker (spawns `lean --worker` with the plugin loaded, sends
   `initialize` + `didOpen`), `waitForDiagnostics` (elaboration done), then send
   the custom LSP request `$/lean/corpusManifest` and decode the response.
3. **Extract** (`CorpusManifest.lean`, *inside the worker*): after the file's
   command snapshots finish, fold over the module-local user constants in the
   post-elaboration environment. Per constant it computes the type/value
   (pretty-printed), `deps`, `axioms`, `premises` (transitive owned cone),
   `signature`/`body` (by navigating the parsed command `Syntax`), and — when
   requested — the reverse-elaborated `proof_script`. A server-side
   eligibility filter matches the dataset's record set.
4. **Map & write** (`WorkerExtract.lean` → `Main.lean`): each
   `CorpusManifestEntry` becomes a `ConstRecord`; the shared pipeline splits and
   writes the JSONL.

**Why this design.** The LSP boundary quarantines version-fragile InfoTree/Core
code inside the plugin, while the driver consumes stable JSON. Crucially, the
worker is a *real frontend* — tactics are registered and the elaboration context
is authentic — which is what makes in-context source reconstruction and
`proof_script` re-elaboration possible. The import-based path cannot reproduce
that context, so it is kept only as a `--enumerate=import` fallback.

#### Plugin `.so` loading (gotcha)

Each plugin `.so` references the `initialize` symbols of the shared helpers it
imports (`Common`, `ReverseElab`) as *undefined* — they are not statically
bundled. The worker must therefore `--load-dynlib` **every helper** before
`--plugin`-loading the handler:

```
lean --worker \
  --load-dynlib=…workers_WorkerPlugins_Common.so \
  --load-dynlib=…workers_WorkerPlugins_ReverseElab.so \
  --plugin=…workers_WorkerPlugins_CorpusManifest.so \
  file://…
```

(`--plugin` loads *and runs* the `initialize` block that registers the LSP
handler; `--load-dynlib` only exposes symbols.) `WorkerExtract.resolvePluginArgs`
assembles these flags.

### Reverse-elaboration / proof simplification

The `proof_script` field is produced by `WorkerPlugins.ReverseElab`, which turns
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
