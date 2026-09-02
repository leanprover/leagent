# Lean Corpus Reassembly

`lean_reassemble` turns extraction JSONL records back into Lean artifacts. It
has three commands:

```bash
lake exe lean_reassemble rewrite-file \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --file <project-relative.lean> \
  --output <rewritten.lean> \
  [--proofs sorry|keep|delete] [--manifest <manifest.json>] \
  [--on-failure fail|skip|backoff]

lake exe lean_reassemble materialize-repo \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --output <artifact-dir> \
  [--build-target <target>] [--proofs sorry|keep|delete] \
  [--manifest <manifest.json>] [--on-failure fail|skip|backoff] [--keep-eval]

lake exe lean_reassemble materialize-units \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --output <artifact-dir> \
  [--build-target <target>] [--proofs sorry|keep|delete] \
  [--manifest <manifest.json>] [--on-failure fail|skip|backoff]
```

Run these from `leagent/reassemble`. The source root must be a Lake project with
`lake-manifest.json`; artifact output must not already exist and must be outside
the source root.

## Records

The reassembler consumes extraction JSONL records. For repository or unit
materialization, pass records for one source project at a time. The records file
must contain theorem records with `file`, `module`, `name`, and source location
metadata matching the source checkout.

`materialize-units` emits one task per theorem record, each holing only its own
target. `materialize-repo` differs: it holes **every** record in one artifact, so
pass it only the theorems you want sorried.

## Proof Modes

`--proofs` sets the default action for every selected theorem:

| Mode | Effect |
|---|---|
| `sorry` (default) | Replace the proof with `by sorry` — the training/eval artifact. |
| `keep` | Preserve the proof verbatim — the compilable **reference state**. |
| `delete` | Erase the whole declaration (doc comment, attributes, signature, value). |

`delete` does **no dependency analysis**: removing a theorem that other
declarations reference will break the build. Keeping the manifest consistent is the
caller's responsibility.

`keep` is not a bypass. It runs the identical pipeline — match each record to
exactly one declaration, obtain the proof range from parsed `Syntax`, check the
recorded `body` against the source — and then writes the original text back
instead of a `sorry`. The output is byte-identical to the source, which is what
makes it meaningful: a wrong range would splice back the wrong slice, so an
identical result is evidence the extraction agrees with the source.

Two uses:

- **Intermediate compilable state.** Get a buildable checkout corresponding to an
  extractor run, before any proofs are holed out.
- **Diff oracle.** Materialize the same records twice and diff. Every differing
  hunk is a replaced proof and nothing else, which validates a sorried artifact:

  ```bash
  lake exe lean_reassemble materialize-repo --source-root ../proj \
    --records t.jsonl --output /tmp/ref --proofs keep
  lake exe lean_reassemble materialize-repo --source-root ../proj \
    --records t.jsonl --output /tmp/holed
  diff -r --exclude=.lake --exclude=rewrite-report.json \
    /tmp/ref/repos/proj /tmp/holed/repos/proj
  ```

Under `keep`, unit verification is *stricter*: `sorry` warnings are permitted in
`sorry` mode (the target is expected to warn) but rejected in `keep` mode, since a
preserved artifact should compile with no diagnostics at all.

`rewrite-report.json` and `manifest.json` record the mode, and the buckets report
the resolved action of each theorem — so a run that mixes actions (via a manifest)
is reflected faithfully:

```json
{ "proof_mode": "keep", "eligible": 104, "replaced": 0,
  "preserved": 104, "deleted": 0, "skipped": 0, "failed": 0, "failures": [] }
```

`failures` names each theorem behind the `skipped`/`failed` counts, so a best-effort
run is auditable rather than only tallied (it is empty under `--on-failure fail`):

```json
"failures": [
  { "theorem": "Project.Term.preservation", "action": "skipped",
    "reason": "theorem record did not match a declaration: Project.Term.preservation" }
]
```

## Per-Theorem Manifest

`--manifest <path>` is a **sparse override** on top of `--proofs`. It names only the
theorems whose action differs from the default; every theorem it does not mention
follows `--proofs`. An empty manifest is a no-op.

```json
{
  "format": "lean-reassemble-manifest.v1",
  "theorems": {
    "Project.Foo.helper":   "keep",
    "Project.Foo.scratch":  "sorry",
    "Project.Foo.deadLemma": "delete"
  }
}
```

Keys are full theorem names (the same names the records carry); values are
`keep | sorry | delete`. A key that matches no theorem in the records is a hard
error, to catch typos.

Deleting a theorem that a surviving declaration still references would break the
build. `materialize-repo` and `materialize-units` detect this from the records'
`deps` **before** building and fail with the offending `dependent -> deleted`
pairs named, rather than deferring to an opaque `lake build` error (a
`--proofs sorry` dependent is safe — its proof, and the references in it, are
holed out). For the full account of which parameter combinations are supported,
degenerate, or rejected — including the manifest's neighbour-pruning role in
units mode — see [`docs/parameter-matrix.md`](../docs/parameter-matrix.md).

## Failure Policy

`--on-failure` controls what happens when a theorem cannot be reassembled — it does
not match a declaration, its recorded body disagrees with the source, or (in units
mode) the artifact it produces does not verify:

| Policy | Effect |
|---|---|
| `fail` (default) | Abort the whole run on the first failure. |
| `skip` | Omit the failing theorem and record it in `skipped`. |
| `backoff` | Delete the failing theorem, record it in `failed`, and continue. |

Under `skip`, repo mode leaves the failing theorem's **original proof in place**
(its edit is simply not applied), so under `--proofs sorry` that proof stays real;
units mode emits no task for it. Under `backoff`, the theorem is deleted — a record
that matches no declaration has nothing to delete, so it falls through to a skip.

### Auxiliary declarations (excluded, not failed)

A `where`/`let rec` proof helper, or a member of a `mutual … end` block, is lifted by
Lean into its own kernel constant — so the extractor emits a record for it — but it
has **no standalone command syntax**: it is written inside its parent declaration.
The reassembler cannot (and need not) hole such a constant on its own — under `keep`
it rides along inside its parent's preserved proof, and under `sorry`/`delete` the
parent's edit already erases the whole body it lives in. These records are therefore
classified **auxiliary**: excluded from the target set and counted in `auxiliary`,
*not* reported as failures. So a project using `where`-helpers reassembles cleanly
under the default `--on-failure fail`. This is distinct from a record that matches no
declaration at all (source/extraction drift), which stays a genuine failure.

`skip`/`backoff` recover from **planning** failures. A post-rewrite `lake build`
break in `materialize-repo` still aborts regardless of policy: such a break is
almost always at a *dependent* of a holed or deleted theorem, not at that theorem,
so there is no safe declaration to auto-attribute and remove.

## Evaluation Commands and `--keep-eval`

Lean refuses to evaluate an expression that transitively depends on `sorry`
("Aborting evaluation since the expression depends on the 'sorry' axiom"). So a
`#eval` / `#eval!` / `#reduce` / `#guard` / `#guard_msgs` that reaches a holed proof
— even indirectly, through an import — turns into a hard build error the moment a
proof is holed. This most often bites an `Examples.lean` full of `#eval`/`#guard_msgs`
anti-vacuity checks.

`materialize-repo` therefore **strips these evaluation commands by default** whenever
the run holes or deletes at least one proof. Stripping erases only the evaluation
commands (a `#guard_msgs` block is removed together with its `/-- info: … -/`
docstring); every `theorem` and `def` — including those living beside the evals in
an `Examples` module — is kept and holed as usual, so no theorem is lost from the
artifact. A pure `--proofs keep` run holes nothing and so never strips. Each strip is
reported per file in `rewrite-report.json` as `eval_stripped`.

Pass `--keep-eval` to preserve the evaluation commands verbatim (the historical
behavior); under `--proofs sorry` this reproduces the build break above, so it is
mainly useful with `--proofs keep`.

## Repository Artifacts

`materialize-repo` creates:

```text
<artifact-dir>/
  manifest.json
  repos/<project-name>/
    <normal Lake project>
    rewrite-report.json
```

It copies the source project, removes `.git` and `.lake`, rewrites every theorem
body in the provided records to `by sorry` (or preserves them under
`--proofs keep`), then runs `lake build` or `lake build <target>`.

Example:

```bash
cd /path/to/leagent/reassemble

lake exe lean_reassemble materialize-repo \
  --source-root /path/to/source-project \
  --records /path/to/project-theorems.jsonl \
  --output /tmp/project-repo
```

The result should build as an ordinary Lake project:

```bash
cd /tmp/project-repo/repos/<project-name>
lake build
```

## Unit Artifacts

`materialize-units` creates one standalone **Lake project** per theorem record,
all sharing one immutable cache:

```text
<artifact-dir>/
  manifest.json
  cache/                                     # shared, immutable, required by every unit
    environment.json                         # toolchain, git hash, ordered search paths
    siblings/                                # a stub Lake package that requires every root
      lakefile.lean  lean-toolchain  lake-manifest.json
    roots/<n>/                               # one stub Lake package per LEAN_PATH root
      lakefile.lean  lean-toolchain  lake-manifest.json
      .lake/build/lib/lean/...               # that root's prebuilt oleans
    native/<n>/...                           # native libraries (direct-lean fallback)
  units/
    <task-id>/
      lakefile.lean                          # requires ../../cache/siblings
      lean-toolchain
      <original-relative-path>.lean          # the one holed module
      task.json
```

Each task is a proof problem for **one** theorem. Its source is the complete
original module with only *that* theorem's proof replaced by `by sorry`; every
other declaration in the module keeps its real proof, including lemmas the target
depends on. Two tasks from the same module therefore differ, each holing its own
target.

The whole module is retained rather than extracting the theorem alone because
private names, section variables, notation, and options are not reproducible in a
fresh file — see [`docs/corpus-reassembly.md`](../docs/corpus-reassembly.md).

Under `--proofs keep` nothing is holed, so every task from a given module is the
same (unmodified) file; keep mode is usually more useful with `materialize-repo`.

**The primary contract is `lake build`.** A unit is an ordinary Lake project: it
resolves its imports from the shared cache through a single `require` of
`cache/siblings`, which transitively requires every `cache/roots/<n>` package in
the pristine `LEAN_PATH` order. To check or work on a task, just build it:

```bash
cd <artifact-dir>/units/<task-id>
lake build          # compiles the holed module against the shared cache
```

Nothing else rebuilds, and a unit's build **cannot mutate the shared cache**: the
root packages declare `roots := #[]`, so Lake schedules no work in them and only
ever reads the prebuilt oleans placed there at materialization. Two units can build
concurrently against the same cache. The whole artifact is relocatable — every path
in the generated lakefiles and manifests is relative — so it can be moved or mounted
as long as `units/` and `cache/` keep their relative positions.

The materializer builds a pristine copy of the source project first, generates the
cache packages (pre-warming their Lake manifests so unit builds are warning-free),
copies each `LEAN_PATH` root's oleans into its stub package, then verifies each task
by running `lake build` in it exactly as a consumer would. The unit's own
`.lake/` build directory and resolved `lake-manifest.json` are stripped afterward so
the shipped unit is minimal; a consumer's first `lake build` regenerates them.

Each source file is elaborated once and reused across all of its targets, so the
per-task cost is a byte-splice plus one `lake build`. Expect roughly a second per
task: 104 theorems over 10 files took about two minutes.

Example:

```bash
cd /path/to/leagent/reassemble

lake exe lean_reassemble materialize-units \
  --source-root /path/to/source-project \
  --records /path/to/project-theorems.jsonl \
  --output /tmp/project-units
```

## Single-Theorem Units

`lean-extract --decl <Name>` extracts one theorem plus its dependency closure and
writes the target record on its own to `data/target.jsonl`. Passing that file here
produces exactly one task, for that theorem:

```bash
# 1. Extract one theorem's closure.
cd /path/to/leagent/lean-extract
./.lake/build/bin/lean_extract \
  --modules     Project \
  --source-root ../../source-project \
  --decl        Project.Btree.insert_sound \
  --output      ./decl-out

# 2. Materialize it as a single unit.
cd ../reassemble
lake exe lean_reassemble materialize-units \
  --source-root ../../source-project \
  --records     ../lean-extract/decl-out/Project.Btree.insert_sound/data/target.jsonl \
  --output      /tmp/insert-sound-unit
```

The remaining files in that closure directory — `theorems/train.jsonl`,
`definitions.jsonl`, and `metadata.json` — are context for whatever fills the hole,
not materialization input. Each record's `closure_role` says whether it is needed
to state the target or was used only by its original proof.

Passing `theorems/train.jsonl` instead is also safe — each emitted task holes only
its own target — but it produces one task per closure member rather than the single
task you probably want. See
[`docs/single-decl-extraction.md`](../docs/single-decl-extraction.md).

## Replaying A Unit

The primary way to run a task is to build it as the Lake project it is:

```bash
ARTIFACT=/tmp/project-units
TASK="$(find "$ARTIFACT/units" -mindepth 1 -maxdepth 1 -type d | sort | head -n 1)"

cd "$TASK" && lake build
```

`task.json` records the exact toolchain pin, so the portable form is:

```bash
elan run "$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["toolchain"])' "$TASK/task.json")" \
  lake build
```

The unit's `lakefile.lean` requires `../../cache/siblings`, which transitively
requires every `cache/roots/<n>` package in order — so Lake reconstructs the
pristine `LEAN_PATH` itself. Every path is relative, so a unit builds wherever
`units/` and `cache/` keep their relative positions.

### Direct-`lean` fallback

`task.json` also records `lean_path` and `ld_library_path` (relative to the
artifact root) for consumers that would rather invoke `lean` directly, without
Lake. Point `LEAN_PATH`/`LD_LIBRARY_PATH` at those cache roots, in order, and use
the unit directory as the `-R` root:

```bash
SOURCE="$(python3 -c 'import json;print(json.load(open("'"$TASK"'/task.json"))["source"])')"

export LEAN_PATH="$(python3 -c 'import json;print(":".join(json.load(open("'"$ARTIFACT"'/cache/environment.json"))["lean_path"]))')"
export LD_LIBRARY_PATH="$(python3 -c 'import json;print(":".join(json.load(open("'"$ARTIFACT"'/cache/environment.json"))["ld_library_path"]))')"

# LEAN_PATH/LD_LIBRARY_PATH entries are artifact-relative; resolve against $ARTIFACT.
( cd "$ARTIFACT" && lean -R "$TASK" "$ARTIFACT/$SOURCE" )
```

The `lean` you use must be the toolchain the cache was built with, or the
`.olean`s are rejected with `incompatible header`.

For a dataset consumer, the durable contract is:

- read `cache/environment.json` for the toolchain, Lean git hash, ordered
  `lean_path`, and ordered `ld_library_path`;
- either `lake build` the unit (which uses the in-tree cache via `require`), or
  resolve those paths relative to the artifact root — or to an equivalent external
  cache — and run `lean -R <task> <task>/<source>` with those variables.

Do not merge cache roots. Lake order is significant; two dependencies may expose
the same module path — which is exactly why the cache keeps one package per root
and requires them in order.

## Notes

- `rewrite-file` is a surgical single-file helper. It validates the rewritten
  document with the Lean worker before writing output.
- `materialize-repo` is the whole-project correctness oracle because it rebuilds
  the rewritten Lake project.
- `materialize-units` produces one standalone Lake project per theorem for
  training/evaluation datasets. Each is verified with `lake build` against a
  shared, immutable cache of prebuilt oleans, so the per-task cost stays a
  byte-splice plus one build.
- For projects with external dependencies, network access may be needed the
  first time Lake recreates `.lake/packages` in the materialized pristine copy;
  the shared cache is then built from that copy and needs no further network.
