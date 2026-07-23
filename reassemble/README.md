# Lean Corpus Reassembly

`lean_reassemble` turns extraction JSONL records back into Lean artifacts. It
has three commands:

```bash
lake exe lean_reassemble rewrite-file \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --file <project-relative.lean> \
  --output <rewritten.lean>

lake exe lean_reassemble materialize-repo \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --output <artifact-dir> \
  [--build-target <target>]

lake exe lean_reassemble materialize-units \
  --source-root <lake-project> \
  --records <records.jsonl> \
  --output <artifact-dir> \
  [--build-target <target>]
```

Run these from `leagent/reassemble`. The source root must be a Lake project with
`lake-manifest.json`; artifact output must not already exist and must be outside
the source root.

## Records

The reassembler consumes extraction JSONL records. For repository or unit
materialization, pass records for one source project at a time. The records file
must contain theorem records with `file`, `module`, `name`, and source location
metadata matching the source checkout.

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
body in the provided records to `by sorry`, then runs `lake build` or
`lake build <target>`.

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

`materialize-units` creates one standalone task per theorem record:

```text
<artifact-dir>/
  manifest.json
  cache/
    environment.json
    roots/<n>/...
    native/<n>/...
  units/
    <task-id>/
      src/<original-relative-path>.lean
      task.json
```

Each task source is the complete original module with all theorem bodies from
the selected records replaced by `by sorry`. The materializer builds a pristine
copy of the source project first, copies the required `LEAN_PATH` and native
library roots into `cache/`, and verifies each task with Lean directly.

Example:

```bash
cd /path/to/leagent/reassemble

lake exe lean_reassemble materialize-units \
  --source-root /path/to/source-project \
  --records /path/to/project-theorems.jsonl \
  --output /tmp/project-units
```

## Replaying A Unit

`task.json` records the intended direct Lean command and cache metadata. A task
can be run from any location as long as `LEAN_PATH` and `LD_LIBRARY_PATH` point
at the artifact cache roots in order:

```bash
ARTIFACT=/tmp/project-units
TASK="$(find "$ARTIFACT/units" -mindepth 1 -maxdepth 1 -type d | sort | head -n 1)"
SOURCE="$(find "$TASK/src" -type f -name '*.lean' | sort | head -n 1)"

export LEAN_PATH="$(find "$ARTIFACT/cache/roots" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd: -)"
export LD_LIBRARY_PATH="$(find "$ARTIFACT/cache/native" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | sort | paste -sd: -)"

lean -R "$TASK/src" "$SOURCE"
```

For a dataset consumer, the durable contract is:

- read `cache/environment.json` for the toolchain, Lean git hash, ordered
  `lean_path`, and ordered `ld_library_path`;
- resolve those paths relative to the artifact root, or replace them with paths
  to an equivalent external cache;
- run `lean -R <task>/src <task>/src/<source>` with those environment variables.

If the dataset stores cache separately from tasks, keep the same root order.
For example, with a shared cache mounted at `/datasets/proofbench/cache`:

```bash
ARTIFACT=/datasets/lean-corpus/project-units
CACHE=/datasets/lean-corpus/cache
TASK="$(find "$ARTIFACT/units" -mindepth 1 -maxdepth 1 -type d | sort | head -n 1)"
SOURCE="$(find "$TASK/src" -type f -name '*.lean' | sort | head -n 1)"

export LEAN_PATH="$CACHE/roots/0:$CACHE/roots/1"
export LD_LIBRARY_PATH="$CACHE/native/0"

lean -R "$TASK/src" "$SOURCE"
```

Do not merge cache roots. Lake order is significant; two dependencies may expose
the same module path.

## Notes

- `rewrite-file` is a surgical single-file helper. It validates the rewritten
  document with the Lean worker before writing output.
- `materialize-repo` is the whole-project correctness oracle because it rebuilds
  the rewritten Lake project.
- `materialize-units` is for training/evaluation datasets where each theorem is
  consumed independently but imports are resolved from the copied pristine cache.
- For projects with external dependencies, network access may be needed the
  first time Lake recreates `.lake/packages` in the materialized copy.
