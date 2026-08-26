# Reassembling Lean Corpus Snapshots

## Goals

A corpus snapshot should support two different products:

1. **Independent units**: each theorem task is a standalone Lean input. It can
   be checked by invoking `lean` directly with a matching, ordered `LEAN_PATH`.
   The output does not need to be a Lake package.
2. **Restored repositories**: each pinned repository is checked out in its
   original layout, with every extracted theorem body replaced by `sorry`.
   The repository remains a normal Lake project.

Both products must come from the same immutable snapshot and use the same
source-rewrite implementation. They differ in layout and build semantics.

## Agent Handoff

This section is the implementation contract for an agent starting work in the
`leagent` repository. The rest of this document describes the complete design;
the first change must remain intentionally smaller.

### Repository Placement

Add a third top-level Lake package:

```text
leagent/
  lean-extract/
  workers/
  reassemble/
    lakefile.lean
    lean-toolchain
    LeanReassemble/
    LeanReassemble.lean
```

The package should declare relative path dependencies on `../lean-extract` and
`../workers`, expose a `LeanReassemble` library, and build a
`lean_reassemble` executable. Use the same Lean toolchain as both existing
packages.

Do not add Lean-aware rewriting to a dataset or storage consumer. `leagent`
owns generic Lean source processing; callers provide local snapshot manifests,
records, and source projects through stable file formats.

### First Milestone

Implement one end-to-end `rewrite-file` vertical slice. It must:

1. read one extraction JSONL file and select theorem records for one requested
   source file;
2. elaborate that source file through `Corpus.Frontend`;
3. match each selected record to exactly one top-level declaration;
4. obtain its proof range from Lean `Syntax`;
5. replace every selected proof in memory with a correctly indented `by sorry`;
6. preserve every byte outside the selected proof ranges;
7. write the result to a separate output path;
8. check the output with the `Workers` language-server client;
9. fail if there is any error diagnostic, unmatched record, duplicate match, or
   overlapping edit.

The initial command may be:

```text
lean_reassemble rewrite-file \
  --source-root <lake-project> \
  --records <declarations.jsonl> \
  --file <project-relative.lean> \
  --output <rewritten.lean>
```

The exact CLI parser is not important yet. The behavior and failure rules are.

### Required Refactor

Before implementing edits, move the reusable source-navigation code currently
private in `lean-extract/Corpus/CorpusManifest.lean` into:

```text
lean-extract/Corpus/SourceSyntax.lean
```

That module should provide public operations for:

- recursively finding syntax nodes by `SyntaxNodeKind`;
- identifying a declaration's `declId`;
- classifying/finding `declValSimple`, `declValEqns`, and
  `whereStructInst`;
- returning the raw command and proof byte ranges;
- mapping a declaration command to the same line/column key used by
  `findDeclarationRanges?`.

Refactor `Corpus.CorpusManifest` to consume this module without changing
extractor JSON output. Do not copy the private traversal into `reassemble`;
extraction and rewriting must share one implementation.

### Tests For The First Milestone

Add a small fixture module covering:

- `theorem ... := term`;
- `theorem ... := by ...`;
- equation-clause declarations;
- a `where` body;
- nested block and line comments;
- Unicode before and inside a proof;
- attributes, docstrings, and `private theorem`;
- multiple rewritten theorems in one file.

Tests must assert:

- the expected proof ranges are selected;
- applying edits in descending byte order produces valid UTF-8;
- all bytes outside those ranges are unchanged;
- the rewritten file elaborates with only expected `sorry` warnings;
- malformed, absent, duplicate, and overlapping records fail loudly;
- `Corpus.CorpusManifest` output remains unchanged for the fixture.

Run at least:

```bash
cd lean-extract && lake build
cd workers && lake build
cd reassemble && lake build
cd reassemble && lake exe reassemble_tests
```

### First-Milestone Non-Goals

Do not implement these in the first change:

- remote object-store access or storage-specific clients;
- snapshot pin resolution or Git checkout;
- complete repository materialization;
- `.olean` cache packaging;
- independent per-theorem task layout;
- tree-sitter integration;
- schema-v2 changes.

The first milestone establishes the only risky primitive shared by both final
modes: a formatting-preserving, Lean-parsed, LSP-validated rewrite.

## Important Constraint

Do not generate an independent task by importing the theorem's original module
and redeclaring the theorem. That is not faithful:

- public theorem names collide with the imported declaration;
- private declarations have module-derived inaccessible names;
- section variables, local notation, options, namespaces, and attributes are
  not fully represented by `scope_prelude`;
- an elaborated `type` is not necessarily valid source in a new context.

An independent task must therefore retain the complete original source module.
The file is compiled under its original module name, while its imports are
resolved from a pristine `.olean` cache.

## Shared Pipeline

The command-line shape should be:

```text
lake exe lean_reassemble SNAPSHOT --mode units --output DIR
lake exe lean_reassemble SNAPSHOT --mode repos --output DIR
```

### Implementation Architecture

The reassembler lives in the `leagent` repository as a new sibling Lake package
alongside `lean-extract` and `workers`:

```text
leagent/
  lean-extract/   authoritative frontend and corpus-record support
  workers/        Lean worker/LSP client and cache support
  reassemble/     generic corpus materializer library and executable
```

Keeping a separate package avoids adding the legacy worker dependency back to
`lean-extract`, which drives the frontend directly without LSP. The reassembler
depends on both packages and uses three layers:

1. **`Corpus.Frontend`**: load the pinned environment, parse and elaborate the
   original module, and associate extracted declaration names with command
   `Syntax` and source information. This substrate already returns the complete
   source, top-level command syntax, environment, and info trees.
2. **Lean syntax range editing**: reuse the declaration navigation currently in
   `Corpus.CorpusManifest`, which already distinguishes `declValSimple`,
   `declValEqns`, and `whereStructInst`. Splice only that syntax node's raw
   source range. Everything outside the proof remains byte-for-byte unchanged,
   so no formatter is involved.
3. **`Workers` language-server client**: send the edited document through
   `didOpen`/`didChange`, wait for diagnostics, and reject any file with errors.
   Final artifact validation still invokes the Lean compiler.

The source-navigation helpers currently private to `Corpus.CorpusManifest`
should move into a small public `Corpus.SourceSyntax` module so extraction and
reassembly cannot drift.

Tree-sitter is not required for the first implementation. Lean's parser is
authoritative and supports syntax extensions registered by imports; a static
tree-sitter grammar does not. Tree-sitter can later be added as an optional
concrete-tree audit, but disagreement must produce a diagnostic rather than
override Lean's range.

The executable consumes local, versioned manifest and JSONL files. Fetching or
publishing those files is outside this package; storage-specific adapters may
wrap the executable without becoming dependencies of it.

Both modes execute the following stages:

1. Resolve the snapshot pins and fetch each run's metadata and declaration
   records.
2. Keep only `corpus` runs. Other extraction modes do not contain enough
   information for source reconstruction.
3. Resolve and check out the exact source commit in a fresh worktree.
4. Verify every source file against the hashes recorded by extraction.
5. Group theorem records by source file and validate all replacement spans.
6. Replace theorem bodies from the end of each file toward the beginning.
7. Write an artifact manifest and run mode-specific validation.

Reassembly must never mutate an existing checkout. Prototype workflows that
stash changes or rewrite a workspace in place are not acceptable artifact
semantics.

### Pin Selection

A reassemblable snapshot must have at most one corpus pin for a
`(source_repo_name, source_commit, source_subdir)` tuple. Exact duplicate pins
may be deduplicated. Conflicting corpus runs for the same source tree must fail
unless the caller selects a run explicitly.

This matters because snapshots currently allow multiple extraction
configurations of the same commit. Combining their records could rewrite the
same declaration twice or mix incompatible inclusion settings.

### Source Rewrite

The rewriter operates on Lean `Syntax` and emits UTF-8 byte-range edits. It
does not use line/column arithmetic or a global `rfind`. For every theorem it:

1. checks the source file SHA-256;
2. asks the Lean frontend for the declaration command and proof source range;
3. requires that range to agree with the extracted declaration record;
4. checks that all replacement spans in the file are non-overlapping;
5. applies the smallest replacement that produces a canonical `by\n  sorry`
   proof, with indentation derived from the existing syntax;
6. checks the edited document through the Lean language server;
7. fails on any missing, ambiguous, malformed, or diagnostic-producing edit.

The replacement span must cover all valid theorem forms, including `:=`,
equation clauses, and `where` blocks. Lean syntax source information is the
semantic source of truth, and splicing its raw byte range makes the edit
surgical and format-preserving.

For existing `declarations.v1` runs, a compatibility rewriter may derive the
declaration candidate from `decl_source`, but proof boundaries must still come
from parsed syntax. It must require one exact declaration match near the
recorded location, report that the artifact used the legacy path, and never
silently skip a theorem.

## Mode 1: Independent Lean Units

### Build Model

Each unit is a standalone **Lake project**, and all units share one immutable
cache of prebuilt oleans. For each source tree, first build the pristine pinned
checkout with its pinned toolchain and Lake manifest. Capture the ordered import
roots reported by:

```bash
lake env printenv LEAN_PATH
```

Turn each root (outside the toolchain sysroot) into a stub Lake package under
`cache/roots/<n>`: a `lakefile.lean` declaring a `lean_lib` with `roots := #[]`,
plus that root's `.olean`/`.ilean` files placed in the package's build libdir
(`.lake/build/lib/lean`). A `cache/siblings` package requires all of them, in the
captured order. The `roots := #[]` lib compiles nothing of its own, so it only
*exposes* its prebuilt oleans to a dependent's `LEAN_PATH` and can never be written
to during a dependent's build — which is what lets every unit share the cache
immutably. The cache is built from pristine sources, not from sources containing
`sorry`.

Each generated task is a Lake project whose only source is a rewritten copy of its
complete original source module, at the original relative path (so Lake assigns the
same module name, which is required for private declarations). Its `lakefile.lean`
requires `cache/siblings`, so `lake build` reconstructs the pristine `LEAN_PATH`:

```text
units/
  <task-id>/
    lakefile.lean                  # requires ../../cache/siblings
    lean-toolchain
    <original/source/path>.lean
    task.json
cache/
  siblings/                        # stub package requiring every root, in order
    lakefile.lean  lean-toolchain  lake-manifest.json
  roots/
    0/  { lakefile.lean, lean-toolchain, lake-manifest.json, .lake/build/lib/lean/... }
    1/  ...
  native/0/...                     # native libraries, for the direct-lean fallback
  environment.json
manifest.json
```

All extracted theorem bodies in the copied module are `sorry`. `task.json`
identifies one target theorem and its replacement span. Multiple theorem tasks
from the same source module may use hard links, reflinks, or archive
deduplication, but they are logically separate inputs.

The primary check recorded in `task.json` is:

```bash
cd units/<task-id> && elan run <exact-toolchain> lake build
```

`task.json` also records `lean_path`/`ld_library_path` (artifact-relative) for an
equivalent direct-`lean` fallback that does not go through Lake:

```bash
LEAN_PATH=<ordered artifact roots> \
LD_LIBRARY_PATH=<ordered native-library roots> \
elan run <exact-toolchain> \
lean -R units/<task-id> units/<task-id>/<original-path>
```

### Cache Rules

The cache key includes:

- source repository URL, commit, and source subdirectory;
- `lean-toolchain` content and `lean --githash`;
- `lake-manifest.json` hash;
- selected Lake build target and relevant Lean options;
- operating system and architecture when native artifacts are present.

The cache keeps `LEAN_PATH` roots ordered, as one Lake package per root required in
sequence. Roots must not be merged because two dependencies can expose the same
module path and Lake's ordering determines which one wins; the per-root packages
and their require order preserve that.

Each package's Lake manifest is pre-warmed at materialization time (a `lake update`
per package) so a unit's `lake build` neither warns about a missing dependency
manifest nor lazily writes one into the shared cache. All generated lakefiles and
manifests use relative paths, so the artifact is relocatable.

The pristine cache may contain the original `.olean` for the task module. This
is harmless because the input file does not import itself. Its transitive
imports are necessarily acyclic, so a unit's own freshly built (holed) module —
written to the unit's private `.lake` libdir, never the cache — is never loaded by
anything else.

### Unit Verification

The materializer must:

- build every baseline task with `lake build` from the unit directory;
- allow only the expected `sorry` warnings, rejecting any other diagnostic;
- verify the input's calculated module name equals the original `module`;
- verify that no source path outside the task and no cache path outside the
  artifact is required;
- record the exit code and diagnostics summary in the task and manifest;
- strip the unit's own `.lake` build directory and resolved `lake-manifest.json`
  after a successful build, so the shipped unit is minimal and a consumer's first
  `lake build` regenerates them.

## Mode 2: Restored Repositories

### Layout and Build Model

Each pin becomes a fresh checkout with its original repository contents:

```text
repos/
  <repo-name>/
    <normal repository tree>
manifest.json
```

For monorepos, the complete repository is retained and rewrites are limited to
`source_subdir`. Lake files, toolchain files, manifests, non-Lean files,
unextracted declarations, and directory structure remain byte-for-byte equal
to the pinned commit.

After rewriting every extracted theorem body, run the repository's normal
build command, usually:

```bash
lake build <recorded-target>
```

Unlike mode 1, this build must not reuse the pristine repository's own
downstream `.olean` files. The modified modules and all downstream modules are
rebuilt so the restored repository has a coherent cache containing the
`sorryAx` versions.

### Repository Verification

For each repository:

- compare the checkout with the pinned commit and require every diff hunk to be
  inside a recorded theorem proof span;
- require the number of replacements to equal the number of eligible theorem
  records;
- run the recorded build command successfully;
- re-enumerate the rewritten declarations and check that names and types match
  the snapshot;
- check that every rewritten theorem depends on `sorryAx`;
- emit `rewrite-report.json` with replaced, skipped, and failed counts, where
  `skipped` and `failed` must both be zero for a successful artifact.

## Required Snapshot Metadata

The current snapshot pins identify runs, and declaration records contain
`decl_source`, source paths, and line/column locations. That is enough for a
strict legacy implementation, but not enough for a portable, durable one.

Add the following run-level fields:

```text
source_repo                 canonical clone URL, required
source_commit               full commit SHA
source_subdir               project path inside a monorepo, default "."
project_root                directory containing lean-toolchain/Lake config
lean_toolchain              exact lean-toolchain content
lean_githash                output of lean --githash
lake_manifest_sha256        dependency-lock hash
build_target                target used during extraction
build_command               normalized build command
platform                    OS and architecture
```

Add the following declaration-level fields in `declarations.v2`:

```text
source_file_sha256
decl_start_byte
decl_end_byte
proof_start_byte
proof_end_byte
decl_source_sha256
sorry_decl_source
```

`sorry_decl_source` is generated and successfully elaborated during extraction.
Keeping it in the record makes reconstruction deterministic across extractor
versions; the byte spans still allow the reassembler to verify exactly what it
is replacing.

Snapshot creation should mark a snapshot `reassemblable: true` only when all
corpus pins contain the required source and toolchain metadata.

## Artifact Manifest

Both modes write a versioned manifest containing:

```json
{
  "format": "lean-corpus-reassembly.v1",
  "snapshot": "train-v1",
  "mode": "units",
  "created_at": "...",
  "pins": [],
  "toolchains": [],
  "caches": [],
  "tasks": [],
  "rewrite_summary": {
    "eligible": 0,
    "replaced": 0,
    "skipped": 0,
    "failed": 0
  },
  "verification": {
    "status": "passed"
  }
}
```

The manifest uses artifact-relative paths and includes SHA-256 hashes for
generated sources, cache files, and repository rewrite reports.

## Implementation Order

1. Extract the existing declaration/body syntax navigation from
   `Corpus.CorpusManifest` into a tested public `Corpus.SourceSyntax` module.
2. Scaffold `leagent/reassemble` as a sibling Lake package depending on
   `lean-extract` and `workers`, with a language-server test harness.
3. Implement one vertical rewrite path: load a module, match one extracted
   theorem, obtain its Lean proof range, apply the edit in memory, and require
   clean LSP diagnostics.
4. Generalize the rewrite library and test `:=`, equation, `where`, comments,
   Unicode, private declarations, and multiple declarations in one file.
5. Extend run metadata and extraction schema with source identity, byte spans,
   hashes, and verified `sorry_decl_source`.
6. Implement snapshot resolution into fresh worktrees and reject ambiguous
   pins.
7. Implement repository mode first; it is the end-to-end correctness oracle
   for the resolver and rewriter.
8. Implement pristine cache capture and independent task packaging.
9. Add full baseline compilation and artifact portability tests for both
   modes.

## Acceptance Criteria

Mode 1 is complete when any emitted task can be moved with its cache to a
directory containing no `lakefile.*` and passes the manifest's direct Lean
command.

Mode 2 is complete when each emitted repository builds normally, differs from
its pinned commit only at extracted theorem bodies, and every such body is
verified to elaborate through `sorryAx`.
