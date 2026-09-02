# Reassembler parameter matrix

Status: spec. Defines the intended behavior of every meaningful combination of
`lean_reassemble` parameters, so each combination is either **sensible** or
**explicitly rejected** — never a silent wrong/misleading result. The
implementation (dependency-conflict detection, per-unit neighbour pruning, combo
guards) is verified against this matrix; see the "Validation" section.

## Parameter surface

Subcommands: `rewrite-file`, `materialize-repo`, `materialize-units`.

| Parameter | Values | Meaning |
|---|---|---|
| `--proofs` | `sorry` (=replace) / `keep` / `delete` | global default action per theorem (`Rewrite.lean` `ProofMode`) |
| `--manifest` | per-theorem `keep`/`sorry`/`delete` | sparse override on `--proofs` (`Manifest.actionFor`) |
| `--on-failure` | `fail` / `skip` / `backoff` | what to do when a theorem cannot be reassembled |
| `--build-target` | a Lake target | scopes the build (see per-subcommand notes) |
| `--keep-eval` | flag | keep `#eval`/`#guard`/… instead of stripping (repo only) |
| `--in-process` | flag | rewrite all files in one process; performance only (repo only) |

Each theorem's **resolved action** is `manifest[name]` if present, else `--proofs`.
The interesting axis is the *set* of resolved actions across the records.

Dependency data on every record (`Corpus.ConstRecord`): `deps` — the direct
constants the declaration references; `premises` — the transitive project-owned
cone (polluted with undeletable auxiliaries like `._f`/`.match_1`/`._proof_*`);
`closureRole` — `"target"`/`"statement"`/`"proof"` within a `--decl` closure.

### Flag applicability

| Flag | rewrite-file | materialize-repo | materialize-units |
|---|---|---|---|
| `--proofs` | ✅ | ✅ | ✅ (target action) |
| `--manifest` | ✅ (optional) | ✅ | ✅ (target + neighbour pruning) |
| `--on-failure` | ✅ | ✅ | ✅ |
| `--build-target` | — | ✅ (final build) | ⚠️ pristine warm-up build only |
| `--keep-eval` | — | ✅ | 🚫 rejected (inert) |
| `--in-process` | — | ✅ | 🚫 rejected (inert) |

## Verdict vocabulary

- **sensible** — supported; the artifact is well-defined.
- **degenerate** — technically runs but yields no value; handled explicitly (excluded/warned) rather than shipped as a success.
- **rejected** — parser or pre-flight error, with a specific message.
- **requires-dependency-check** — runs only if the dependency pre-flight finds no dangling reference; otherwise fails fast naming each `dependent → deleted` pair.
- **inert** — flag has no effect for that subcommand; rejected at parse for units, documented for repo.

## materialize-repo

Copies the whole source tree, rewrites the files that carry records, then runs a
single `lake build` (scoped by `--build-target`). The build is the correctness
oracle for what remains; the dependency pre-flight makes *declared* deletes fail
with attribution before that build.

| `--proofs` \ manifest | absent | mixes in `delete` | mixes in `keep`/`sorry` only |
|---|---|---|---|
| `sorry` | sensible — hole every recorded proof, strip eval, build | requires-dependency-check | sensible |
| `keep` | sensible — byte-identical reference state; nothing holed | requires-dependency-check | sensible |
| `delete` | requires-dependency-check — deletes all recorded theorems | requires-dependency-check | requires-dependency-check |

Orthogonal flags:
- `--keep-eval`: meaningful with `sorry`/`delete` (something is holed); inert but
  harmless with a pure `keep` run (nothing holed ⇒ eval never stripped).
- `--in-process` vs isolated: identical artifacts; performance/memory only.
- `--build-target`: scopes the final build. A holed/deleted theorem in a module
  *outside* the target is not compiled, so a break there is not observed — see
  "Rejections & guards".
- `--on-failure backoff`: degrades *planning*-failed theorems to `delete`. Those
  discovered deletes are **not** covered by the pre-flight (which only sees
  declared manifest/mode deletes); a resulting break still aborts at `lake build`.

## materialize-units

One standalone unit per theorem record. A unit is the target's whole module file
with the target's proof holed (`sorry`); statement neighbours stay proven and
resolve, together with cross-module dependencies, from the shared prebuilt cache.
A manifest may additionally **prune same-module neighbours** marked `delete`.

| target's resolved action | verdict |
|---|---|
| `sorry` (replace) | sensible — the standard task (target holed) |
| `keep` | degenerate — a "prove-nothing" unit; excluded with a warning |
| `delete` | degenerate — no task for a deleted target; excluded (counted) |

Neighbour actions **within** a unit (manifest, same module as the target):
- `delete` → the neighbour declaration is removed from that unit's file.
- `keep` / unlisted → kept proven (default is `keep`, not `--proofs`).
- `sorry` on a non-target neighbour → treated as `keep` (a unit only holes its own
  target; holing an unrelated neighbour is out of scope).
- `delete` on a `where`/`let rec` auxiliary → no-op (no standalone syntax).

Removing a neighbour can strand a *kept* neighbour or a def that references it;
that is caught per-unit by the dependency pre-flight (**requires-dependency-check**,
restricted to the target's module — cross-module refs come from the cache).

Orthogonal flags: `--build-target` scopes only the *pristine warm-up* build that
populates the shared cache, **not** the per-unit builds; `--keep-eval` and
`--in-process` are inert and rejected at parse.

## rewrite-file

Rewrites one file and validates the edited document with the Lean LSP worker; it
does not build the project.

- `sorry`/`keep`/`delete` on this file's records: **sensible**. A `delete` of a
  name referenced *within the same file* is caught by the LSP validation.
- Cross-file dangling references are **not** checked (single-file scope, by
  design). `--manifest` is accepted and validated against every record (a key
  naming a theorem in another file is not a typo), but only this file's records
  are rewritten.

## Rejections & guards

Each of these is an explicit error or excluded outcome, not a silent success:

1. **repo/units dependency conflict** — a surviving declaration's `deps` names a
   theorem the run deletes. Fail (under `--on-failure fail`) before building:
   ```
   dependency conflict: N surviving declaration(s) reference deleted theorem(s);
   deleting would break the build:
     Trees.Tree.total_mirror -> Trees.sumList_reverse
   ```
   In units under `--on-failure skip`/`backoff`, the affected unit is omitted and
   named in the artifact's `manifest.json` instead of aborting the whole run.
2. **units empty artifact** — if no task is produced (every eligible theorem
   resolved to `delete`/`keep`/auxiliary), fail rather than write a `manifest.json`
   with `verification: passed` over zero tasks:
   ```
   materialize-units produced no tasks: all N eligible theorem(s) resolved to
   delete/keep/auxiliary — nothing to reconstruct
   ```
3. **units `--proofs delete`** (global default) — rejected early: it would delete
   every target and produce no tasks.
4. **units `--proofs keep`** (global default) — every target is a prove-nothing
   unit; all are excluded, so the empty-artifact guard (2) fails the run.
5. **units `--keep-eval` / `--in-process`** — rejected at parse as unknown
   arguments; they have no effect in units mode.
6. **repo `--build-target` masking** — a build scoped to a target does not compile
   modules outside it, so a dangling reference there is not observed by the build.
   The dependency pre-flight (1) covers *declared* deletes regardless of target;
   the artifact's `verification` object records the exact `lake build <target>`
   command so a scoped verification is never mistaken for a whole-project one.

## Validation

Automated tests live in `reassemble/ReassembleTests.lean` against the in-repo
`TestProject` (and a new `TestProject/Fixture/Deps.lean` fixture that carries a
real theorem→theorem `deps` edge, which the original fixtures lack). They cover:
the pure `danglingReferences` relation, the three confirmed regressions
(units-delete → no tasks, units-keep → empty, repo delete-with-kept-dependent →
named conflict, not an opaque `lake` error), and the new units neighbour-pruning
and per-unit conflict behavior.

Manual end-to-end on `examples/tree-project` (both pinned to the repo toolchain):
`materialize-repo --manifest '{"theorems":{"Trees.sumList_reverse":"delete"}}'`
reports the named conflict `Trees.Tree.total_mirror -> Trees.sumList_reverse`;
default `materialize-units` and a units run pruning a leaf theorem both build clean.

Not in CI: the external corpus under `~/workplace/arg/src/LeanCorpusData/generated/*`
pins Lean v4.31.0 while leagent tracks a newer toolchain, so real-corpus checks
need version-matched binaries.
