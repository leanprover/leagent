# Reassembler manifest — design

Status: proposed (planning). Grounds every decision in the current code so the
implementation is a series of localized changes rather than a rewrite.

## Goal

Give the reassembler a per-theorem policy: for each theorem, decide whether to
**keep** its proof, replace it with **sorry**, or **delete** the declaration
entirely. A manifest supplies these decisions sparsely; anything it does not
mention falls back to the global `--proofs` flag. A run-level policy decides what
happens when a theorem fails to reassemble: fail loudly, or back off by deleting
the offending theorem and retrying.

## Current state (what we build on)

- `ProofMode` is global and binary: `--proofs sorry|keep`
  (`LeanReassemble/Rewrite.lean:20`). `.replace` holes each proof with
  `by sorry`; `.keep` preserves it verbatim. There is no `delete`.
- Behavior is strictly all-or-nothing. The first record that fails to match a
  declaration, whose recorded `body` disagrees with source, or that breaks the
  build aborts the whole run via `fail` (`Rewrite.lean:60`).
- The manifest output already carries `skipped` and `failed` fields, both
  hardcoded to `0` (`Materialize.lean:148-149`).
- Three commands (`Main.lean`): `rewrite-file`, `materialize-repo` (one
  whole-tree `lake build`), `materialize-units` (one isolated `lean -R` per
  theorem — failure is already attributable to a single theorem here).
- Records match declarations by full name + optional `startLine`/`startCol`
  (`Rewrite.lean:173`).
- `Corpus.SourceSyntax.commandRange?` (`SourceSyntax.lean:81`) returns the full
  declaration span — doc comment and attributes included — so `delete` can excise
  a whole theorem cleanly, not merely its proof.

## Decisions (locked)

1. **Scope:** manifest actions and back-off apply to *both* `materialize-repo`
   and `materialize-units` (and `rewrite-file` for keep/sorry/delete).
2. **Delete + dependents:** no dependency analysis. The user owns manifest
   correctness. Deleting a theorem that others depend on will fail the build —
   that is the user's responsibility, not something we cascade or block.
3. **Failure policy:** a global flag `--on-failure fail|skip|backoff`
   (default `fail` = today's behavior).
   - `fail`: abort the whole run on any theorem failure.
   - `skip`: omit the failing theorem from output (leave source as-is), record it
     in `skipped`, continue.
   - `backoff`: degrade the failing theorem straight to `delete`, record it in
     `failed`, retry.
   Uses both existing manifest fields (`skipped`, `failed`).
4. **Repo-mode attribution:** best-effort parse of `lake build` diagnostics to
   map a failure back to a theorem; if it can't attribute, fall back to
   fail-loud (applies to both `skip` and `backoff` in repo mode).
5. **Repo-mode skip semantics:** a skipped theorem keeps its *original proof* in
   the artifact (the edit is simply not applied). Under `--proofs sorry` that
   means the proof stays real, not holed. This is accepted and logged in
   `skipped` so the artifact is honest about what was not rewritten.

## Manifest format

New optional flag `--manifest <path>`, valid on all commands. Sparse JSON
override map keyed by full theorem name (the same string matched at
`Rewrite.lean:174`):

```json
{
  "format": "lean-reassemble-manifest.v1",
  "theorems": {
    "Nat.add_comm":  "keep",
    "Foo.helper":    "sorry",
    "Foo.deadLemma": "delete"
  }
}
```

- Values: `keep | sorry | delete`.
- Absent theorem ⇒ fall back to `--proofs`.
- A manifest key that matches no eligible theorem ⇒ hard error (typo guard).

## Implementation phases

### Phase 1 — `delete` as a third action
- Extend `ProofMode` (`Rewrite.lean:20`) with `| delete`; `toString` → `"delete"`.
- Accept `--proofs delete` as a global default (`parseProofMode`, `Main.lean:46`).
- `planEdits` (`Rewrite.lean:164`): for `.delete`, edit range = `commandRange?`
  (whole declaration), `replacement := ""`. Skip the body-match check for delete
  (nothing to preserve). Keep/replace paths unchanged.
- `replacementFor` (`Rewrite.lean:136`) gains a `.delete` arm.
- `rewriteSummary` (`Materialize.lean:142`) reports a real `deleted` count wired
  from per-action tallies instead of the current derived values.

### Phase 2 — manifest plumbing (sparse override)
- New `Manifest` type (`Std.HashMap String ProofMode`) + a JSON reader reusing
  `Corpus.Artifact` conventions.
- Thread an optional manifest through `RewriteConfig` / `MaterializeConfig` into
  `planEdits`, which resolves each record's effective mode:
  `manifest[name]?.getD config.proofMode`.
- Validate every manifest key matches an eligible theorem; error on strays.
- Units mode: a `delete` target emits no task and is recorded as
  `deleted`/`skipped` — a "prove this deleted theorem" unit is meaningless.

### Phase 3 — failure policy (`--on-failure fail|skip|backoff`)
`skip` and `backoff` share one mechanism: (a) attribute the failure to a theorem,
(b) relax the all-or-nothing invariant, (c) act on the offender. They differ only
in the action — `skip` omits + records in `skipped`; `backoff` deletes + records
in `failed`.

- Default `fail` = current fail-loud behavior.
- Attribution:
  - Cleanly attributable today: `planEdits`/validation errors that name the
    record (`Rewrite.lean:178,180,193`) and per-unit `lean -R` failures
    (`Materialize.lean:356`).
  - Repo mode: the single whole-tree `lake build` (`Materialize.lean:179`) fails
    without naming a theorem. Best-effort parse the Lean diagnostic's file+line
    back to an edit; if attribution fails, both `skip` and `backoff` fall back to
    `fail`.
- Relax the `replaced == theorems.size` invariant (`Materialize.lean:176`), which
  currently assumes every theorem was edited.
- Repo-mode `skip` leaves the original proof in place (decision 5); units-mode
  `skip` simply drops the task.
- Populate `skipped`/`failed` in the manifest (currently hardcoded `0`).

**Implementation boundary (as built).** Attribution turned out to cleanly cover
only *planning* failures (unmatched record, ambiguous match, body mismatch,
missing declaration syntax). A *post-rewrite build break* was deliberately left as
fail-loud even under `skip`/`backoff`, because a `sorry`/`delete` almost never
breaks at the theorem's own location — it breaks at a **dependent**, and the Lean
diagnostic points at that dependent. Auto-deleting the erroring site would remove
the wrong declaration and silently produce a wrong-but-"successful" artifact,
which violates the "don't paper over failures" principle. So:
- `planEdits` → strict (used under `fail`); `planEditsCollecting` → returns
  `{edits, failures}` (used under `skip`/`backoff`).
- units mode: the whole per-task body (plan + write + `lean -R` verify) is
  attributable to one record, so `skip`/`backoff` are clean end-to-end there.
- repo mode: per-file planning is resilient; the final whole-tree `lake build`
  aborts on failure regardless of policy.
- `backoff` re-plans each failed record as `delete`; a record with no matchable
  declaration has nothing to delete, so it falls through to a skip.

### Phase 4 — docs + tests
- Update `usage` (`Main.lean:6`) and `README.md`.
- Fixtures/tests: delete of a leaf; delete-with-surviving-dependent (asserts the
  failure is the user's, per decision 2); manifest override precedence;
  back-off degrading a failing theorem to delete.

## Open risks

- Repo-mode attribution is the one fragile piece; explicitly best-effort with a
  fail-loud fallback, called out in docs.
- `delete` removing a name that dependents reference is by-design allowed to
  break the build (decision 2).
