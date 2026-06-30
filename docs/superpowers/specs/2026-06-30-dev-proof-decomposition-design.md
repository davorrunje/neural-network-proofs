# Development-Proof Decomposition — Design

**Date:** 2026-06-30
**Status:** approved (design); implementation plan to follow
**Predecessor:** `2026-06-28-formathlib-conformance-design.md` (ForMathlib Phase 2,
proof decomposition) — this applies the same idea to the *development* proofs.

## Goal

Improve the **readability and maintainability** of the Cybenko and Leshno
development proofs by decomposing long tactic blocks into small, well-named
lemmas — with a secondary aim of surfacing reusable lemmas for the upcoming
monotone-NN work (`UniversalApproximation/Monotone/`).

Unlike `ForMathlib/`, these modules are **not upstream-facing**, so the
refactor has more freedom: intermediate lemmas may be renamed, re-scoped, or
re-signatured. Only the two headline theorems are frozen.

## Scope

Both developments are in scope (the earlier "do not modify Cybenko proof
content" constraint is lifted):

- `NeuralNetworkProofs/UniversalApproximation/Cybenko/` + `Cybenko.lean`
- `NeuralNetworkProofs/UniversalApproximation/Leshno/` + `Leshno.lean`

Out of scope: `ForMathlib/` (done in Phase 2), `NeuralNetwork/` infrastructure
unless a track directly requires it.

## The frozen invariant

Exactly two things must be preserved, verified with fresh `.olean`s:

- `UniversalApproximation.Cybenko.universal_approximation` — statement & axioms
- `UniversalApproximation.Leshno.leshno_dense_iff` — statement & axioms

Both must remain `[propext, Classical.choice, Quot.sound]`. Everything between
the leaves and these headlines may be restructured. No `sorry`/`admit`, no new
`import Mathlib`, no `set_option maxHeartbeats` (there are none outside
ForMathlib today — keep it that way), lines ≤ 100 codepoints.

## Architecture — Strategy A: two concurrent tracks, serial within each

Cybenko and Leshno share nothing but `ForMathlib`, so they run as two
**concurrent pipelines**. Within a track, files are decomposed **bottom-up in
dependency order** (leaves first), **one file at a time**. Because a file's
consumers are always strictly downstream (not yet processed), a rename can only
ripple forward — it can never collide with a sibling task already in flight.

### Dependency orders (from imports)

**Cybenko track** (bottom-up):

1. `Cybenko/Activation.lean` (leaf)
2. `Cybenko/Discriminatory.lean`, `Cybenko/Family.lean`, `Cybenko/Riesz.lean`
   (same level — independent of each other)
3. `Cybenko/Theorem.lean`
4. `Cybenko.lean` (root re-export; expected no-op)

**Leshno track** (bottom-up):

1. `Leshno/ClassM.lean` (leaf)
2. `Leshno/MollifyDef.lean`, `Leshno/Family.lean` (same level)
3. `Leshno/SmoothEngine.lean`, `Leshno/Ridge.lean`, `Leshno/Mollify.lean`,
   `Leshno/Converse.lean` (same level)
4. `Leshno/Theorem.lean`
5. `Leshno.lean` (root re-export; expected no-op)

Same-level files have no inter-dependency and could be parallelized later if
throughput is wanted; the default is serial-in-order for simplicity.

## Task unit & decomposition policy

- **One file = one task** (implementer + reviewer), as in Phase 2.
- **Judgment-driven, not mechanical.** Split a proof only where a named
  sub-lemma genuinely clarifies the argument or is plausibly reusable for the
  monotone work. Never split solely to reduce a line count.
- **No-op tasks are valid.** A file (especially the small leaves: `MollifyDef`,
  `Activation`, `ClassM`, `Cybenko.lean`, `Leshno.lean`) may have nothing worth
  decomposing. The implementer reports "left intact" with a one-line rationale
  and the controller records it complete — exactly like Phase 2 Task 9
  (`iteratedDeriv_convolution_left`).
- Extracted lemmas carry docstrings and minimal hypotheses; tighten visibility
  to `private` where the lemma is file-local.

## Cross-file renames

Renaming exported lemmas is **allowed**. Because tracks run bottom-up, an
exported lemma's consumers are always in downstream (not-yet-decomposed) files:

- The renaming task **updates all in-repo call sites in the same commit** (pure
  identifier swaps). It is acceptable for a downstream file to appear in two
  task diffs — once for a rename-only touch, later for its own decomposition.
- File-local lemmas may be renamed/restructured with no further obligation.

## Execution mechanics

- **Subagent-driven development** (the Phase 2 workflow): one implementer per
  task (stage-only — `git add`, never commit), then a task reviewer (spec
  compliance + code quality). Controller commits each task as it lands
  **unsigned** (`git -c commit.gpgsign=false commit`).
- **Deferred signing (hard requirement).** SSH commit-signing requires the
  user's live presence to confirm the agent operation, which is *not* available
  during autonomous execution. Therefore **no commit is signed during
  execution**; the entire branch is **batch-signed in a single step immediately
  before opening the PR** (`git rebase --exec 'git commit --amend --no-edit -S'
  <base>`), a step the user must be present for. The PR is opened only after
  every commit shows `G`.
- **Two concurrent tracks:** the controller may have one Cybenko task and one
  Leshno task in flight at once (disjoint files — no commit contention).
- **Ledger** at `.superpowers/sdd/progress.md` records each task completion
  (commit range + review verdict), the recovery map across compaction.
- **Final whole-branch review** on the most capable model before PR.
- **One branch, one PR** (base `main`) for both tracks. Split into two PRs only
  if the combined diff becomes unwieldy.

### Per-task verification

`lake build` green + `lean_diagnostic_messages` zero errors/sorry on the file.

### Per-track close-out

The track's headline is axiom-clean against fresh `.olean`s:
Cybenko → `universal_approximation`; Leshno → `leshno_dense_iff`.

### Final gate

Full `lake build` green; **both** headlines `[propext, Classical.choice,
Quot.sound]`; no `maxHeartbeats` / no bare `import Mathlib` anywhere; zero
linter warnings in touched files; all lines ≤ 100 codepoints.

## Out of scope / non-goals

- No promotion of dev lemmas into `ForMathlib/` in this pass (a separate
  decision; this pass is internal readability only).
- No changes to headline statements or to the public API a downstream consumer
  outside this repo might rely on — there is none beyond the two headlines.
- No new mathematical content; behavior-preserving only.
