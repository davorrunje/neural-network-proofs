# Monotone-NN Proofs — Mathlib-Standards Refactor — Design

**Date:** 2026-07-03
**Status:** approved (design); implementation plan to follow
**Target:** the merged monotone-NN development under
`NeuralNetworkProofs/UniversalApproximation/Monotone/` (Mikulincer–Reichman Result 1, PR #15).

## Goal

Refactor the monotone-NN development to Mathlib-idiomatic quality (**Approach A: full re-model**).
The code is correct and reviewed but was written quickly; it carries a hand-rolled network model,
`Fin (n*d)` flattening gymnastics, junk-value finite-difference machinery, a duplicated proof, and
longhand hypotheses that are really `MonotoneOn`. This refactor re-models the internals to idiom
while preserving the two headline theorems exactly.

## Frozen invariant

Exactly two declarations are immutable — statements **and** axiom profile
`[propext, Classical.choice, Quot.sound]` (verified on fresh oleans):

- `UniversalApproximation.Monotone.monotone_interpolation`
- `UniversalApproximation.Monotone.monotone_approximation`

Everything else — the network model (`θ`/`ThreshStack`/`MonoNet`), the domination gadget, the
interpolation construction, the grid, and every intermediate signature — may be re-modeled. The
refactor is behavior-preserving *only* at the two headlines. No `sorry`/`admit`; no
`set_option maxHeartbeats` in committed code; lines ≤ 100 codepoints; docstrings on public decls.

Extracted general lemmas stay **project-local** (this refactor's chosen depth is "re-model internal
defs", not upstreaming); they are named so they *could* migrate to `ForMathlib/` later, but that is a
separate decision and out of scope here.

## Re-model, file by file

### `Defs.lean` — the model (linchpin; ripples to all files)

- **`θ → heaviside`.** Keep `if 0 ≤ z then 1 else 0`; derive `heaviside_monotone`, `heaviside_nonneg`,
  `heaviside_le_one` via clean lemmas (not ad-hoc `split_ifs <;> norm_num` where a library lemma fits).
- **Monotonicity via `OrderHom`.** Replace the standalone `monotone_toFun` structural recursion with
  a bundled `ThreshStack.toOrderHom : S.IsMonotone → ((Fin a → ℝ) →o (Fin b → ℝ))` built by induction
  using `OrderHom.comp`; `ThreshStack.toFun` becomes its coercion, and `MonoNet.monotone_toFun` falls
  out of `OrderHom` monotonicity plus the non-negative read-out. `depth`/`IsMonotone` stay structural.
- **Reusable layer lemma** via `Matrix.dotProduct_le_dotProduct_of_nonneg_right`, relocated/renamed
  out of the misleading `Layer.*` prefix.
- The dependent-dimension layer chain is retained (dimensions are heterogeneous
  `d → n·d → n → n → 1`); the gain is *derived* monotonicity + downstream reuse, not a homogeneous
  `List`.

### `Domination.lean`

- Keep the middle layer **`Fin n × Fin d`-indexed** (curry; flatten only at the type boundary),
  removing the `finProdFinEquiv.symm` / `Fintype.sum_prod_type` / `Finset.sum_eq_single` gymnastics in
  `dominationLayer1_apply` / `dominationStack_apply`.
- Extract `sum_thresh_ge_iff` as a general `Finset` lemma: for `g : ι → ℝ` with `∀ i, g i ≤ 1`,
  `Finset.card … ≤ ∑ g ↔ ∀ i, g i = 1` (independent of `heaviside`).

### `Interpolation.lean` — crux

- Replace `readW` / `Ycum` / `telescope_pred` with **forward differences `Y (k+1) − Y k` and
  `Finset.sum_range_sub'`**, deleting the custom telescope lemma and the `0−1=0` / `if _ = 0` /
  `if h : k < n … else 0` junk-value guards (honest indexing, e.g. `Fin.cons`/`Fin.consEquiv`).
- **Reuse `dominationStack` and `dominationStack_isMonotone`** when building `stack₃`, deleting the
  duplicated non-negativity proof (`interpNet_isMonotone` currently re-derives the domination layers'
  weights ≥ 0).
- Tidy the `Tuple.sort` reindex using Mathlib sort-uniqueness lemmas
  (`Tuple.eq_sort_iff`/`Tuple.sort_sorted`) where they shorten `reindex_linear_extension`.

### `Grid.lean`

- Adopt `MonotoneOn f (Set.Icc 0 1)` in `gridEnum_monotone_dataset` (replacing the longhand
  `∀ ⦃a b⦄, a ∈ … → b ∈ … → a ≤ b → …`).
- Use resolution `m + 1` in the types so the `m = 0` junk branch in `gridPoint_mem_Icc` disappears.
- `gridPoint_injective` via `div_left_injective₀`; floor/ceil clamp cleanup using
  `Nat.ceil_le_floor_add_one` and cleaner `Fin.mk` construction.

### `Approximation.lean`

- Thread `MonotoneOn` through the sandwich (`hfl`/`hfr` via `MonotoneOn.` API). The headline's own
  `hmono` hypothesis is part of the frozen statement and does **not** change; only the surrounding
  private lemmas adopt `MonotoneOn`.
- Extract `dist_le_of_coord` (sup-metric-from-coordinates, a `dist_pi_le_iff` wrapper) as a named
  lemma; keep the clean uniform-continuity helper.

### `Monotone/Basic.lean` (new)

Home for the genuinely general extracted lemmas — `sum_thresh_ge_iff`, `dist_le_of_coord`,
`reindex_linear_extension` — to cut cross-file coupling. Imported by the files that use them. (If a
lemma reads better next to its sole use site, it may stay there instead; `Basic.lean` is for the
shared ones.)

## Execution & verification

- **Subagent-driven**, one implementer + one reviewer per file, then a final whole-branch review.
- **Order** (mostly serial — the model change propagates): `Basic` (extracted lemmas) → `Defs` →
  `Domination` → `Interpolation`; `Grid` and `Approximation` follow. `Defs` is first among the model
  files because its re-model ripples everywhere.
- **Per task:** module builds; `lean_diagnostic_messages` zero errors/`sorry`/linter-warnings.
- **Whole-branch gate:** full `lake build` green; both headlines `[propext, Classical.choice,
  Quot.sound]` on fresh oleans; `scripts/check_sorry_free.lean` clean; no `maxHeartbeats`; all changed
  files ≤ 100 codepoints.
- **Deferred signing:** execution commits are **unsigned** (`git -c commit.gpgsign=false commit`); the
  branch is **batch-signed before the PR**, signing only the unpushed commits (the repo blocks
  force-push). PR opened only after every commit shows `G`.

## Risk & escape hatch

The `ThreshStack.toOrderHom` re-model is the linchpin; its payoff over the current inductive is real
but not dramatic. If, during implementation, the `OrderHom` bundling *complicates* the crux
interpolation proof rather than clarifying it, that is a `NEEDS_CONTEXT` checkpoint to reconsider (fall
back to keeping the current `monotone_toFun` recursion while still doing the de-flattening,
telescoping, dedup, and `MonotoneOn` cleanups) — not a `sorry`, and never a change to a frozen
headline.

## Out of scope

Upstreaming to `ForMathlib/` (a separate later decision); any change to the two headline statements;
Result 2 of the paper; new mathematical content.
