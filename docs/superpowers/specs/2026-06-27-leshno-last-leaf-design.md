# Closing the last Leshno leaf: `tendstoUniformly_riemannSum_aeContinuous`

**Date:** 2026-06-27
**Status:** Approved (design); proceeding to plan + implementation.

## Goal

Eliminate the single remaining `sorry` in the Leshno M-class UAT development:
`UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous`. Closing it makes
`Mollify.mollify_ridge_mem_T` and the headline `leshno_dense_iff` `sorryAx`-free, taking the whole
development to **0 leaves**.

## The leaf

```lean
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S
```

`f` is the M-class activation `σ` (locally bounded; closure of its discontinuity set is null);
`φ` is a continuous, compactly-supported test function; `riemannSum f φ M m s` is the
equispaced point-sampling Riemann sum of `y ↦ f (s − y) · φ y` over `m` cells of `Icc (-M) M`
(defined in the file). The claim: those sums converge to the convolution integral **uniformly in
`s ∈ S`** for compact `S`.

## Why this route (good/bad cells via metric thickening)

The blocker note records two dead ends — `BoxIntegral` (no parameter-uniform tendsto, does not
specialise to the fixed equispaced point-sampling sum) and oscillation-sup + dominated convergence
(measurability of an uncountable-index supremum needs `AnalyticSet.nullMeasurableSet`, absent from
this Mathlib). The good/bad-cell route **contains no `sup`-over-uncountable-index object at all**, so
the measurability obstruction never arises. It is the classical Lebesgue-criterion proof done by
hand, and every ingredient is already in Mathlib.

## Proof architecture

Fill the leaf's `sorry` in place. Supporting `private` helper lemmas go *above* the leaf in the same
file (`LeanPlayground/Contrib/UniformRiemannConvolution.lean`). The proved continuous lemma
`tendstoUniformly_riemannSum_continuous`, the `riemannSum` definition, the leaf's *statement*, and
every other file remain byte-untouched. No new imports (the file already does `import Mathlib`). The
cell-decomposition skeleton from the continuous case (`g_eq`, `hg_sum`, `hr_sum`, node monotonicity
and containment) is re-derived inline in the new proof rather than refactored out, so the existing
lemma is not disturbed.

### The decomposition

Via `Metric.tendstoUniformlyOn_iff`, fix `ε > 0`. Reduce the convolution integral to an interval
integral on `(-M)..M` and to a sum over cells (as in the continuous case). On each cell `i` with
left endpoint `yᵢ`, split the integrand error:

```
f(s−y)·φ(y) − f(s−yᵢ)·φ(yᵢ)
  = f(s−y)·(φ(y) − φ(yᵢ))          -- φ-variation term
  + (f(s−y) − f(s−yᵢ))·φ(yᵢ)       -- f-variation term
```

**φ-variation term.** `|f(s−y)| ≤ C` on the fixed compact `J' := S + [−M, M]` for all `s ∈ S` (from
`hbdd` with `R` = a bound on `|J'|`); `|φ(y) − φ(yᵢ)| ≤ ω_φ(Δ) → 0` by uniform continuity of `φ` on
its compact support, where `Δ = 2M/m` is the cell width. Total `≤ C · ω_φ(Δ) · 2M`, uniform in `s`,
handled exactly as in the continuous case.

**f-variation term.** Bounded by `‖φ‖∞ · ∑ᵢ ∫_{cellᵢ} |f(s−y) − f(s−yᵢ)| dy`. Let
`K := closure {t | ¬ ContinuousAt f t} ∩ J` where `J := Icc (sInf S − M) (sSup S + M)` is the fixed
compact set containing every `s − y` for `s ∈ S`, `y ∈ Icc (-M) M`. `K` is compact (closed ∩ compact)
and null (subset of the null `closure {¬ContinuousAt f}`).

- **Good cells** (those disjoint from `Metric.thickening δ₀ K`): such a cell lies in
  `J \ Metric.thickening δ₀ K`, a *compact* set on which `f` is continuous at every point (its points
  are at distance `≥ δ₀ > 0` from `K ⊇ closure{¬ContinuousAt f} ∩ J`, hence not discontinuity
  points). `f` restricted there is uniformly continuous
  (`IsCompact.uniformContinuousOn_of_continuous`), giving oscillation `≤ ε'` once `Δ < δ_unif`. Sum
  over good cells `≤ ε' · 2M`.
- **Bad cells** (those meeting `Metric.thickening δ₀ K`): oscillation `≤ 2C`. Each bad cell lies in
  `Metric.cthickening (δ₀ + Δ) K` (a cell within `δ₀` of `K` has all points within `δ₀ + Δ` of `K`),
  so the union of bad cells has measure `≤ volume (cthickening (δ₀ + Δ) K)`. By
  `tendsto_measure_cthickening`, `volume (cthickening r K) → volume K = 0` as `r → 0⁺`; choose `δ₀`
  (and require `Δ` small) so this is `< η`. Sum over bad cells `≤ 2C · η`.

`K` and `δ₀` depend only on `f, S, M` — never on `s` — so both bounds are **uniform in `s`**.

### Quantifier order

Given `ε`: choose `η` with `2 · ‖φ‖∞ · C · η < ε/3` (the bad-cell budget); `tendsto_measure_cthickening`
yields `δ₀` with `volume (cthickening δ₀ K) < η`, fixing `K`'s thickening and the compact complement;
uniform continuity of `f` on that complement yields `δ_unif` for the good-cell budget `ε/3`; uniform
continuity of `φ` and the bound `C` give the φ-term budget `ε/3`. Then pick `N` so that for `m ≥ N`,
`Δ = 2M/m` is below `δ_unif`, below `δ₀` (so the bad-cell `cthickening (δ₀+Δ)` measure stays `< η`
via a second application / monotonicity), and small enough for the φ-term. Total `< ε` for all
`s ∈ S`.

## Load-bearing Mathlib facts (to confirm during implementation)

- `MeasureTheory.tendsto_measure_cthickening` — measure of closed thickening tends to measure of the
  set (closed) as radius `→ 0⁺`. Requires a finite-measure thickening witness, available since `K`
  is bounded.
- `IsCompact.uniformContinuousOn_of_continuous` — continuity on a compact set ⟹ uniform continuity.
- `ContinuousAt.continuousWithinAt` — assemble `ContinuousOn f (J \ thickening δ₀ K)` from pointwise
  `ContinuousAt` at each point of the complement.
- `Metric.thickening` / `Metric.cthickening` and their monotonicity, openness, and
  `self_subset_thickening` / containment facts.
- The interval-integral machinery already used in the continuous proof
  (`intervalIntegral.sum_integral_adjacent_intervals`, `integral_const`,
  `norm_integral_le_of_norm_le_const`, `setIntegral_eq_integral_of_forall_compl_eq_zero`).

If a named lemma turns out to have a different signature or to be absent, the implementer reports
NEEDS_CONTEXT rather than weakening the leaf statement or hiding a `sorry` — consistent with the
project's research-leaf discipline.

## Components / file structure

Single file touched: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`. Planned `private`
helpers, each independently checkable, added above the leaf:

1. `exists_uniform_bound_on_compact` — from `hbdd` + `S` compact, a single `C` bounding `|f (s − y)|`
   for all `s ∈ S`, `y ∈ Icc (-M) M`.
2. `uniformContinuousOn_compl_thickening` — `f` is uniformly continuous on
   `J \ Metric.thickening δ₀ K` (continuity at each complement point ⟹ `ContinuousOn` ⟹ uniform on
   the compact complement).
3. `measure_badCells_small` — for the fixed null compact `K`, given `η`, a `δ₀` and an `m`-threshold
   such that the union of cells meeting `thickening δ₀ K` has measure `< η` (via
   `tendsto_measure_cthickening` + the `cthickening (δ₀+Δ)` containment).
4. The main proof of `tendstoUniformly_riemannSum_aeContinuous`, assembling the φ-term (continuous-case
   technique) and the good/bad-cell split of the f-term.

Exact lemma signatures and the inline re-derivation of the cell skeleton are fixed in the
implementation plan.

## Testing / done-criteria

- `lake build` green.
- `lean_verify UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` →
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- `lean_verify Mollify.mollify_ridge_mem_T` and `lean_verify ...leshno_dense_iff` → no `sorryAx`.
- `lean_diagnostic_messages` on the file: zero `sorry` warnings, zero errors.
- `Leshno.lean` admit inventory updated to **0 leaves**.
- All previously-proved lemmas, the leaf *statement*, the `riemannSum` def, and the continuous lemma
  byte-unchanged; no Cybenko file touched; no new import.

## Global constraints

- Do **not** modify `leshno_dense_iff`, `mollify`, `ClassM`, `T`, the leaf *statement*, the
  `riemannSum` definition, or any already-proved lemma.
- Do **not** modify existing Cybenko files.
- No new Mathlib upstream dependency; `import Mathlib` only.
- Line length ≤ 100 codepoints.
- Research-grade blockers are reported (NEEDS_CONTEXT), never hidden as `sorry` or worked around by
  weakening a statement.
- Commits unsigned for now (`--no-gpg-sign`), to be re-signed later.
