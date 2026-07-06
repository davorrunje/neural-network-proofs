/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic

/-!
# Saturating activations and point reflection

This file develops the foundational analysis for the Sartor et al. saturating-activation
universal approximation results (arXiv, Definition 3.3 and Proposition 3.8).

An activation `σ : ℝ → ℝ` is *right-saturating* (`σ ∈ 𝒮⁺`) if it has a finite limit at `+∞`,
and *left-saturating* (`σ ∈ 𝒮⁻`) if it has a finite limit at `−∞` (Definition 3.3).

The *point reflection* `reflect σ x = −σ(−x)` (Proposition 3.8) is an involution that preserves
monotonicity and swaps the saturation side: `σ` is left-saturating iff `reflect σ` is
right-saturating, and dually.

* `RightSaturating` — `σ` has a finite limit at `atTop` (Definition 3.3, `𝒮⁺`).
* `LeftSaturating` — `σ` has a finite limit at `atBot` (Definition 3.3 dual, `𝒮⁻`).
* `reflect` — the point reflection `x ↦ −σ(−x)` (Proposition 3.8).
* `reflect_reflect` — `reflect` is an involution.
* `reflect_monotone` — `reflect` preserves monotonicity.
* `reflect_rightSaturating` / `reflect_leftSaturating` — `reflect` swaps the saturation side.
-/

namespace UniversalApproximation.Monotone

open Filter Topology

/-- Definition 3.3 (`𝒮⁺`): an activation `σ` is *right-saturating* if it has a finite limit as
its argument tends to `+∞`. -/
def RightSaturating (σ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto σ Filter.atTop (nhds L)

/-- Definition 3.3 (dual, `𝒮⁻`): an activation `σ` is *left-saturating* if it has a finite limit
as its argument tends to `−∞`. -/
def LeftSaturating (σ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto σ Filter.atBot (nhds L)

/-- Proposition 3.8: the *point reflection* of an activation, `reflect σ x = −σ(−x)`. -/
def reflect (σ : ℝ → ℝ) : ℝ → ℝ := fun x => -σ (-x)

/-- The point reflection is an involution: `reflect (reflect σ) = σ`. -/
theorem reflect_reflect (σ : ℝ → ℝ) : reflect (reflect σ) = σ := by
  funext x
  simp only [reflect, neg_neg]

/-- Proposition 3.8: the point reflection of a monotone activation is monotone. -/
theorem reflect_monotone {σ : ℝ → ℝ} (hσ : Monotone σ) : Monotone (reflect σ) := by
  intro a b h
  simp only [reflect, neg_le_neg_iff]
  exact hσ (neg_le_neg h)

/-- Proposition 3.8 (`σ ∈ 𝒮⁻ → reflect σ ∈ 𝒮⁺`): if `σ` is left-saturating, then its point
reflection is right-saturating. -/
theorem reflect_rightSaturating {σ : ℝ → ℝ} (h : LeftSaturating σ) :
    RightSaturating (reflect σ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨-L, ?_⟩
  have hneg : Filter.Tendsto (fun x : ℝ => -x) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr Filter.tendsto_id
  exact (hL.comp hneg).neg

/-- Proposition 3.8 (`σ ∈ 𝒮⁺ → reflect σ ∈ 𝒮⁻`): if `σ` is right-saturating, then its point
reflection is left-saturating. -/
theorem reflect_leftSaturating {σ : ℝ → ℝ} (h : RightSaturating σ) :
    LeftSaturating (reflect σ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨-L, ?_⟩
  have hneg : Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
    Filter.tendsto_neg_atTop_iff.mpr Filter.tendsto_id
  exact (hL.comp hneg).neg

/-- Proposition 3.8 (biconditional): `reflect σ` is right-saturating iff `σ` is left-saturating. -/
theorem reflect_rightSaturating_iff {σ : ℝ → ℝ} :
    RightSaturating (reflect σ) ↔ LeftSaturating σ :=
  ⟨fun h => reflect_reflect σ ▸ reflect_leftSaturating h, reflect_rightSaturating⟩

/-- Proposition 3.8 (biconditional): `reflect σ` is left-saturating iff `σ` is right-saturating. -/
theorem reflect_leftSaturating_iff {σ : ℝ → ℝ} :
    LeftSaturating (reflect σ) ↔ RightSaturating σ :=
  ⟨fun h => reflect_reflect σ ▸ reflect_rightSaturating h, reflect_leftSaturating⟩

/-!
## Quantitative half-space limit (Lemma 3.6, ε-form)

The lemmas below turn the *qualitative* saturation limits of Definition 3.3 into the
*quantitative* estimates the interpolation construction needs. Reading a layer-1 neuron as
`t ↦ σ (λ · t)` with gain `λ`, a right-saturating activation is driven within `ε` of its
right limit `L⁺` on the half-line `t ≥ m > 0`, uniformly, once the gain exceeds a threshold
`Λ` depending only on `ε` and the margin `m`. Dually for left-saturating activations on
`t ≤ -m`. Task 4 instantiates `m` at the finite dataset's separation margin.
-/

/-- The `ε`-`M` unpacking of a right-saturation limit: if `σ` tends to `L` at `+∞`, then for
every `ε > 0` there is a threshold `M` beyond which `σ` stays within `ε` of `L`. -/
theorem rightSaturating_eventually {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atTop (nhds L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ z : ℝ, M ≤ z → |σ z - L| ≤ ε := by
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨M, hM⟩ := hL ε hε
  refine ⟨M, fun z hz => ?_⟩
  have := hM z hz
  rw [Real.dist_eq] at this
  exact le_of_lt this

/-- Lemma 3.6 (ε-form, right-saturating). For a right-saturating activation with right limit
`L⁺`, any target accuracy `ε > 0`, and any positive margin `m`, there is a gain threshold
`Λ > 0` such that for every gain `λ ≥ Λ` and every input `t ≥ m`, the scaled neuron `σ (λ · t)`
lies within `ε` of `L⁺`. This is the quantitative form of the half-space limit: a large gain
drives the activation to its saturation value off the margin. -/
theorem rightSaturating_scaled_approx {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atTop (nhds L)) {ε m : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, m ≤ t → |σ (lam * t) - L| ≤ ε := by
  obtain ⟨M, hM⟩ := rightSaturating_eventually hL hε
  refine ⟨max 1 (M / m), lt_of_lt_of_le one_pos (le_max_left _ _), fun lam hlam t ht => ?_⟩
  have hΛpos : 0 < lam := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hlam
  apply hM
  -- Goal: M ≤ lam * t. First M ≤ lam * m, then lam * m ≤ lam * t.
  have hMm : M / m ≤ lam := le_trans (le_max_right _ _) hlam
  have h1 : M ≤ lam * m := by
    rw [div_le_iff₀ hm] at hMm
    linarith [hMm]
  have h2 : lam * m ≤ lam * t := by
    apply mul_le_mul_of_nonneg_left ht (le_of_lt hΛpos)
  linarith

/-- The `ε`-`M` unpacking of a left-saturation limit: if `σ` tends to `L` at `−∞`, then for
every `ε > 0` there is a threshold `M` below which `σ` stays within `ε` of `L`. -/
theorem leftSaturating_eventually {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atBot (nhds L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ z : ℝ, z ≤ M → |σ z - L| ≤ ε := by
  have hball : ∀ᶠ z in Filter.atBot, σ z ∈ Metric.ball L ε :=
    hL.eventually (Metric.ball_mem_nhds L hε)
  obtain ⟨M, hM⟩ := Filter.eventually_atBot.mp hball
  refine ⟨M, fun z hz => ?_⟩
  have := hM z hz
  rw [Metric.mem_ball, Real.dist_eq] at this
  exact le_of_lt this

/-- Lemma 3.6 (ε-form, left-saturating). For a left-saturating activation with left limit `L⁻`,
any target accuracy `ε > 0`, and any positive margin `m`, there is a gain threshold `Λ > 0` such
that for every gain `λ ≥ Λ` and every input `t ≤ -m`, the scaled neuron `σ (λ · t)` lies within
`ε` of `L⁻`. This is the dual of `rightSaturating_scaled_approx` on the left half-line. -/
theorem leftSaturating_scaled_approx {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atBot (nhds L)) {ε m : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, t ≤ -m → |σ (lam * t) - L| ≤ ε := by
  obtain ⟨M, hM⟩ := leftSaturating_eventually hL hε
  refine ⟨max 1 (-M / m), lt_of_lt_of_le one_pos (le_max_left _ _), fun lam hlam t ht => ?_⟩
  have hΛpos : 0 < lam := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hlam
  apply hM
  -- Goal: lam * t ≤ M. First lam * t ≤ lam * (-m) = -(lam * m), then -(lam * m) ≤ M.
  have hMm : -M / m ≤ lam := le_trans (le_max_right _ _) hlam
  have h1 : -M ≤ lam * m := by
    rw [div_le_iff₀ hm] at hMm
    linarith [hMm]
  have h2 : lam * t ≤ lam * (-m) := by
    apply mul_le_mul_of_nonneg_left ht (le_of_lt hΛpos)
  have h3 : lam * (-m) = -(lam * m) := by ring
  linarith

/-- Two-sided quantitative half-space limit (Lemma 3.6, combined). For an activation that is both
right- and left-saturating, a single gain threshold `Λ > 0` drives the scaled neuron `σ (λ · t)`
within `ε` of the right limit `L⁺` on `t ≥ m` and within `ε` of the left limit `L⁻` on `t ≤ -m`,
for every gain `λ ≥ Λ`. This packages both half-lines under one threshold for downstream use. -/
theorem saturating_scaled_approx_two_sided {σ : ℝ → ℝ} {Lp Lm : ℝ}
    (hLp : Filter.Tendsto σ Filter.atTop (nhds Lp))
    (hLm : Filter.Tendsto σ Filter.atBot (nhds Lm)) {ε m : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧
      (∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, m ≤ t → |σ (lam * t) - Lp| ≤ ε) ∧
      (∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, t ≤ -m → |σ (lam * t) - Lm| ≤ ε) := by
  obtain ⟨Λp, hΛp_pos, hΛp⟩ := rightSaturating_scaled_approx hLp hε hm
  obtain ⟨Λm, hΛm_pos, hΛm⟩ := leftSaturating_scaled_approx hLm hε hm
  refine ⟨max Λp Λm, lt_of_lt_of_le hΛp_pos (le_max_left _ _), ?_, ?_⟩
  · exact fun lam hlam t ht => hΛp lam (le_trans (le_max_left _ _) hlam) t ht
  · exact fun lam hlam t ht => hΛm lam (le_trans (le_max_right _ _) hlam) t ht

/-!
## Intersection via saturation (Lemma 3.7, ε-form)

The layer-2 units of the interpolation construction take a *non-negative combination* of the
layer-1 half-space values and pass it through a saturating activation. The paper reads such a
unit as `σ (b + λ · ∑ᵢ hᵢ)`, where `A` is the intersection of the half-spaces:

* *inside* `A` every input `hᵢ = 0`, so the pre-activation is exactly `b` and the unit outputs
  the constant `γ = σ b`;
* *outside* `A` at least one input `hᵢ` is bounded away from `0` on the saturating side (here
  `hᵢ ≤ -m < 0`), while the remaining inputs are still on that side (`hᵢ ≤ 0`), so the whole sum
  is `≤ -m` and a large gain drives the pre-activation to `-∞`, where a left-saturating `σ` with
  `σ(-∞) = 0` outputs a value within `ε` of `0`.

The crux Task 4 needs is the *outside-`A` vanishing*, stated quantitatively below. The inside
value is the exact identity `σ (lam * 0 + b) = σ b`, recorded separately. The right-saturating
dual (`σ(+∞) = 0`, inputs `hᵢ ≥ 0` with one `≥ m`) is handled analogously via `reflect`-style
symmetry, stated directly here.
-/

/-- Combinatorial core of the outside-`A` bound: over a finite index set `s`, if every input
`h i` is non-positive and some distinguished index `j ∈ s` has `h j ≤ -m`, then the whole sum is
`≤ -m`. This packages the "one coordinate saturates, the rest do not fight it" structure of a
non-negative combination of half-space indicators. -/
theorem sum_le_neg_of_single {ι : Type*} (s : Finset ι) (h : ι → ℝ) {m : ℝ}
    {j : ι} (hj : j ∈ s) (hjm : h j ≤ -m) (hnonpos : ∀ i ∈ s, h i ≤ 0) :
    ∑ i ∈ s, h i ≤ -m := by
  classical
  rw [← Finset.add_sum_erase s h hj]
  have hrest : ∑ i ∈ s.erase j, h i ≤ 0 :=
    Finset.sum_nonpos fun i hi => hnonpos i (Finset.mem_of_mem_erase hi)
  linarith

/-- Bias-inclusive left-saturation estimate. If `σ` tends to `L` at `−∞`, then for every target
accuracy `ε > 0`, every positive margin `m`, and every bias `b`, there is a gain threshold
`Λ > 0` such that for all gains `λ ≥ Λ` and all inputs `t ≤ -m`, the biased scaled pre-activation
`σ (λ · t + b)` lies within `ε` of `L`. This is `leftSaturating_scaled_approx` with an additive
bias absorbed into the threshold. -/
theorem leftSaturating_scaled_approx_bias {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atBot (nhds L)) {ε m b : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, t ≤ -m → |σ (lam * t + b) - L| ≤ ε := by
  obtain ⟨M, hM⟩ := leftSaturating_eventually hL hε
  refine ⟨max 1 ((b - M) / m), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun lam hlam t ht => ?_⟩
  have hΛpos : 0 < lam := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hlam
  apply hM
  -- Goal: lam * t + b ≤ M.  We have t ≤ -m, so lam * t ≤ -(lam * m), and lam ≥ (b - M)/m.
  have hMm : (b - M) / m ≤ lam := le_trans (le_max_right _ _) hlam
  have h1 : b - M ≤ lam * m := by
    rw [div_le_iff₀ hm] at hMm
    linarith [hMm]
  have h2 : lam * t ≤ lam * (-m) := mul_le_mul_of_nonneg_left ht (le_of_lt hΛpos)
  have h3 : lam * (-m) = -(lam * m) := by ring
  linarith

/-- Lemma 3.7 (ε-form, left-saturating / `𝒮⁻` side), *outside `A`*. Let `σ` be left-saturating
with `σ(-∞) = 0`, let `s` be the finite family of layer-1 inputs, `b` a bias, and `m > 0` a
margin. Then there is a gain threshold `Λ > 0` such that for every gain `λ ≥ Λ`, whenever the
inputs `h : ι → ℝ` witness *being outside the intersection* — every `h i ≤ 0` and some `j ∈ s`
has `h j ≤ -m` — the saturating unit `σ (λ · ∑ᵢ hᵢ + b)` is within `ε` of `0`.

This is the crux the interpolation read-out consumes: off the margin, the intersection unit
vanishes to within `ε`. The gain threshold depends only on `ε`, `m`, and `b`, uniformly over
all outside-`A` input configurations. -/
theorem leftSaturating_intersection_vanishes {σ : ℝ → ℝ}
    (hL : Filter.Tendsto σ Filter.atBot (nhds 0)) {ι : Type*} (s : Finset ι) {ε m b : ℝ}
    (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ h : ι → ℝ, (∀ i ∈ s, h i ≤ 0) →
      (∃ j ∈ s, h j ≤ -m) → |σ (lam * (∑ i ∈ s, h i) + b) - 0| ≤ ε := by
  obtain ⟨Λ, hΛpos, hΛ⟩ := leftSaturating_scaled_approx_bias (b := b) hL hε hm
  refine ⟨Λ, hΛpos, fun lam hlam h hnonpos hout => ?_⟩
  obtain ⟨j, hj, hjm⟩ := hout
  exact hΛ lam hlam _ (sum_le_neg_of_single s h hj hjm hnonpos)

/-- Lemma 3.7 (ε-form), *inside `A`*: when all inputs vanish (`h i = 0` for `i ∈ s`, the exact
inside-intersection condition), the saturating unit outputs the exact constant `σ b = γ`, with no
dependence on the gain `λ`. This is the companion of `leftSaturating_intersection_vanishes`
recording the interior value the read-out weights against. -/
theorem intersection_inside_value {σ : ℝ → ℝ} {ι : Type*} (s : Finset ι) (h : ι → ℝ)
    (b lam : ℝ) (hzero : ∀ i ∈ s, h i = 0) :
    σ (lam * (∑ i ∈ s, h i) + b) = σ b := by
  rw [Finset.sum_eq_zero hzero]
  simp

/-- Bias-inclusive right-saturation estimate (dual of `leftSaturating_scaled_approx_bias`). If
`σ` tends to `L` at `+∞`, then for every accuracy `ε > 0`, margin `m > 0`, and bias `b`, there is
a gain threshold `Λ > 0` with `|σ (λ · t + b) - L| ≤ ε` for all `λ ≥ Λ` and `t ≥ m`. -/
theorem rightSaturating_scaled_approx_bias {σ : ℝ → ℝ} {L : ℝ}
    (hL : Filter.Tendsto σ Filter.atTop (nhds L)) {ε m b : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, m ≤ t → |σ (lam * t + b) - L| ≤ ε := by
  obtain ⟨M, hM⟩ := rightSaturating_eventually hL hε
  refine ⟨max 1 ((M - b) / m), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun lam hlam t ht => ?_⟩
  have hΛpos : 0 < lam := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hlam
  apply hM
  -- Goal: M ≤ lam * t + b.  We have t ≥ m, so lam * t ≥ lam * m, and lam ≥ (M - b)/m.
  have hMm : (M - b) / m ≤ lam := le_trans (le_max_right _ _) hlam
  have h1 : M - b ≤ lam * m := by
    rw [div_le_iff₀ hm] at hMm
    linarith [hMm]
  have h2 : lam * m ≤ lam * t := mul_le_mul_of_nonneg_left ht (le_of_lt hΛpos)
  linarith

/-- Combinatorial core of the outside-`A` bound, right-saturating side: if every input `h i` is
non-negative and some `j ∈ s` has `h j ≥ m`, then the whole sum is `≥ m`. -/
theorem sum_ge_of_single {ι : Type*} (s : Finset ι) (h : ι → ℝ) {m : ℝ}
    {j : ι} (hj : j ∈ s) (hjm : m ≤ h j) (hnonneg : ∀ i ∈ s, 0 ≤ h i) :
    m ≤ ∑ i ∈ s, h i := by
  classical
  rw [← Finset.add_sum_erase s h hj]
  have hrest : 0 ≤ ∑ i ∈ s.erase j, h i :=
    Finset.sum_nonneg fun i hi => hnonneg i (Finset.mem_of_mem_erase hi)
  linarith

/-- Lemma 3.7 (ε-form, right-saturating / `𝒮⁺` side), *outside `A`*. Dual of
`leftSaturating_intersection_vanishes`: for a right-saturating `σ` with `σ(+∞) = 0`, if every
input `h i ≥ 0` and some `j ∈ s` has `h j ≥ m`, then a large gain drives the unit
`σ (λ · ∑ᵢ hᵢ + b)` to within `ε` of `0`. -/
theorem rightSaturating_intersection_vanishes {σ : ℝ → ℝ}
    (hL : Filter.Tendsto σ Filter.atTop (nhds 0)) {ι : Type*} (s : Finset ι) {ε m b : ℝ}
    (hε : 0 < ε) (hm : 0 < m) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ h : ι → ℝ, (∀ i ∈ s, 0 ≤ h i) →
      (∃ j ∈ s, m ≤ h j) → |σ (lam * (∑ i ∈ s, h i) + b) - 0| ≤ ε := by
  obtain ⟨Λ, hΛpos, hΛ⟩ := rightSaturating_scaled_approx_bias (b := b) hL hε hm
  refine ⟨Λ, hΛpos, fun lam hlam h hnonneg hout => ?_⟩
  obtain ⟨j, hj, hjm⟩ := hout
  exact hΛ lam hlam _ (sum_ge_of_single s h hj hjm hnonneg)

/-!
## Approximate interior value (rigorous interior for the Lemma 3.7 chaining)

Lemma 3.7's interior claim `hᵢ ≈ 0 ⇒ σ (λ·∑ hᵢ + b) ≈ σ b` is valid only when the pre-activation
stays near the bias `b`. Since `σ` here is merely monotone (possibly discontinuous), the interior
argument needs `σ` continuous at `b`; then a standard ε-δ bound controls the interior value. In the
depth-4 assembly `b` is chosen at a continuity point of `σ` (monotone ⇒ continuity points dense), so
no extra global hypothesis on `σ` is imposed.
-/

/-- Continuity of `σ` at `b`, in the ε-δ form the interior argument consumes: within radius `δ` of
`b`, the activation stays within `ε` of its interior value `σ b`. -/
theorem approx_interior_value {σ : ℝ → ℝ} {b : ℝ} (hcont : ContinuousAt σ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - b| ≤ δ → |σ t - σ b| ≤ ε := by
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ε hε
  refine ⟨δ / 2, half_pos hδpos, fun t ht => ?_⟩
  have hlt : |t - b| < δ := lt_of_le_of_lt ht (half_lt_self hδpos)
  have hdist_in : dist t b < δ := by rw [Real.dist_eq]; exact hlt
  have hdist_out := hδ hdist_in
  rw [Real.dist_eq] at hdist_out
  exact le_of_lt hdist_out

end UniversalApproximation.Monotone
