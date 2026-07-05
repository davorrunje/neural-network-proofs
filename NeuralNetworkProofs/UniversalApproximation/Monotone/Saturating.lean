/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib

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

end UniversalApproximation.Monotone
