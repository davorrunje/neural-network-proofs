import Mathlib
import LeanPlayground.UniversalApproximation.Activation

/-! # Discriminatory property of sigmoidal activations (Cybenko 1989, §3). -/

namespace UniversalApproximation

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A sigmoidal function is bounded: continuity plus finite limits at ±∞. -/
theorem Sigmoidal.bounded {σ : ℝ → ℝ} (hσ : Sigmoidal σ) : ∃ C, ∀ t, |σ t| ≤ C := by
  -- Near `+∞`, `σ` is within `1` of `1`, hence `|σ| ≤ 2`.
  have hT : ∀ᶠ t in Filter.atTop, |σ t| ≤ 2 := by
    have := hσ.atTop.eventually (eventually_abs_sub_lt 1 (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with t ht
    have : |σ t - 1| < 1 := ht
    rw [abs_sub_lt_iff] at this
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  -- Near `-∞`, `σ` is within `1` of `0`, hence `|σ| ≤ 1`.
  have hB : ∀ᶠ t in Filter.atBot, |σ t| ≤ 1 := by
    have := hσ.atBot.eventually (eventually_abs_sub_lt 0 (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with t ht
    have : |σ t - 0| < 1 := ht
    simp only [sub_zero] at this
    linarith [this]
  rw [eventually_atTop] at hT
  rw [eventually_atBot] at hB
  obtain ⟨A, hA⟩ := hT
  obtain ⟨B, hBb⟩ := hB
  -- On the compact interval `[B, A]`, continuity gives a bound `C`.
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := B) (b := A)).exists_bound_of_continuousOn
    (f := σ) hσ.continuous.continuousOn
  refine ⟨max C 2, fun t => ?_⟩
  rcases le_or_gt t B with h | h
  · calc |σ t| ≤ 1 := hBb t h
      _ ≤ max C 2 := le_trans (by norm_num) (le_max_right _ _)
  rcases le_or_gt A t with h' | h'
  · exact le_trans (hA t h') (le_max_right _ _)
  · have hmem : t ∈ Set.Icc B A := ⟨le_of_lt h, le_of_lt h'⟩
    have := hC t hmem
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)

/-- As `m → ∞`, `σ (m * t + φ) → 1` when `t > 0`: the inner argument tends to `+∞`. -/
theorem sigmoidal_tendsto_pos {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) Filter.atTop (𝓝 1) := by
  have hinner : Tendsto (fun m : ℕ => (m : ℝ) * t + φ) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Tendsto.atTop_mul_const ht tendsto_natCast_atTop_atTop
  exact hσ.atTop.comp hinner

/-- As `m → ∞`, `σ (m * t + φ) → 0` when `t < 0`: the inner argument tends to `-∞`. -/
theorem sigmoidal_tendsto_neg {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : t < 0) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) Filter.atTop (𝓝 0) := by
  have hinner : Tendsto (fun m : ℕ => (m : ℝ) * t + φ) Filter.atTop Filter.atBot := by
    apply Filter.tendsto_atBot_add_const_right
    exact Tendsto.atTop_mul_neg ht tendsto_natCast_atTop_atTop tendsto_const_nhds
  exact hσ.atBot.comp hinner

end UniversalApproximation
