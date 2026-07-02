/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs

/-!
# The domination gadget

This file builds the two-layer threshold gadget from the Mikulincer–Reichman construction
(arXiv:2207.05275, Result 1, paper layers 1–2). Given finitely many points
`p : Fin n → (Fin d → ℝ)`, `dominationStack p` is a depth-`2` threshold stack whose output
coordinate `i` is the *domination indicator* of `p i`: it is `1` exactly when the input `x`
dominates `p i` coordinatewise (`p i ≤ x` in the Pi order) and `0` otherwise.

* `dominationStack` — the two-layer threshold stack.
* `dominationStack_depth` — its depth is `2`.
* `dominationStack_isMonotone` — its weights are non-negative.
* `dominationStack_apply` — its output coordinate `i` is `if p i ≤ x then 1 else 0`.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- Sum of threshold values over `Fin d`: since each `θ (x r - (p i) r) ≤ 1`, the sum is at
most `d`, and reaches `d` exactly when every term is `1`, i.e. when `p i ≤ x`. -/
private theorem sum_thresh_ge_iff {d : ℕ} (x q : Fin d → ℝ) :
    (d : ℝ) ≤ ∑ r, θ (x r - q r) ↔ ∀ r, q r ≤ x r := by
  constructor
  · intro hsum r
    by_contra hlt
    rw [not_le] at hlt
    -- the `r`th term is `0` while all others are `≤ 1`, so the sum is `< d`
    have hr : θ (x r - q r) = 0 := by
      unfold θ; rw [if_neg]; linarith
    have hbound : ∑ s, θ (x s - q s) < d := by
      calc ∑ s, θ (x s - q s)
          < ∑ _s : Fin d, (1 : ℝ) := by
            apply Finset.sum_lt_sum
            · intro s _; exact θ_le_one _
            · exact ⟨r, Finset.mem_univ r, by rw [hr]; norm_num⟩
        _ = d := by simp
    linarith
  · intro hle
    have hone : ∀ r, θ (x r - q r) = 1 := by
      intro r; unfold θ; rw [if_pos]; linarith [hle r]
    have heq : (d : ℝ) = ∑ r, θ (x r - q r) := by
      rw [Finset.sum_congr rfl (fun r _ => hone r)]
      simp
    exact heq.le

/-- Layer 1 of the domination gadget: `Layer d (n * d)`. Neuron `finProdFinEquiv (i, r)`
copies coordinate `r` of the input (weight row `eᵣ`) and subtracts `(p i) r` (as bias), so
under `θ` it fires iff `x r ≥ (p i) r`. -/
noncomputable def dominationLayer1 {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    NeuralNetwork.Layer d (n * d) where
  W := fun q k => if k = (finProdFinEquiv.symm q).2 then 1 else 0
  c := fun q => -(p (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2

/-- Layer 2 of the domination gadget: `Layer (n * d) n`. Neuron `i` sums the `d` coordinate
indicators belonging to point `i` and thresholds at `d` (bias `-d`), so under `θ` it fires iff
all `d` coordinates of `p i` are dominated. -/
noncomputable def dominationLayer2 (d : ℕ) {n : ℕ} :
    NeuralNetwork.Layer (n * d) n where
  W := fun i q => if (finProdFinEquiv.symm q).1 = i then 1 else 0
  c := fun _ => -(d : ℝ)

/-- The two-layer domination gadget for the points `p`. Its output coordinate `i` is the
domination indicator of `p i`. -/
noncomputable def dominationStack {d n : ℕ} (p : Fin n → (Fin d → ℝ)) : ThreshStack d n :=
  .cons (dominationLayer1 p) (.cons (dominationLayer2 d) (.nil n))

/-- The domination gadget is a depth-`2` threshold stack. -/
theorem dominationStack_depth {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    (dominationStack p).depth = 2 := rfl

/-- The domination gadget has non-negative weights, hence is a monotone threshold stack. -/
theorem dominationStack_isMonotone {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    (dominationStack p).IsMonotone := by
  refine ⟨?_, ?_, trivial⟩
  · intro q k
    unfold dominationLayer1
    dsimp only
    split_ifs <;> norm_num
  · intro i q
    unfold dominationLayer2
    dsimp only
    split_ifs <;> norm_num

/-- The output of layer 1 at neuron `finProdFinEquiv (i, r)` is `θ (x r - (p i) r)`. -/
private theorem dominationLayer1_apply {d n : ℕ} (p : Fin n → (Fin d → ℝ))
    (x : Fin d → ℝ) (i : Fin n) (r : Fin d) :
    (dominationLayer1 p).toFun θ x (finProdFinEquiv (i, r)) = θ (x r - (p i) r) := by
  unfold NeuralNetwork.Layer.toFun dominationLayer1
  congr 1
  rw [Matrix.mulVec]
  simp only [dotProduct, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single r]
  · rw [if_pos rfl]; ring
  · intro k _ hk; rw [if_neg hk]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

open Classical in
/-- The domination gadget's output coordinate `i` is `1` iff `x` dominates `p i`
coordinatewise, and `0` otherwise. -/
theorem dominationStack_apply {d n : ℕ} (p : Fin n → (Fin d → ℝ))
    (x : Fin d → ℝ) (i : Fin n) :
    (dominationStack p).toFun x i = if p i ≤ x then 1 else 0 := by
  change (dominationLayer2 d).toFun θ ((dominationLayer1 p).toFun θ x) i = _
  -- output of layer 2 at neuron `i`
  rw [NeuralNetwork.Layer.toFun]
  -- compute the mulVec sum: it selects the `d` coordinate indicators of point `i`
  have hsum : (Matrix.mulVec (dominationLayer2 d).W
        ((dominationLayer1 p).toFun θ x) i)
      = ∑ r : Fin d, θ (x r - (p i) r) := by
    rw [Matrix.mulVec]
    simp only [dotProduct, dominationLayer2]
    rw [← finProdFinEquiv.sum_comp
        (fun q => (if (finProdFinEquiv.symm q).1 = i then 1 else 0)
          * (dominationLayer1 p).toFun θ x q)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · congr 1
      ext r
      rw [dominationLayer1_apply]
      simp
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro r _
      rw [Equiv.symm_apply_apply]
      dsimp only
      rw [if_neg hj]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  -- now `θ (∑ - d) = 1` iff `∑ ≥ d` iff `p i ≤ x`
  change θ ((∑ r : Fin d, θ (x r - (p i) r)) + (dominationLayer2 d).c i) = _
  simp only [dominationLayer2]
  rw [θ, show (∑ r : Fin d, θ (x r - (p i) r)) + -(d : ℝ)
        = (∑ r : Fin d, θ (x r - (p i) r)) - d by ring]
  simp only [sub_nonneg, sum_thresh_ge_iff, Pi.le_def]

end UniversalApproximation.Monotone
