/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic

/-!
# ε-indicators and the domination gadget

This file introduces the *ε-indicator* abstraction and instantiates it with the two-layer
threshold gadget from the Mikulincer–Reichman construction (arXiv:2207.05275, Result 1, paper
layers 1–2).

An `ActStack` is an *ε-indicator* for a family of points `p : Fin n → (Fin d → ℝ)` when its output
coordinate `i` approximates the *domination indicator* of `p i` — the function that is `1` exactly
when the input `x` dominates `p i` coordinatewise (`p i ≤ x` in the Pi order) and `0` otherwise —
uniformly to accuracy `ε`.  The threshold gadget realizes this indicator *exactly* (accuracy `0`).

The middle layer of the gadget carries `n * d` neurons, one per pair `(i, r)` of point index and
coordinate.  To avoid reasoning through the flattening `Fin (n * d)`, both layers are described by
*curried* weight/bias data on `Fin n × Fin d`, flattened to `Fin (n * d)` only at the layer's type
boundary via `finProdFinEquiv`.  The `_apply` proofs then reindex the middle sums with
`finProdFinEquiv` and `Fintype.sum_prod_type`, so the block structure is visible directly.

* `IsEpsIndicator` — a monotone stack approximating the domination indicators of `p` to accuracy ε.
* `dominationStack` — the two-layer threshold stack (built with `heaviside` at each layer).
* `dominationStack_depth` — its depth is `2`.
* `dominationStack_isMonotone` — its weights are non-negative and its activations monotone.
* `dominationStack_apply` — its output coordinate `i` is `if p i ≤ x then 1 else 0`.
* `dominationStack_isEpsIndicator` — the gadget is an *exact* (`ε = 0`) indicator for `p`.
-/

namespace UniversalApproximation.MikulincerReichman

open UniversalApproximation.Monotone
open scoped BigOperators

open Classical in
/-- An activation stack `S : ActStack d n` is an *ε-indicator* for the points
`p : Fin n → (Fin d → ℝ)` when, for every input `x`, its output coordinate `i` approximates the
domination indicator of `p i` — `1` if `p i ≤ x` coordinatewise, else `0` — to within `ε`.

Forward-facing API for the Sartor co-design: not consumed internally at present. -/
def IsEpsIndicator {d n : ℕ} (S : ActStack d n) (p : Fin n → (Fin d → ℝ)) (ε : ℝ) : Prop :=
  ∀ x i, |S.toFun x i - (if p i ≤ x then 1 else 0)| ≤ ε

/-- Layer 1 of the domination gadget: `Layer d (n * d)`. The neuron flattened from the pair
`(i, r)` copies coordinate `r` of the input (weight row `eᵣ`) and subtracts `(p i) r` (as bias),
so under `heaviside` it fires iff `x r ≥ (p i) r`. The weights and bias are described by currying:
they read the pair `finProdFinEquiv.symm q` and are flattened only through `finProdFinEquiv`. -/
noncomputable def dominationLayer1 {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    NeuralNetwork.Layer d (n * d) where
  W := fun q k => if k = (finProdFinEquiv.symm q).2 then 1 else 0
  c := fun q => -(p (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2

/-- Layer 2 of the domination gadget: `Layer (n * d) n`. Neuron `i` sums the `d` coordinate
indicators belonging to point `i` and thresholds at `d` (bias `-d`), so under `heaviside` it fires
iff all `d` coordinates of `p i` are dominated. The weight is `1` exactly on the block of neurons
whose curried point index is `i`. -/
noncomputable def dominationLayer2 (d : ℕ) {n : ℕ} :
    NeuralNetwork.Layer (n * d) n where
  W := fun i q => if (finProdFinEquiv.symm q).1 = i then 1 else 0
  c := fun _ => -(d : ℝ)

/-- The two-layer domination gadget for the points `p`, built on the generalized activation stack
with `heaviside` at every layer. Its output coordinate `i` is the domination indicator of `p i`. -/
noncomputable def dominationStack {d n : ℕ} (p : Fin n → (Fin d → ℝ)) : ActStack d n :=
  .cons (dominationLayer1 p) heaviside (.cons (dominationLayer2 d) heaviside (.nil n))

/-- The domination gadget is a depth-`2` activation stack. -/
theorem dominationStack_depth {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    (dominationStack p).depth = 2 := rfl

/-- The domination gadget has non-negative weights and monotone (`heaviside`) activations, hence
is a monotone stack. -/
theorem dominationStack_isMonotone {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    (dominationStack p).IsMonotone := by
  refine ⟨⟨heaviside_monotone, ?_⟩, ⟨heaviside_monotone, ?_⟩, trivial⟩
  · intro q k
    unfold dominationLayer1
    dsimp only
    split_ifs <;> norm_num
  · intro i q
    unfold dominationLayer2
    dsimp only
    split_ifs <;> norm_num

/-- The output of layer 1 at the neuron flattened from `(i, r)` is `heaviside (x r - (p i) r)`.
Stated on the curried index `finProdFinEquiv (i, r)` so `Equiv.symm_apply_apply` collapses the
weight/bias lookup back to the pair. -/
private theorem dominationLayer1_apply {d n : ℕ} (p : Fin n → (Fin d → ℝ))
    (x : Fin d → ℝ) (i : Fin n) (r : Fin d) :
    (dominationLayer1 p).toFun heaviside x (finProdFinEquiv (i, r))
      = heaviside (x r - (p i) r) := by
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
  change (dominationLayer2 d).toFun heaviside
    ((dominationLayer1 p).toFun heaviside x) i = _
  -- output of layer 2 at neuron `i`
  rw [NeuralNetwork.Layer.toFun]
  -- reindex the middle sum by `(j, r)` and collapse the block for `j = i`
  have hsum : (Matrix.mulVec (dominationLayer2 d).W
        ((dominationLayer1 p).toFun heaviside x) i)
      = ∑ r : Fin d, heaviside (x r - (p i) r) := by
    rw [Matrix.mulVec]
    simp only [dotProduct, dominationLayer2]
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Equiv.symm_apply_apply, dominationLayer1_apply, if_pos rfl, one_mul]
    · intro j _ hj
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [Equiv.symm_apply_apply, if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  -- now `heaviside (∑ - d) = 1` iff `∑ ≥ d` iff `p i ≤ x`
  change heaviside ((∑ r : Fin d, heaviside (x r - (p i) r))
    + (dominationLayer2 d).c i) = _
  simp only [dominationLayer2]
  rw [heaviside, show (∑ r : Fin d, heaviside (x r - (p i) r)) + -(d : ℝ)
        = (∑ r : Fin d, heaviside (x r - (p i) r)) - d by ring]
  have hcard : (d : ℝ) = (Fintype.card (Fin d) : ℝ) := by rw [Fintype.card_fin]
  simp only [sub_nonneg, hcard, sum_le_one_card_le_iff (fun r => heaviside_le_one _), Pi.le_def]
  -- both conditions are `∀`s; show them equivalent coordinatewise, branches are equal
  refine if_congr (forall_congr' fun r => ?_) rfl rfl
  rw [heaviside_eq_one_iff, sub_nonneg]

/-- The domination gadget is an *exact* ε-indicator for `p`: each output coordinate equals the
domination indicator on the nose, so the ε bound holds with `ε = 0`. Immediate from
`dominationStack_apply`, since `|a - a| = 0 ≤ 0`.

Forward-facing API for the Sartor co-design: not consumed internally at present. -/
theorem dominationStack_isEpsIndicator {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    IsEpsIndicator (dominationStack p) p 0 := by
  intro x i
  rw [dominationStack_apply, sub_self, abs_zero]

end UniversalApproximation.MikulincerReichman
