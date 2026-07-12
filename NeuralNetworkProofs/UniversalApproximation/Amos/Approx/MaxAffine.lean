/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs
import NeuralNetworkProofs.UniversalApproximation.Amos.Activation

/-!
# Max of affine functions as a convex ICNN (Amos et al.)

A finite max of affine functions `y ↦ max_i (aᵢ ⬝ᵥ y + bᵢ)` is realized by a fully input-convex
network with nonnegative propagation weights and `relu`/`id` activations, via the running-max
recursion `hₖ = max (hₖ₋₁) gₖ = gₖ + relu (hₖ₋₁ - gₖ)`. Each max-step is two width-1 layers (a
`relu` layer then an `id` layer); every `Wz` entry is `0` or `1`, and all affine data rides the
unconstrained input skip `Wy`/`bias`. Used by `Approx/Density.lean` for the UAP headline.
-/

namespace UniversalApproximation.Amos

open scoped Matrix

/-- An affine functional `y ↦ a ⬝ᵥ y + c`. -/
def dotAffine {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (y : Fin d → ℝ) : ℝ := a ⬝ᵥ y + c

/-- The max of the `n+1` affine functions `dotAffine (a i) (b i)`. -/
def maxAffine {d : ℕ} :
    (n : ℕ) → (Fin (n + 1) → (Fin d → ℝ)) → (Fin (n + 1) → ℝ) → (Fin d → ℝ) → ℝ
  | 0, a, b, y => dotAffine (a 0) (b 0) y
  | n + 1, a, b, y =>
      max (maxAffine n (fun i => a i.castSucc) (fun i => b i.castSucc) y)
        (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y)

/-- Each affine piece `i` never exceeds the max over all `n + 1` pieces. -/
theorem le_maxAffine {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (y : Fin d → ℝ) → (i : Fin (n + 1)) → dotAffine (a i) (b i) y ≤ maxAffine n a b y
  | 0, a, b, y, i => by
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi; exact le_refl _
  | n + 1, a, b, y, i => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [maxAffine]; exact le_max_right _ _
      · intro j
        simp only [maxAffine]
        exact le_trans
          (le_maxAffine n (fun i => a i.castSucc) (fun i => b i.castSucc) y j) (le_max_left _ _)

/-- Any common upper bound `c` on all affine pieces also bounds their max `maxAffine`. -/
theorem maxAffine_le {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (y : Fin d → ℝ) → (c : ℝ) → (∀ i, dotAffine (a i) (b i) y ≤ c) → maxAffine n a b y ≤ c
  | 0, a, b, y, c, h => by simpa only [maxAffine] using h 0
  | n + 1, a, b, y, c, h => by
      simp only [maxAffine]
      refine max_le ?_ (h (Fin.last (n + 1)))
      exact maxAffine_le n _ _ y c (fun j => h j.castSucc)

/-- Initial layer `0 → 1`: `id (a ⬝ᵥ y + c)` (no hidden input). -/
def initLayer {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 0 1 where
  Wz := Matrix.of (fun _ (j : Fin 0) => j.elim0)
  Wy := Matrix.of (fun _ => a)
  bias := fun _ => c
  act := id

/-- `relu` step `1 → 1`: `relu (h - (a ⬝ᵥ y + c))`. -/
def reluStep {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 1 1 where
  Wz := !![1]
  Wy := Matrix.of (fun _ => -a)
  bias := fun _ => -c
  act := relu

/-- `id` step `1 → 1`: `u + (a ⬝ᵥ y + c)`. -/
def idStep {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 1 1 where
  Wz := !![1]
  Wy := Matrix.of (fun _ => a)
  bias := fun _ => c
  act := id

/-- `initLayer`'s output on (the empty) hidden input `z` and data `y` is `a ⬝ᵥ y + c`. -/
theorem initLayer_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 0 → ℝ) (y : Fin d → ℝ) :
    (initLayer a c).toFun z y 0 = dotAffine a c y := by
  simp [ICNNLayer.toFun, initLayer, dotAffine, Matrix.mulVec, dotProduct]

/-- `reluStep`'s output on hidden input `z` and data `y` is `relu (z 0 - (a ⬝ᵥ y + c))`. -/
theorem reluStep_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (reluStep a c).toFun z y 0 = relu (z 0 - dotAffine a c y) := by
  simp only [ICNNLayer.toFun, reluStep, Matrix.mulVec, dotProduct, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    one_mul, Finset.sum_singleton, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, dotAffine]
  congr 1
  ring

/-- `idStep`'s output on hidden input `z` and data `y` is `z 0 + (a ⬝ᵥ y + c)`. -/
theorem idStep_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (idStep a c).toFun z y 0 = z 0 + dotAffine a c y := by
  simp only [ICNNLayer.toFun, idStep, Matrix.mulVec, dotProduct, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    one_mul, Finset.sum_singleton, id_eq, dotAffine]
  ring

/-- `n` max-steps folded onto a running hidden max (width 1 → 1). -/
def maxNetTail {d : ℕ} :
    (n : ℕ) → (Fin (n + 1) → (Fin d → ℝ)) → (Fin (n + 1) → ℝ) → ICNN d 1 1
  | 0, _, _ => ICNN.nil
  | n + 1, a, b =>
      .cons (reluStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1))))
        (.cons (idStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1))))
          (maxNetTail n (fun i => a i.castSucc) (fun i => b i.castSucc)))

/-- The full max-of-affine network `0 → 1`. -/
def maxNet {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) : ICNN d 0 1 :=
  .cons (initLayer (a 0) (b 0)) (maxNetTail n a b)

/-- `initLayer` is convex: it has no hidden input, and `act = id` is monotone and convex. -/
theorem initLayer_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (initLayer a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact j.elim0
  · exact id_monotone
  · exact id_convexOn

/-- `reluStep` is convex: its `Wz` entry is nonnegative, and `relu` is monotone and convex. -/
theorem reluStep_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (reluStep a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [reluStep]
  · exact relu_monotone
  · exact relu_convexOn

/-- `idStep` is convex: its `Wz` entry is nonnegative, and `act = id` is monotone and convex. -/
theorem idStep_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (idStep a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [idStep]
  · exact id_monotone
  · exact id_convexOn

/-- `maxNetTail`'s `n` max-steps are all convex, hence the whole tail is convex. -/
theorem maxNetTail_isConvex {d : ℕ} :
    (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (maxNetTail (d := d) n a b).IsConvex
  | 0, _, _ => by simp [maxNetTail, ICNN.IsConvex]
  | n + 1, a, b => by
      refine ⟨reluStep_isConvex _ _, idStep_isConvex _ _, ?_⟩
      exact maxNetTail_isConvex n _ _

/-- `maxNet` is convex: its initial layer and max-step tail are both convex. -/
theorem maxNet_isConvex {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) :
    (maxNet (d := d) n a b).IsConvex :=
  ⟨initLayer_isConvex _ _, maxNetTail_isConvex n a b⟩

/-- Real-arithmetic identity behind one running-max step: `max u v = v + relu (u - v)`. -/
theorem max_eq_add_relu (u v : ℝ) : max u v = v + relu (u - v) := by
  rw [relu]
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : u - v ≤ 0)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith : (0 : ℝ) ≤ u - v)]; ring

/-- The running max computed by `maxNetTail`, seeded by `r` and folding the affine pieces in the
same `Fin.last`-first peel order as `eval` (index `0` is left for the seed). -/
def foldMax {d : ℕ} : (n : ℕ) → (Fin (n + 1) → (Fin d → ℝ)) → (Fin (n + 1) → ℝ) →
    (Fin d → ℝ) → ℝ → ℝ
  | 0, _, _, _, r => r
  | n + 1, a, b, y, r =>
      foldMax n (fun i => a i.castSucc) (fun i => b i.castSucc) y
        (max r (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y))

/-- `maxNetTail` starting from a running hidden value `r` computes `foldMax`. -/
theorem maxNetTail_eval {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) →
    (b : Fin (n + 1) → ℝ) → (y : Fin d → ℝ) → (r : ℝ) →
    (maxNetTail n a b).eval y (fun _ => r) 0 = foldMax n a b y r
  | 0, _, _, _, _ => rfl
  | n + 1, a, b, y, r => by
      simp only [maxNetTail, ICNN.eval]
      have hz : (idStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1)))).toFun
            ((reluStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1)))).toFun (fun _ => r) y) y
          = fun _ => max r (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y) := by
        funext j
        have hj : j = 0 := Fin.fin_one_eq_zero j
        subst hj
        rw [idStep_toFun, reluStep_toFun, max_eq_add_relu, add_comm]
      rw [hz, maxNetTail_eval n _ _ y _, foldMax]

/-- Folding the pieces `1 … n` onto `max (piece 0) t` yields `max (maxAffine …) t`. -/
theorem foldMax_maxAffine {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) →
    (b : Fin (n + 1) → ℝ) → (y : Fin d → ℝ) → (t : ℝ) →
    foldMax n a b y (max (dotAffine (a 0) (b 0) y) t) = max (maxAffine n a b y) t
  | 0, _, _, _, _ => by simp only [foldMax, maxAffine]
  | n + 1, a, b, y, t => by
      have h0 : dotAffine ((fun i : Fin (n + 1) => a i.castSucc) 0)
          ((fun i : Fin (n + 1) => b i.castSucc) 0) y = dotAffine (a 0) (b 0) y := by simp
      rw [foldMax, max_assoc, ← h0,
        foldMax_maxAffine n (fun i => a i.castSucc) (fun i => b i.castSucc) y
          (max t (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y)),
        maxAffine]
      rw [max_comm t (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y), ← max_assoc]

/-- The max-of-affine network denotes exactly the max-of-affine function. -/
theorem maxNet_toFun {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ)
    (y : Fin d → ℝ) : (maxNet n a b).toFun y = maxAffine n a b y := by
  rw [ICNN.toFun, maxNet]
  simp only [ICNN.eval]
  have hinit : (initLayer (a 0) (b 0)).toFun (0 : Fin 0 → ℝ) y
      = fun _ => dotAffine (a 0) (b 0) y := by
    funext j
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    exact initLayer_toFun (a 0) (b 0) 0 y
  rw [hinit, maxNetTail_eval n a b y (dotAffine (a 0) (b 0) y),
    ← max_self (dotAffine (a 0) (b 0) y),
    foldMax_maxAffine n a b y (dotAffine (a 0) (b 0) y)]
  exact max_eq_left (le_maxAffine n a b y 0)

/-- `maxAffine` is realized by a convex ICNN. Packages `maxNet_isConvex` with `maxNet_toFun`. -/
theorem maxAffine_isICNN {d n : ℕ} (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ N.toFun = fun y => maxAffine n a b y :=
  ⟨maxNet n a b, maxNet_isConvex n a b, funext (maxNet_toFun n a b)⟩

end UniversalApproximation.Amos
