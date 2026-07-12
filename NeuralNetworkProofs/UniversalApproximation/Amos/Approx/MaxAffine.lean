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

theorem initLayer_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 0 → ℝ) (y : Fin d → ℝ) :
    (initLayer a c).toFun z y 0 = dotAffine a c y := by
  simp [ICNNLayer.toFun, initLayer, dotAffine, Matrix.mulVec, dotProduct]

theorem reluStep_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (reluStep a c).toFun z y 0 = relu (z 0 - dotAffine a c y) := by
  simp [ICNNLayer.toFun, reluStep, dotAffine, Matrix.mulVec, dotProduct]
  ring_nf

theorem idStep_toFun {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (idStep a c).toFun z y 0 = z 0 + dotAffine a c y := by
  simp [ICNNLayer.toFun, idStep, dotAffine, Matrix.mulVec, dotProduct]
  ring_nf

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

theorem initLayer_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (initLayer a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact j.elim0
  · exact id_monotone
  · exact id_convexOn

theorem reluStep_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (reluStep a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [reluStep]
  · exact relu_monotone
  · exact relu_convexOn

theorem idStep_isConvex {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : (idStep a c).IsConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [idStep]
  · exact id_monotone
  · exact id_convexOn

theorem maxNetTail_isConvex {d : ℕ} :
    (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (maxNetTail (d := d) n a b).IsConvex
  | 0, _, _ => by simp [maxNetTail, ICNN.IsConvex]
  | n + 1, a, b => by
      refine ⟨reluStep_isConvex _ _, idStep_isConvex _ _, ?_⟩
      exact maxNetTail_isConvex n _ _

theorem maxNet_isConvex {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) :
    (maxNet (d := d) n a b).IsConvex :=
  ⟨initLayer_isConvex _ _, maxNetTail_isConvex n a b⟩

end UniversalApproximation.Amos
