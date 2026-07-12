/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Matrix.ToLin
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs

/-!
# Fully input-convex neural networks — soundness (Amos et al.)

A fully input-convex network (`ICNN.IsConvex`: nonnegative propagation weights `Wz`, convex and
nondecreasing activations) denotes a convex function of its input.  The headline
`icnn_convex` proves `ConvexOn ℝ Set.univ N.toFun` for `N : ICNN d 0 1`.

The argument is the classical FICNN soundness induction: convexity is preserved through each layer
because (i) `Wz ≥ 0` keeps the propagated term `Wz z` a nonnegative combination of convex
coordinate maps, (ii) the input skip `Wy y` is linear hence convex, and (iii) post-composition with
a convex nondecreasing activation preserves convexity (`convexOn_comp_univ`).
-/

namespace UniversalApproximation.Amos

open scoped BigOperators

/-- The `j`-th coordinate of `W.mulVec ·` is a convex (indeed linear) functional. -/
theorem linear_coord_convexOn {d b : ℕ} (W : Matrix (Fin b) (Fin d) ℝ) (j : Fin b) :
    ConvexOn ℝ Set.univ (fun y : Fin d → ℝ => (W.mulVec y) j) := by
  have heq : (fun y : Fin d → ℝ => (W.mulVec y) j)
      = ⇑((LinearMap.proj j).comp (Matrix.mulVecLin W)) := by
    funext y; simp [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [heq]
  exact LinearMap.convexOn _ convex_univ

/-- If `g` is convex and monotone on all of `ℝ` and `f : (Fin d → ℝ) → ℝ` is convex on `univ`,
then `g ∘ f` is convex on `univ`. -/
theorem convexOn_comp_univ {d : ℕ} {g : ℝ → ℝ} {f : (Fin d → ℝ) → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hgm : Monotone g) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun y => g (f y)) := by
  have hcont : ContinuousOn f Set.univ := hf.continuousOn isOpen_univ
  have hrange : Convex ℝ (f '' Set.univ) :=
    ((convex_univ.isPreconnected).image f hcont).convex
  have hcomp := ConvexOn.comp (hg.subset (Set.subset_univ _) hrange) hf
    (hgm.monotoneOn (f '' Set.univ))
  exact hcomp

/-- A finite sum of convex functions on `univ` is convex. -/
theorem convexOn_univ_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin d → ℝ) → ℝ) (h : ∀ i ∈ s, ConvexOn ℝ Set.univ (F i)) :
    ConvexOn ℝ Set.univ (fun y => ∑ i ∈ s, F i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) convex_univ
  | insert a t ha ih =>
      have hsum : (fun y => ∑ i ∈ insert a t, F i y)
          = (fun y => F a y + ∑ i ∈ t, F i y) :=
        funext fun y => by rw [Finset.sum_insert ha]
      rw [hsum]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Convexity is preserved through the FICNN chain: if the initial hidden vector `zf` is convex
coordinatewise, so is every output coordinate of `N.eval`. -/
theorem ICNN.eval_convexOn {d : ℕ} : {a b : ℕ} → (N : ICNN d a b) → N.IsConvex →
    (zf : (Fin d → ℝ) → (Fin a → ℝ)) → (∀ i, ConvexOn ℝ Set.univ (fun y => zf y i)) →
    ∀ j, ConvexOn ℝ Set.univ (fun y => N.eval y (zf y) j)
  | _, _, .nil, _, _, hz, j => by simpa [ICNN.eval] using hz j
  | _, _, .cons L rest, h, zf, hz, j => by
      have hL : L.IsConvex := h.1
      have hlayer : ∀ k, ConvexOn ℝ Set.univ (fun y => L.toFun (zf y) y k) := by
        intro k
        have hWz : ConvexOn ℝ Set.univ (fun y => (L.Wz.mulVec (zf y)) k) := by
          have hsum : (fun y => (L.Wz.mulVec (zf y)) k)
              = fun y => ∑ m, L.Wz k m • zf y m := by
            funext y; simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
          rw [hsum]
          exact convexOn_univ_finset_sum Finset.univ _
            (fun m _ => (hz m).smul (hL.1 k m))
        have harg : ConvexOn ℝ Set.univ
            (fun y => (L.Wz.mulVec (zf y)) k + (L.Wy.mulVec y) k + L.bias k) :=
          (hWz.add (linear_coord_convexOn L.Wy k)).add (convexOn_const (L.bias k) convex_univ)
        have hcomp := convexOn_comp_univ hL.2.2 hL.2.1 harg
        simpa [ICNNLayer.toFun] using hcomp
      have hrec := rest.eval_convexOn h.2 (fun y => L.toFun (zf y) y) hlayer j
      simpa [ICNN.eval] using hrec

/-- **Soundness.** A fully input-convex network with nonnegative propagation weights and convex,
nondecreasing activations denotes a convex function. -/
theorem icnn_convex {d : ℕ} (N : ICNN d 0 1) (h : N.IsConvex) :
    ConvexOn ℝ Set.univ N.toFun := by
  have := N.eval_convexOn h (fun _ => (0 : Fin 0 → ℝ)) (fun i => i.elim0) 0
  exact this

end UniversalApproximation.Amos
