/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine

/-!
# Tangent-plane minorant for convex differentiable functions (Amos et al.)

A convex, differentiable `f : (Fin d → ℝ) → ℝ` lies above each of its tangent planes:
`f x + fderiv ℝ f x (y - x) ≤ f y`. Proved by restricting `f` to the line through `x` and `y` and
applying Mathlib's one-dimensional convex-derivative inequality (no supporting-hyperplane / Hahn–
Banach machinery). `gradVec` expresses the derivative functional as a dot product so the tangent
plane is an affine `dotAffine`, feeding `Approx/Density.lean`.
-/

namespace UniversalApproximation.Amos

open scoped Matrix

/-- The gradient vector of `f` at `x`: its `j`-th entry is the derivative functional applied to the
`j`-th standard basis vector. -/
noncomputable def gradVec {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => fderiv ℝ f x (Pi.single j 1)

/-- The derivative functional `fderiv ℝ f x` equals the dot product with `gradVec f x`. No
differentiability hypothesis: `fderiv` is `ℝ`-linear unconditionally. -/
theorem gradVec_dotProduct {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (v : Fin d → ℝ) : gradVec f x ⬝ᵥ v = fderiv ℝ f x v := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
    ext k; simp [Pi.single_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, gradVec, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- A convex differentiable `f` lies above its tangent plane at `x`. -/
theorem convex_diff_tangent_le {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : Fin d → ℝ) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  set g : ℝ →ᵃ[ℝ] (Fin d → ℝ) := AffineMap.lineMap x y with hg
  set φ : ℝ → ℝ := f ∘ g with hφ
  have hconv : ConvexOn ℝ Set.univ φ := by
    have := hf.comp_affineMap g
    simpa [hφ, Set.preimage_univ] using this
  have hderiv : HasDerivAt φ (fderiv ℝ f x (y - x)) 0 := by
    have hg0 : HasDerivAt g (y - x) 0 := AffineMap.hasDerivAt_lineMap
    have hfg : HasFDerivAt f (fderiv ℝ f x) (g 0) := by
      rw [hg, AffineMap.lineMap_apply_zero]
      exact (hd x).hasFDerivAt
    exact hfg.comp_hasDerivAt 0 hg0
  have hslope := hconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (by norm_num) hderiv
  rw [slope_def_field] at hslope
  have h0 : φ 0 = f x := by rw [hφ]; simp [hg, AffineMap.lineMap_apply_zero]
  have h1 : φ 1 = f y := by rw [hφ]; simp [hg, AffineMap.lineMap_apply_one]
  rw [h0, h1] at hslope
  simp only [sub_zero, div_one] at hslope
  linarith

/-- The tangent-plane minorant in `dotAffine` form. -/
theorem tangent_le {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : Fin d → ℝ) :
    dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x) y ≤ f y := by
  have h := convex_diff_tangent_le hf hd x y
  rw [← gradVec_dotProduct (y - x), dotProduct_sub] at h
  unfold dotAffine
  linarith

end UniversalApproximation.Amos
