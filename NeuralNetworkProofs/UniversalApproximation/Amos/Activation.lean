/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Convex, nondecreasing activations for FICNNs (Amos et al.)

Concrete activations usable in a convex ICNN layer (`ConvexOn ℝ univ` + `Monotone`): `relu`,
`softplus`, and the identity (for a linear final layer). `softplus` is defined independently here
(the `Runje` development has its own copy; not shared, to keep developments self-contained).
-/

namespace UniversalApproximation.Amos

/-- Rectified linear unit. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- Softplus. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- `relu = max 0 ·` is convex: a pointwise supremum of the constant `0` and the identity. -/
theorem relu_convexOn : ConvexOn ℝ Set.univ relu :=
  (convexOn_const 0 convex_univ).sup (convexOn_id convex_univ)

/-- `relu` is monotone. -/
theorem relu_monotone : Monotone relu := fun _ _ h => max_le_max le_rfl h

/-- Softplus is monotone: `log` is monotone on `(0, ∞)` and `1 + exp x > 0` increases with `x`. -/
theorem softplus_monotone : Monotone softplus := by
  intro x y hxy
  simp only [softplus]
  have hpos : (0 : ℝ) < 1 + Real.exp x := by positivity
  exact Real.log_le_log hpos (by linarith [Real.exp_le_exp.mpr hxy])

/-- Softplus is convex: its second derivative `exp x / (1 + exp x) ^ 2` is nonnegative. -/
theorem softplus_convexOn : ConvexOn ℝ Set.univ softplus := by
  have hpos : ∀ x : ℝ, (0 : ℝ) < 1 + Real.exp x := fun x => by positivity
  -- first derivative of softplus
  have hd1 : ∀ x : ℝ, HasDerivAt softplus (Real.exp x / (1 + Real.exp x)) x := by
    intro x
    exact ((Real.hasDerivAt_exp x).const_add 1).log (hpos x).ne'
  have hderiv1 : deriv softplus = fun x => Real.exp x / (1 + Real.exp x) :=
    funext fun x => (hd1 x).deriv
  -- second derivative of softplus (derivative of the first derivative)
  have hd2 : ∀ x : ℝ,
      HasDerivAt (fun x => Real.exp x / (1 + Real.exp x))
        ((Real.exp x * (1 + Real.exp x) - Real.exp x * Real.exp x) / (1 + Real.exp x) ^ 2) x :=
    fun x => (Real.hasDerivAt_exp x).div ((Real.hasDerivAt_exp x).const_add 1) (hpos x).ne'
  refine convexOn_univ_of_deriv2_nonneg (fun x => (hd1 x).differentiableAt) ?_ ?_
  · rw [hderiv1]; exact fun x => (hd2 x).differentiableAt
  · intro x
    have hval : deriv^[2] softplus x = Real.exp x / (1 + Real.exp x) ^ 2 := by
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hderiv1, (hd2 x).deriv]
      ring
    rw [hval]
    positivity

/-- The identity is convex on `univ`. -/
theorem id_convexOn : ConvexOn ℝ Set.univ (id : ℝ → ℝ) := convexOn_id convex_univ

/-- The identity is monotone. -/
theorem id_monotone : Monotone (id : ℝ → ℝ) := monotone_id

end UniversalApproximation.Amos
