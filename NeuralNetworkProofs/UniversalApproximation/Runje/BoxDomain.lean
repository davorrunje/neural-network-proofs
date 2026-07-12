/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs

/-!
# Affine box↔cube rescaling and the closure lemmas for the general-box partial-monotone UAP

`cubeOfBox a b` sends the box `Set.Icc a b` (non-degenerate: `a j < b j`) coordinatewise-affinely
onto the unit cube `Set.Icc 0 1`; `boxOfCube a b` is its inverse. Both are increasing and
continuous. This file also proves the two structural closure lemmas used by `PartMonoBox.lean`:
`genSpanPi` is closed under affine input precomposition, and a `MonoNet` gains a coordinatewise
suffix rescaling by prepending an identity-activation positive-diagonal layer.
-/

namespace UniversalApproximation.Runje

open scoped Matrix

/-- Affine map sending the box `Set.Icc a b` onto the unit cube, coordinatewise. -/
noncomputable def cubeOfBox {d : ℕ} (a b x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (x j - a j) / (b j - a j)

/-- Inverse affine map sending the unit cube onto the box `Set.Icc a b`, coordinatewise. -/
def boxOfCube {d : ℕ} (a b x : Fin d → ℝ) : Fin d → ℝ := fun j => a j + (b j - a j) * x j

theorem boxOfCube_cubeOfBox {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) (x) :
    boxOfCube a b (cubeOfBox a b x) = x := by
  funext j; simp only [boxOfCube, cubeOfBox]
  have : b j - a j ≠ 0 := ne_of_gt (sub_pos.mpr (hab j))
  field_simp
  ring

theorem cubeOfBox_boxOfCube {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) (x) :
    cubeOfBox a b (boxOfCube a b x) = x := by
  funext j; simp only [boxOfCube, cubeOfBox]
  have : b j - a j ≠ 0 := ne_of_gt (sub_pos.mpr (hab j))
  field_simp
  ring

theorem cubeOfBox_mem {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) {x}
    (hx : x ∈ Set.Icc a b) : cubeOfBox a b x ∈ Set.Icc (0 : Fin d → ℝ) 1 := by
  rw [Set.mem_Icc, Pi.le_def, Pi.le_def] at hx ⊢
  refine ⟨fun j => ?_, fun j => ?_⟩
  · exact div_nonneg (sub_nonneg.mpr (hx.1 j)) (sub_pos.mpr (hab j)).le
  · exact div_le_one (sub_pos.mpr (hab j)) |>.mpr (sub_le_sub_right (hx.2 j) (a j))

theorem boxOfCube_mem {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) {x}
    (hx : x ∈ Set.Icc (0 : Fin d → ℝ) 1) : boxOfCube a b x ∈ Set.Icc a b := by
  rw [Set.mem_Icc, Pi.le_def, Pi.le_def] at hx ⊢
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp only [boxOfCube]
    have h0 : (0 : ℝ) ≤ (b j - a j) * x j := mul_nonneg (sub_pos.mpr (hab j)).le (hx.1 j)
    linarith
  · simp only [boxOfCube]
    have h1 : (b j - a j) * x j ≤ (b j - a j) * 1 :=
      mul_le_mul_of_nonneg_left (hx.2 j) (sub_pos.mpr (hab j)).le
    linarith

theorem continuous_boxOfCube {d} (a b : Fin d → ℝ) : Continuous (boxOfCube a b) := by
  unfold boxOfCube
  fun_prop

theorem monotone_boxOfCube {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) :
    Monotone (boxOfCube a b) := by
  intro x y hxy
  rw [Pi.le_def] at hxy ⊢
  intro j
  simp only [boxOfCube]
  have := mul_le_mul_of_nonneg_left (hxy j) (sub_pos.mpr (hab j)).le
  linarith

end UniversalApproximation.Runje
