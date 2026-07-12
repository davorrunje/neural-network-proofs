/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import NeuralNetworkProofs.NeuralNetwork.Network
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding

/-!
# Affine box↔cube rescaling for the general-box partial-monotone UAP

`cubeOfBox a b` sends the box `Set.Icc a b` (non-degenerate: `a j < b j`) coordinatewise-affinely
onto the unit cube `Set.Icc 0 1`; `boxOfCube a b` is its inverse. Both are increasing and
continuous. The structural closure lemmas used by `PartMonoBox.lean` (`genSpanPi` closed under
affine input precomposition, and a `MonoNet` coordinatewise suffix rescaling) are added in later
files/tasks.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone
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

/-- A single Pi-side ridge unit precomposed with the affine `cubeOfBox` map is again a ridge
unit, with rescaled weights `w c / (bF c - aF c)` and shifted bias. Pure functional identity — no
non-degeneracy hypothesis on `bF - aF` is needed. -/
theorem genFunPi_comp_cubeOfBox {σ : ℝ → ℝ} {df} {aF bF : Fin df → ℝ}
    (w : Fin df → ℝ) (b : ℝ) :
    (fun u => genFunPi σ w b (cubeOfBox aF bF u))
      = genFunPi σ (fun c => w c / (bF c - aF c))
          (b - ∑ c, w c * aF c / (bF c - aF c)) := by
  funext u
  simp only [genFunPi, cubeOfBox]
  congr 1
  rw [show (∑ c, w c * ((u c - aF c) / (bF c - aF c)))
        = ∑ c, (w c / (bF c - aF c) * u c - w c * aF c / (bF c - aF c))
      from Finset.sum_congr rfl fun c _ => by ring,
    Finset.sum_sub_distrib]
  ring

/-- **Feature-block closure.** The Leshno single-hidden-layer span `genSpanPi σ df` is closed under
precomposition with the affine box→cube map `cubeOfBox aF bF`. -/
theorem genSpanPi_comp_cubeOfBox {σ : ℝ → ℝ} {df} {aF bF : Fin df → ℝ}
    (_hab : ∀ j, aF j < bF j) {g : (Fin df → ℝ) → ℝ} (hg : g ∈ genSpanPi σ df) :
    (fun u => g (cubeOfBox aF bF u)) ∈ genSpanPi σ df := by
  have hmap : Submodule.map (LinearMap.funLeft ℝ ℝ (cubeOfBox aF bF)) (genSpanPi σ df)
      ≤ genSpanPi σ df := by
    rw [genSpanPi, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨wb, rfl⟩, rfl⟩
    rw [show (LinearMap.funLeft ℝ ℝ (cubeOfBox aF bF)) (genFunPi σ wb.1 wb.2)
          = (fun u => genFunPi σ wb.1 wb.2 (cubeOfBox aF bF u)) from rfl,
      genFunPi_comp_cubeOfBox wb.1 wb.2]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  exact hmap ⟨g, hg, rfl⟩

/-- The layer `(z, x) ↦ (z, s ⊙ x + t)`: identity on the `p` prefix, affine on the `q` suffix. -/
def rescaleSuffixLayer {p q : ℕ} (s t : Fin q → ℝ) : NeuralNetwork.Layer (p + q) (p + q) where
  W := Matrix.diagonal (Fin.addCases (fun _ : Fin p => (1 : ℝ)) s)
  c := Fin.addCases (fun _ : Fin p => (0 : ℝ)) t

/-- Evaluating the rescaling layer under the identity activation: the `p` prefix is unchanged and
the `q` suffix is sent coordinatewise to `s ⊙ x + t`. -/
theorem rescaleSuffixLayer_toFun {p q} (s t : Fin q → ℝ) (z : Fin p → ℝ) (x : Fin q → ℝ) :
    (rescaleSuffixLayer s t).toFun id (Fin.append z x)
      = Fin.append z (fun j => s j * x j + t j) := by
  funext k
  simp only [NeuralNetwork.Layer.toFun, rescaleSuffixLayer, id_eq, Matrix.mulVec_diagonal]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [Fin.addCases_left, Fin.append_left]
  · simp [Fin.addCases_right, Fin.append_right]

end UniversalApproximation.Runje

namespace UniversalApproximation.Monotone

open UniversalApproximation.Runje

/-- Rescale a monotone network's last `q` (monotone-block) inputs by the coordinatewise increasing
affine map `x ↦ s ⊙ x + t`, by prepending an identity-activation positive-diagonal layer. -/
def MonoNet.rescaleSuffix {p q : ℕ} (N : MonoNet (p + q)) (s t : Fin q → ℝ) : MonoNet (p + q) where
  width := N.width
  stack := .cons (rescaleSuffixLayer s t) id N.stack
  readW := N.readW
  readBias := N.readBias

/-- The rescaled network evaluated at `(z, x)` equals the original network evaluated at the
suffix-rescaled input `(z, s ⊙ x + t)`. -/
theorem MonoNet.rescaleSuffix_toFun {p q} (N : MonoNet (p + q)) (s t : Fin q → ℝ)
    (z : Fin p → ℝ) (x : Fin q → ℝ) :
    (N.rescaleSuffix s t).toFun (Fin.append z x)
      = N.toFun (Fin.append z (fun j => s j * x j + t j)) := by
  simp only [MonoNet.toFun, MonoNet.rescaleSuffix, ActStack.toFun, rescaleSuffixLayer_toFun]
  rfl

/-- The suffix-rescaling combinator preserves monotonicity when the scale factors are
non-negative: the prepended diagonal layer has an identity (hence monotone) activation and
non-negative weights, and the read-out is untouched. -/
theorem MonoNet.rescaleSuffix_isMonotone {p q} {N : MonoNet (p + q)} {s t : Fin q → ℝ}
    (hN : N.IsMonotone) (hs : ∀ j, 0 ≤ s j) : (N.rescaleSuffix s t).IsMonotone := by
  refine ⟨⟨⟨monotone_id, ?_⟩, hN.1⟩, hN.2⟩
  intro i j
  simp only [rescaleSuffixLayer, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp [hs]
  · exact le_refl 0

end UniversalApproximation.Monotone
