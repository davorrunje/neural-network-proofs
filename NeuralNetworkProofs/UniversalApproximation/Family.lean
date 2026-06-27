import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Activation
import NeuralNetworkProofs.UniversalApproximation.Network

/-!
# The single-hidden-layer function family

This file defines the family of functions realised by a single hidden layer with
activation `σ`, viewed as a subspace of the continuous functions on a set `K`.

* `continuous_preactivation` — the affine pre-activation `x ↦ ⟪w, x⟫ + b` is continuous.
* `generator σ hσc w b` — the continuous map `x ↦ σ (⟪w, x⟫ + b)` on the subtype `↥K`.
* `S σ hσc` — the linear span of all such generators inside `C(↥K, ℝ)`.
* `generator_mem_S` — every generator lies in `S`.

No compactness of `K` is needed to form these objects; compactness is supplied
later, at theorem time, when invoking density (Stone–Weierstrass) arguments.
-/

namespace UniversalApproximation

open scoped RealInnerProductSpace

variable {n : ℕ} (σ : ℝ → ℝ)

/-- The affine pre-activation `x ↦ ⟪w, x⟫ + b` is continuous. -/
theorem continuous_preactivation (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪w, x⟫ + b) :=
  (continuous_const.inner continuous_id).add continuous_const

/-- The continuous map `x ↦ σ (⟪w, x⟫ + b)` on the subtype `↥K`, i.e. a single
hidden unit with weight `w`, bias `b` and activation `σ`. -/
noncomputable def generator (hσc : Continuous σ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) : C(↥K, ℝ) where
  toFun := fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)
  continuous_toFun :=
    hσc.comp ((continuous_preactivation w b).comp continuous_subtype_val)

/-- The linear span of all single-hidden-unit generators, as a submodule of the
continuous functions `C(↥K, ℝ)`. This is the function family realised by a single
hidden layer with activation `σ`. -/
noncomputable def S (hσc : Continuous σ) {K : Set (EuclideanSpace ℝ (Fin n))} :
    Submodule ℝ C(↥K, ℝ) :=
  Submodule.span ℝ
    (Set.range fun wb : EuclideanSpace ℝ (Fin n) × ℝ => generator σ hσc wb.1 wb.2)

/-- Every generator belongs to the span `S`. -/
theorem generator_mem_S (hσc : Continuous σ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    generator σ hσc (K := K) w b ∈ S σ hσc (K := K) :=
  Submodule.subset_span ⟨(w, b), rfl⟩

end UniversalApproximation
