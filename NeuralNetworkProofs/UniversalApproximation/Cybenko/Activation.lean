/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Topology.Filter

/-!
# Activation functions for the Universal Approximation Theorem

This file collects the activation-function-side definitions used by the
Universal Approximation Theorem (UAT) scaffold:

* `Sigmoidal`     — the analytic shape of a classical sigmoidal activation;
* `signedIntegral` — integration of a real-valued function against a signed
  measure, defined via the Jordan decomposition (positive part minus negative
  part);
* `Discriminatory` — the key property of an activation that drives the UAT
  contradiction: no nonzero signed measure can annihilate all the affine
  pre-compositions `x ↦ σ (⟪w, x⟫ + b)`.

The theorem `sigmoidal_discriminatory` (continuous sigmoidal ⇒ discriminatory)
is proved in `NeuralNetworkProofs.UniversalApproximation.Cybenko.Discriminatory`.
-/

namespace UniversalApproximation.Cybenko

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A `Sigmoidal` activation `σ : ℝ → ℝ` is continuous and tends to `0` at `-∞`
and to `1` at `+∞`. This is the classical (Cybenko) notion of a sigmoidal
function, made into a `Prop`-valued structure. -/
structure Sigmoidal (σ : ℝ → ℝ) : Prop where
  /-- `σ` is continuous. -/
  continuous : Continuous σ
  /-- `σ → 0` as its argument tends to `-∞`. -/
  atBot : Tendsto σ atBot (𝓝 0)
  /-- `σ → 1` as its argument tends to `+∞`. -/
  atTop : Tendsto σ atTop (𝓝 1)

/-- The integral of `g : ↥K → ℝ` against a signed measure `μ`, defined through
the Jordan decomposition of `μ` as the (Bochner) integral against the positive
part minus the integral against the negative part. -/
noncomputable def signedIntegral {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (μ : MeasureTheory.SignedMeasure ↥K) (g : ↥K → ℝ) : ℝ :=
  (∫ x, g x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, g x ∂μ.toJordanDecomposition.negPart)

/-- An activation `σ` is `Discriminatory` on `K` if the only signed measure on
`↥K` that annihilates every affine pre-composition `x ↦ σ (⟪w, x⟫ + b)` is the
zero measure. This is precisely the property used to derive density of the
single-hidden-layer network family. -/
def Discriminatory (K : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ → ℝ) : Prop :=
  ∀ μ : SignedMeasure ↥K,
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
      signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0) →
        μ = 0

end UniversalApproximation.Cybenko
