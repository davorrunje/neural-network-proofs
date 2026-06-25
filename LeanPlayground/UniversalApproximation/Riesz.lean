import Mathlib
import LeanPlayground.UniversalApproximation.Activation

/-!
# Riesz representation for the Universal Approximation Theorem

This file isolates the analytic input from duality theory used by the
Universal Approximation Theorem (UAT) scaffold: every continuous linear
functional on `C(K, ℝ)` is represented by integration against a signed
(regular Borel) measure on `K`.

Mathlib provides the Riesz–Markov–Kakutani theorem for *positive* linear
functionals; the *signed* / dual-space form needed here is the substantive
gap, so `riesz_repr` is **admitted** (roadmap item 1).
-/

namespace UniversalApproximation

open MeasureTheory

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- ADMITTED (roadmap item 1). Riesz representation of (C(K,ℝ))* by signed
regular Borel measures. Mathlib has Riesz–Markov–Kakutani for *positive*
functionals; the signed/dual form is the substantive gap. Cybenko 1989. -/
theorem riesz_repr (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    ∃ μ : SignedMeasure ↥K,
      (∀ g : C(↥K, ℝ), L g = signedIntegral μ (⇑g)) ∧ (L = 0 ↔ μ = 0) := by
  sorry

end UniversalApproximation
