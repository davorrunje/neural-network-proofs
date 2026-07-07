/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Polynomial

/-! # The Leshno (1993) activation class `M` and polynomial predicates.

This is the first file of the top-down Leshno universal-approximation scaffold. It defines:

* `ClassM σ` — the activation class `M`: `σ` is locally bounded and the closure of its
  discontinuity set is Lebesgue-null;
* `IsAEPolynomial σ` — `σ` agrees Lebesgue-a.e. with a polynomial function (the M-boundary
  notion);
* `IsPolynomialFun σ` — `σ` equals a polynomial function everywhere (the smooth-layer notion);
* `ClassM.of_continuous` — every continuous `σ` is in `M`;
* `isPolynomialFun_of_continuous_of_aePolynomial` — a continuous a.e.-polynomial is an everywhere
  polynomial (bridges the two notions for the smooth engine).
-/

namespace UniversalApproximation.Leshno

open MeasureTheory

/-- The Leshno class `M`: locally bounded, and the closure of the discontinuity set is null. -/
structure ClassM (σ : ℝ → ℝ) : Prop where
  locBdd : ∀ R : ℝ, ∃ C, ∀ t, |t| ≤ R → |σ t| ≤ C
  discNull : volume (closure {t : ℝ | ¬ ContinuousAt σ t}) = 0

/-- `σ` agrees Lebesgue-a.e. with a polynomial function. -/
def IsAEPolynomial (σ : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, σ =ᵐ[volume] fun t => p.eval t

/-- `σ` equals a polynomial function everywhere. -/
def IsPolynomialFun (σ : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, σ = fun t => p.eval t

/-- A continuous function is in class `M` (discontinuity set is empty). -/
theorem ClassM.of_continuous {σ : ℝ → ℝ} (hσ : Continuous σ) : ClassM σ where
  locBdd R := by
    -- On the compact interval `[-R, R]`, continuity gives a bound `C`.
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
      (f := σ) hσ.continuousOn
    refine ⟨C, fun t ht => ?_⟩
    have hmem : t ∈ Set.Icc (-R) R := abs_le.mp ht
    have := hC t hmem
    rwa [Real.norm_eq_abs] at this
  discNull := by
    -- A continuous function has no points of discontinuity, so the set is empty.
    have hempty : {t : ℝ | ¬ ContinuousAt σ t} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hσ.continuousAt
    rw [hempty, closure_empty, measure_empty]

/-- A continuous a.e.-polynomial is an everywhere polynomial. (Bridges the two notions for the
smooth engine.) -/
theorem isPolynomialFun_of_continuous_of_aePolynomial {σ : ℝ → ℝ}
    (hσ : Continuous σ) (h : IsAEPolynomial σ) : IsPolynomialFun σ := by
  obtain ⟨p, hp⟩ := h
  -- Two continuous functions equal `volume`-a.e. on `ℝ` (a measure of full support) are equal
  -- everywhere.
  exact ⟨p, (hσ.ae_eq_iff_eq volume (Polynomial.continuous p)).mp hp⟩

end UniversalApproximation.Leshno
