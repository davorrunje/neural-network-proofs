/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM
import NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import NeuralNetworkProofs.UniversalApproximation.Leshno.SmoothEngine
import NeuralNetworkProofs.UniversalApproximation.Leshno.Mollify
import NeuralNetworkProofs.UniversalApproximation.Leshno.Ridge
import NeuralNetworkProofs.UniversalApproximation.Leshno.Converse

/-! # The headline Leshno (1993) universal approximation theorem.

This file assembles the top-down scaffold into the headline equivalence:

* `univariate_density` — for an `M`-class non-a.e.-polynomial `σ`, every continuous function on a
  compact `I ⊆ ℝ` is approximable (`T σ I = ⊤`). Proof: mollify `σ` to a smooth non-polynomial
  `g₀` (`exists_nonpoly_mollify`, `contDiff_mollify`), run the smooth derivative engine
  (`smooth_engine`) to fill out the closure of `Sg g₀`, and observe each generator of `Sg g₀` is a
  mollified ridge in `T σ I` (`mollify_ridge_mem_T`), so `T σ I` (being closed, `T_isClosed`)
  contains the whole closure `= ⊤`.
* `leshno_dense` — for an `M`-class non-a.e.-polynomial `σ`, `σ` densely approximates
  (`univariate_density` + `ridge_density` + the reduction `denselyApproximates_of_forall_T_eq_top`).
* `leshno_dense_iff` — the headline equivalence: an `M`-class `σ` densely approximates iff it is
  **not** a.e. a polynomial (`leshno_dense` for `mpr`, the converse `aePolynomial_not_dense` for
  `mp`).
-/

namespace UniversalApproximation.Leshno

open Topology
open scoped RealInnerProductSpace ContDiff

/-- Every generator of the smooth engine's span `Sg (mollify σ φ) I` lies in the continuous core
`T σ I`. A generator `t ↦ mollify σ φ (lb.1 * t + lb.2)` is exactly the dilated/translated ridge of
the mollification with weight `w = 1`, bias `b = 0`, dilation `lb.1`, shift `lb.2`, so
`mollify_ridge_mem_T` (the hard `M`-class core) places it in `T σ I`. -/
private lemma smoothMollify_span_le_T {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {I : Set ℝ} (hI : IsCompact I)
    (hcont : Continuous (mollify σ φ)) :
    Sg (mollify σ φ) I hcont ≤ T σ I := by
  rw [Sg, Submodule.span_le]
  rintro _ ⟨lb, rfl⟩
  -- The generator `t ↦ mollify σ φ (lb.1 * t + lb.2)` is the mollified ridge with `w = 1, b = 0`.
  have hridge : Continuous fun t : ↥I =>
      mollify σ φ (lb.1 * (⟪(1 : ℝ), (t : ℝ)⟫ + 0) + lb.2) := by
    have haff : Continuous fun t : ↥I => lb.1 * (⟪(1 : ℝ), (t : ℝ)⟫ + 0) + lb.2 := by
      simp only [RCLike.inner_apply, conj_trivial]; fun_prop
    exact hcont.comp haff
  have hmem := mollify_ridge_mem_T hσ hφ hφc I hI (1 : ℝ) 0 lb.1 lb.2 hridge
  -- The generator equals this mollified ridge (using `⟪(1:ℝ), t⟫ = t`).
  change (⟨fun t : ↥I => mollify σ φ (lb.1 * (t : ℝ) + lb.2), hcont.comp (by fun_prop)⟩
      : C(↥I, ℝ)) ∈ T σ I
  have heq : (⟨fun t : ↥I => mollify σ φ (lb.1 * (t : ℝ) + lb.2), hcont.comp (by fun_prop)⟩
      : C(↥I, ℝ))
      = (⟨fun t : ↥I => mollify σ φ (lb.1 * (⟪(1 : ℝ), (t : ℝ)⟫ + 0) + lb.2), hridge⟩
          : C(↥I, ℝ)) := by
    ext t
    simp
  rw [heq]
  exact hmem

/-- For an `M`-class non-a.e.-polynomial `σ`, every continuous function on a compact `I ⊆ ℝ` is
approximable by `genSpan σ I`, i.e. `T σ I = ⊤`. -/
theorem univariate_density {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    UnivariateDense σ := by
  intro I hI
  -- Mollify `σ` to a smooth non-polynomial `g₀`.
  obtain ⟨φ, hφ, hφc, hnp₀⟩ := exists_nonpoly_mollify hσ hnp
  set g₀ : ℝ → ℝ := mollify σ φ with hg₀def
  have hg₀ : ContDiff ℝ ∞ g₀ := contDiff_mollify hσ hφ hφc
  -- The smooth engine fills out the closure of `Sg g₀`.
  have heng : (Sg g₀ I hg₀.continuous).topologicalClosure = ⊤ := smooth_engine hg₀ hnp₀ I hI
  -- Each generator of `Sg g₀` is a mollified ridge living in `T σ I`.
  have hgen_le : Sg g₀ I hg₀.continuous ≤ T σ I :=
    smoothMollify_span_le_T hσ hφ hφc hI hg₀.continuous
  -- `T σ I` is closed and contains `Sg g₀`, so it contains the closure `= ⊤`.
  have hclosed : IsClosed (T σ I : Set C(↥I, ℝ)) := T_isClosed σ hI
  have hle : (Sg g₀ I hg₀.continuous).topologicalClosure ≤ T σ I :=
    Submodule.topologicalClosure_minimal _ hgen_le hclosed
  rw [heng] at hle
  exact top_le_iff.mp hle

/-- For an `M`-class non-a.e.-polynomial `σ`, `σ` densely approximates. -/
theorem leshno_dense {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    DenselyApproximates σ :=
  denselyApproximates_of_forall_T_eq_top
    (fun K hK => ridge_density (univariate_density hσ hnp) K hK)

/-- **The headline Leshno (1993) universal approximation theorem.** An `M`-class `σ` densely
approximates iff it is not (Lebesgue-a.e.) a polynomial. -/
theorem leshno_dense_iff {σ : ℝ → ℝ} (hσ : ClassM σ) :
    DenselyApproximates σ ↔ ¬ IsAEPolynomial σ := by
  refine ⟨fun hd hpoly => aePolynomial_not_dense hpoly hd, fun hnp => leshno_dense hσ hnp⟩

end UniversalApproximation.Leshno
