import Mathlib
import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.Contrib.RieszKantorovich

/-!
# Riesz representation for the Universal Approximation Theorem

This file isolates the analytic input from duality theory used by the
Universal Approximation Theorem (UAT) scaffold: every continuous linear
functional on `C(K, ℝ)` is represented by integration against a signed
(regular Borel) measure on `K`.

Mathlib provides the Riesz–Markov–Kakutani theorem for *positive* linear
functionals only. The *signed* / dual-space form `riesz_repr` is **proved**
here by combining the Riesz–Kantorovich decomposition
(`Contrib.RieszKantorovich.exists_positive_decomposition`, which splits a
continuous functional into two cone-positive functionals) with the positive
Riesz–Markov–Kakutani theorem applied to each part.
-/

namespace UniversalApproximation

open MeasureTheory

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- Every continuous linear functional on `C(↥K, ℝ)` (with `↥K` compact) is order bounded:
on each order interval `[0, f]` its values are bounded above by `‖L‖ * ‖f‖`. This is the
bridge feeding `C(↥K, ℝ)` into the abstract Riesz–Kantorovich decomposition. -/
theorem continuous_isOrderBounded [CompactSpace ↥K] (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    RieszKantorovich.IsOrderBounded L.toLinearMap := by
  intro f hf
  refine ⟨‖L‖ * ‖f‖, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  have hng : ‖g‖ ≤ ‖f‖ := by
    rw [ContinuousMap.norm_le _ (norm_nonneg f)]
    intro x
    have hgx0 : 0 ≤ g x := hg0 x
    have hgfx : g x ≤ f x := hgf x
    have habs : |g x| ≤ |f x| := by
      rw [abs_of_nonneg hgx0, abs_of_nonneg (le_trans hgx0 hgfx)]
      exact hgfx
    exact le_trans habs (ContinuousMap.norm_coe_le_norm f x)
  calc L.toLinearMap g = L g := rfl
    _ ≤ |L g| := le_abs_self _
    _ ≤ ‖L g‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖g‖ := L.le_opNorm g
    _ ≤ ‖L‖ * ‖f‖ := mul_le_mul_of_nonneg_left hng (norm_nonneg L)

/-- Build a positive linear functional on `C_c(↥K, ℝ)` from a positive linear
functional on `C(↥K, ℝ)` (the two coincide when `↥K` is compact). -/
private noncomputable def cscFunctional [CompactSpace ↥K] (Lp : C(↥K, ℝ) →ₗ[ℝ] ℝ)
    (hLp : ∀ f, 0 ≤ f → 0 ≤ Lp f) :
    CompactlySupportedContinuousMap ↥K ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Lp f.toContinuousMap
      map_add' := fun f g => by
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl,
          map_add]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl, map_smul] }
    (fun f hf => hLp _ (by
      rw [ContinuousMap.le_def]; intro x
      have := (CompactlySupportedContinuousMap.le_def.mp hf) x
      simpa using this))

/-- Riesz representation of `(C(K,ℝ))*` by signed regular Borel measures, assembled
from the Riesz–Kantorovich decomposition (`exists_positive_decomposition`) and the
positive Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`). -/
theorem riesz_repr [CompactSpace ↥K] (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    ∃ μ : SignedMeasure ↥K,
      (∀ g : C(↥K, ℝ), L g = signedIntegral μ (⇑g)) ∧ (L = 0 ↔ μ = 0) := by
  -- Riesz–Kantorovich: split `L` into a difference of positive functionals.
  obtain ⟨Lp, Lm, hLp, hLm, hL⟩ :=
    RieszKantorovich.exists_positive_decomposition L.toLinearMap (continuous_isOrderBounded L)
  -- Each positive functional becomes a positive functional on `C_c(↥K, ℝ)`.
  set Λp := cscFunctional Lp hLp with hΛp
  set Λn := cscFunctional Lm hLm with hΛn
  -- Riesz–Markov–Kakutani: represent each by a regular finite measure.
  set μp := RealRMK.rieszMeasure Λp with hμp_def
  set μn := RealRMK.rieszMeasure Λn with hμn_def
  haveI : IsFiniteMeasure μp := RealRMK.instIsFiniteMeasureRieszMeasure Λp
  haveI : IsFiniteMeasure μn := RealRMK.instIsFiniteMeasureRieszMeasure Λn
  haveI : μp.Regular := RealRMK.regular_rieszMeasure Λp
  haveI : μn.Regular := RealRMK.regular_rieszMeasure Λn
  -- The representing signed measure.
  set μ := μp.toSignedMeasure - μn.toSignedMeasure with hμ_def
  -- For every `g`, `∫ g ∂μp = Lp g` and `∫ g ∂μn = Lm g`, so `L g = signedIntegral μ g`.
  have hrepr : ∀ g : C(↥K, ℝ), L g = signedIntegral μ (⇑g) := by
    intro g
    have hgcsc : Λp (CompactlySupportedContinuousMap.continuousMapEquiv g) = Lp g := rfl
    have hgcscn : Λn (CompactlySupportedContinuousMap.continuousMapEquiv g) = Lm g := rfl
    have hip : ∫ x, g x ∂μp = Lp g := by
      rw [hμp_def]
      exact (RealRMK.integral_rieszMeasure Λp
        (CompactlySupportedContinuousMap.continuousMapEquiv g)).trans hgcsc
    have hin : ∫ x, g x ∂μn = Lm g := by
      rw [hμn_def]
      exact (RealRMK.integral_rieszMeasure Λn
        (CompactlySupportedContinuousMap.continuousMapEquiv g)).trans hgcscn
    -- `g` is integrable against every finite measure on the compact space `↥K`.
    have hgint : ∀ ρ : Measure ↥K, IsFiniteMeasure ρ → Integrable (⇑g) ρ := by
      intro ρ _
      have := BoundedContinuousFunction.integrable ρ (BoundedContinuousFunction.mkOfCompact g)
      refine this.congr ?_
      filter_upwards with x using (BoundedContinuousFunction.mkOfCompact_apply g x)
    -- Jordan parts of the difference are `μp - μn` and `μn - μp`.
    have hsi : signedIntegral μ (⇑g) = ∫ x, g x ∂μp - ∫ x, g x ∂μn := by
      rw [hμ_def]
      unfold signedIntegral
      rw [Measure.toJordanDecomposition_toSignedMeasure_sub,
        Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
        Measure.jordanDecompositionOfToSignedMeasureSub_negPart]
      haveI : IsFiniteMeasure (μp - μn) := Measure.isFiniteMeasure_sub
      haveI : IsFiniteMeasure (μn - μp) := Measure.isFiniteMeasure_sub
      -- `(μp - μn) + μn = (μn - μp) + μp` (both equal `μp ⊔ μn`).
      obtain ⟨s, hs⟩ := exists_isHahnDecomposition μp μn
      have hms := hs.measurableSet
      have hmeq : (μp - μn) + μn = (μn - μp) + μp := by
        have rs : ((μp - μn) + μn).restrict s = ((μn - μp) + μp).restrict s := by
          rw [Measure.restrict_add, Measure.restrict_add,
            Measure.restrict_sub_eq_restrict_sub_restrict hms,
            Measure.restrict_sub_eq_restrict_sub_restrict hms,
            Measure.sub_eq_zero_of_le hs.le_on, zero_add, Measure.sub_add_cancel_of_le hs.le_on]
        have rsc : ((μp - μn) + μn).restrict sᶜ = ((μn - μp) + μp).restrict sᶜ := by
          rw [Measure.restrict_add, Measure.restrict_add,
            Measure.restrict_sub_eq_restrict_sub_restrict hms.compl,
            Measure.restrict_sub_eq_restrict_sub_restrict hms.compl,
            Measure.sub_eq_zero_of_le hs.compl.le_on, zero_add,
            Measure.sub_add_cancel_of_le hs.compl.le_on]
        rw [← Measure.restrict_add_restrict_compl (μ := (μp - μn) + μn) hms,
          ← Measure.restrict_add_restrict_compl (μ := (μn - μp) + μp) hms, rs, rsc]
      -- integrate the measure identity
      have hkey : ∫ x, g x ∂((μp - μn) + μn) = ∫ x, g x ∂((μn - μp) + μp) := by
        rw [hmeq]
      rw [integral_add_measure (hgint _ inferInstance) (hgint _ inferInstance),
        integral_add_measure (hgint _ inferInstance) (hgint _ inferInstance)] at hkey
      linarith
    rw [hsi, hip, hin]
    change L g = Lp g - Lm g
    have := hL g
    simpa using this
  refine ⟨μ, hrepr, ?_, ?_⟩
  · -- `L = 0 → μ = 0`: integrals against `μp` and `μn` agree, so `μp = μn`.
    intro hL0
    have hint_eq : ∀ g : C(↥K, ℝ), ∫ x, g x ∂μp = ∫ x, g x ∂μn := by
      intro g
      have hip : ∫ x, g x ∂μp = Lp g :=
        (RealRMK.integral_rieszMeasure Λp
          (CompactlySupportedContinuousMap.continuousMapEquiv g))
      have hin : ∫ x, g x ∂μn = Lm g :=
        (RealRMK.integral_rieszMeasure Λn
          (CompactlySupportedContinuousMap.continuousMapEquiv g))
      have hLg : Lp g - Lm g = 0 := by
        have : (L : C(↥K, ℝ) → ℝ) g = Lp g - Lm g := hL g
        rw [hL0] at this; simpa using this.symm
      rw [hip, hin]; linarith
    -- `integralPositiveLinearMap μp = integralPositiveLinearMap μn` ⇒ `μp = μn`.
    have heqΛ : CompactlySupportedContinuousMap.integralPositiveLinearMap μp =
        CompactlySupportedContinuousMap.integralPositiveLinearMap μn := by
      apply PositiveLinearMap.ext
      intro f
      change ∫ x, f x ∂μp = ∫ x, f x ∂μn
      exact hint_eq f.toContinuousMap
    have hμpn : μp = μn := RealRMK.integralPositiveLinearMap_inj.mp heqΛ
    rw [hμ_def]
    simp only [hμpn, sub_self]
  · -- `μ = 0 → L = 0`.
    intro hμ0
    ext g
    rw [hrepr g, hμ0]
    show signedIntegral (0 : SignedMeasure ↥K) (⇑g) = (0 : C(↥K, ℝ) →L[ℝ] ℝ) g
    simp only [zero_apply]
    unfold signedIntegral
    rw [SignedMeasure.toJordanDecomposition_zero]
    simp

end UniversalApproximation
