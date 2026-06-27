import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.MollifyDef
import LeanPlayground.Contrib.ConvolutionPolynomial
import LeanPlayground.Contrib.IteratedDerivPolynomial

/-! # Uniform degree bound for polynomial mollifications (convolution degree-invariance).
Intended Mathlib home: research leaf — no general Mathlib home yet. The argument is elementary and
Baire-free: convolving against a fixed normalized bump `ψ₀` (with `∫ ψ₀ = 1`) preserves polynomial
degree, and associativity of convolution relates `mollify σ φ` to `mollify σ ψ₀`; see the
per-declaration note. -/

namespace TestFunctionDegreeBound

open MeasureTheory
open UniversalApproximation.Leshno

open scoped ContDiff

/-- An `M`-class `σ` is a.e.-strongly-measurable (local copy; the import graph forbids depending on
`UniversalApproximation.Leshno.Mollify`, which imports this file). -/
private theorem classM_aestronglyMeasurable {σ : ℝ → ℝ} (hσ : ClassM σ) :
    AEStronglyMeasurable σ volume := by
  set G : Set ℝ := (closure {t | ¬ ContinuousAt σ t})ᶜ with hG
  have hGopen : IsOpen G := isClosed_closure.isOpen_compl
  have hcont : ContinuousOn σ G := by
    intro x hx
    have hx' : ContinuousAt σ x := by
      by_contra h
      exact hx (subset_closure h)
    exact hx'.continuousWithinAt
  have hmeas : AEStronglyMeasurable σ (volume.restrict G) :=
    hcont.aestronglyMeasurable hGopen.measurableSet
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ G := by
    rw [ae_iff]
    simpa [hG, compl_compl] using hσ.discNull
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hmeas

/-- An `M`-class `σ` is locally integrable (local copy; see `classM_aestronglyMeasurable`). -/
private theorem classM_locallyIntegrable {σ : ℝ → ℝ} (hσ : ClassM σ) :
    LocallyIntegrable σ volume := by
  intro x
  obtain ⟨C, hC⟩ := hσ.locBdd (|x| + 1)
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  apply Measure.integrableOn_of_bounded (M := C)
  · exact (measure_Icc_lt_top).ne
  · exact classM_aestronglyMeasurable hσ
  · refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro t ht
    have htR : |t| ≤ |x| + 1 := by
      rw [abs_le]
      constructor <;> [(have := ht.1); (have := ht.2)] <;>
        [(have hx := neg_abs_le x); (have hx := le_abs_self x)] <;> linarith
    simpa [Real.norm_eq_abs] using hC t htR

/-- Associativity bridge in the `mollify` orientation:
`(σ⋆φ) ⋆ ψ = σ ⋆ (φ⋆ψ)`, i.e. mollifying `σ` by `φ` then by `ψ` equals mollifying by `φ⋆ψ`. -/
theorem mollify_conv_assoc {σ φ ψ : ℝ → ℝ} (hσ : ClassM σ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    convolution (mollify σ φ) ψ (ContinuousLinearMap.mul ℝ ℝ) volume
      = mollify σ (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) := by
  rw [mollify_eq_convolution, mollify_eq_convolution]
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  -- measurability of the three factors
  have hσint : LocallyIntegrable σ volume := classM_locallyIntegrable hσ
  have hσm : AEStronglyMeasurable σ volume := classM_aestronglyMeasurable hσ
  have hφm : AEStronglyMeasurable φ volume := hφ.aestronglyMeasurable
  have hψm : AEStronglyMeasurable ψ volume := hψ.aestronglyMeasurable
  -- the coherence side-goal is `mul_assoc`
  have hcoh : ∀ (x y z : ℝ), (L ((L x) y)) z = (L x) ((L y) z) := by
    intro x y z; simp [hL, mul_assoc]
  -- norm versions of the factors
  have hφnc : Continuous (fun y => ‖φ y‖) := hφ.norm
  have hψnc : Continuous (fun y => ‖ψ y‖) := hψ.norm
  have hφnk : HasCompactSupport (fun y => ‖φ y‖) := hφc.norm
  have hψnk : HasCompactSupport (fun y => ‖ψ y‖) := hψc.norm
  have hσnint : LocallyIntegrable (fun y => ‖σ y‖) volume := by
    intro x; obtain ⟨s, hs, hint⟩ := hσint x; exact ⟨s, hs, hint.norm⟩
  -- `‖σ‖ ⋆ ‖ψ‖` is continuous (locally integrable × continuous compact support)
  have hcSψ : Continuous (convolution (fun y => ‖σ y‖) (fun y => ‖ψ y‖) L volume) :=
    hψnk.continuous_convolution_right L hσnint hψnc
  funext x
  -- LHS: `(φ ⋆ σ) ⋆ ψ = φ ⋆ (σ ⋆ ψ)`
  have hLHS : convolution (convolution φ σ L volume) ψ L volume x
      = convolution φ (convolution σ ψ L volume) L volume x := by
    refine convolution_assoc L L L L hcoh hφm hσm hψm ?_ ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun y => ConvolutionPolynomial.convolutionExists_left_mul hφ hφc hσint y)
    · exact Filter.Eventually.of_forall
        (fun y => ConvolutionPolynomial.convolutionExists_right_mul hσnint hψnc hψnk y)
    · exact ConvolutionPolynomial.convolutionExists_left_mul hφnc hφnk hcSψ.locallyIntegrable x
  -- RHS: `(φ ⋆ ψ) ⋆ σ = φ ⋆ (ψ ⋆ σ)`
  have hRHS : convolution (convolution φ ψ L volume) σ L volume x
      = convolution φ (convolution ψ σ L volume) L volume x := by
    refine convolution_assoc L L L L hcoh hφm hψm hσm ?_ ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun y => ConvolutionPolynomial.convolutionExists_left_mul hφ hφc
          (hψ.locallyIntegrable) y)
    · exact Filter.Eventually.of_forall
        (fun y => ConvolutionPolynomial.convolutionExists_left_mul hψnc hψnk hσnint y)
    · -- `‖ψ‖ ⋆ ‖σ‖ = ‖σ‖ ⋆ ‖ψ‖` is continuous, so `‖φ‖ ⋆ (‖ψ‖⋆‖σ‖)` exists
      have hcom : convolution (fun y => ‖ψ y‖) (fun y => ‖σ y‖) (ContinuousLinearMap.mul ℝ ℝ) volume
          = convolution (fun y => ‖σ y‖) (fun y => ‖ψ y‖) (ContinuousLinearMap.mul ℝ ℝ) volume :=
        ConvolutionPolynomial.convolution_comm_mul _ _
      rw [hcom]
      exact ConvolutionPolynomial.convolutionExists_left_mul hφnc hφnk hcSψ.locallyIntegrable x
  rw [hLHS, hRHS]
  -- inner factors agree by commutativity: `σ ⋆ ψ = ψ ⋆ σ`
  congr 1
  rw [show L = ContinuousLinearMap.mul ℝ ℝ from hL]
  exact ConvolutionPolynomial.convolution_comm_mul σ ψ

/-- **Uniform degree bound.** If every mollification `mollify σ φ` of an `M`-class `σ` by a `C^∞`
compactly-supported kernel `φ` is an everywhere polynomial, then there is a single `d : ℕ` bounding
the degree of *all* of them simultaneously, expressed as the vanishing of the `(d+1)`-st iterated
derivative.

This is the only analytic input to the (D) leaf `exists_nonpoly_mollify`. The proof is elementary
and Baire-free. Fix a normalized smooth bump `ψ₀` with `∫ ψ₀ = 1`; by hypothesis `mollify σ ψ₀` is a
polynomial `p₀`, and we show `d := p₀.natDegree` works. For any test `φ`, with `mollify σ φ = pφ`,
compute `mollify σ (φ⋆ψ₀)` two ways via convolution associativity (`mollify_conv_assoc`):
one route gives `pφ ⋆ ψ₀`, which has `natDegree = pφ.natDegree` since convolving against `ψ₀`
preserves degree (`∫ ψ₀ = 1 ≠ 0`, `natDegree_poly_conv_eq`); the other gives `p₀ ⋆ φ`, which has
`natDegree ≤ p₀.natDegree` (`poly_conv_isPoly`). Both represent the same function, so
`pφ.natDegree ≤ p₀.natDegree` (`Polynomial.funext`), and the bound follows from
`iteratedDeriv_succ_eq_zero_of_natDegree_le`. -/
theorem exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : ClassM σ)
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      IsPolynomialFun (mollify σ φ)) :
    ∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      iteratedDeriv (d + 1) (mollify σ φ) = 0 := by
  -- a fixed smooth compactly-supported bump with `∫ ψ₀ = 1`
  let b0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  set ψ₀ : ℝ → ℝ := b0.normed volume with hψ₀def
  have hψ₀sm : ContDiff ℝ ∞ ψ₀ := b0.contDiff_normed
  have hψ₀cont : Continuous ψ₀ := hψ₀sm.continuous
  have hψ₀c : HasCompactSupport ψ₀ := b0.hasCompactSupport_normed
  have hψ₀int : (∫ y, ψ₀ y) = 1 := b0.integral_normed
  have hψ₀mom : (∫ y, ψ₀ y) ≠ 0 := by rw [hψ₀int]; exact one_ne_zero
  -- bridge: `(p.eval) ⋆ ψ` in the convolution orientation of Task 3's integral
  have hbridge : ∀ (p : Polynomial ℝ) (ψ : ℝ → ℝ),
      convolution (fun x => p.eval x) ψ (ContinuousLinearMap.mul ℝ ℝ) volume
        = fun x => ∫ y, p.eval (x - y) * ψ y := by
    intro p ψ
    rw [ConvolutionPolynomial.convolution_comm_mul]
    funext x
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  -- degree of `mollify σ ψ₀` gives the uniform bound `d₀`
  obtain ⟨p₀, hp₀⟩ := H ψ₀ hψ₀sm hψ₀c
  refine ⟨p₀.natDegree, fun φ hφ hφc => ?_⟩
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨pφ, hpφ⟩ := H φ hφ hφc
  -- it suffices to bound `pφ.natDegree` by `p₀.natDegree`
  suffices hbound : pφ.natDegree ≤ p₀.natDegree by
    rw [hpφ]
    exact IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le hbound
  -- `F := mollify σ (φ ⋆ ψ₀)`, computed two ways
  -- Route A: via `(mollify σ φ) ⋆ ψ₀ = pφ.eval ⋆ ψ₀`, degree `= pφ.natDegree`
  obtain ⟨q1, hq1, hq1deg⟩ := ConvolutionPolynomial.natDegree_poly_conv_eq hψ₀cont hψ₀c pφ hψ₀mom
  -- Route B: via `(mollify σ ψ₀) ⋆ φ = p₀.eval ⋆ φ`, degree `≤ p₀.natDegree`
  obtain ⟨q2, hq2, hq2deg, -⟩ := ConvolutionPolynomial.poly_conv_isPoly hφcont hφc p₀
  -- the two polynomial representations of `F` agree, so `q1 = q2`
  have hFA : mollify σ (convolution φ ψ₀ (ContinuousLinearMap.mul ℝ ℝ) volume)
      = fun x => q1.eval x := by
    rw [← mollify_conv_assoc hσ hφcont hφc hψ₀cont hψ₀c, hpφ, hbridge, hq1]
  have hFB : mollify σ (convolution φ ψ₀ (ContinuousLinearMap.mul ℝ ℝ) volume)
      = fun x => q2.eval x := by
    rw [ConvolutionPolynomial.convolution_comm_mul φ ψ₀,
      ← mollify_conv_assoc hσ hψ₀cont hψ₀c hφcont hφc, hp₀, hbridge, hq2]
  have hq12 : q1 = q2 :=
    Polynomial.funext (fun r => congrFun (hFA.symm.trans hFB) r)
  rw [← hq1deg, hq12]
  exact hq2deg

end TestFunctionDegreeBound
