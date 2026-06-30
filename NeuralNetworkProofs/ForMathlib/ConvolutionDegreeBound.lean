/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import NeuralNetworkProofs.ForMathlib.ConvolutionPolynomial
import NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial

/-! # Uniform iterated-derivative bound for polynomial convolutions.

If convolving a fixed locally integrable `σ` against every smooth compactly-supported test function
yields an everywhere polynomial, then a single `d` bounds all those polynomials' degrees
simultaneously (equivalently, the `(d+1)`-st iterated derivative of each such convolution vanishes).

The argument is elementary and Baire-free: convolving against a fixed normalized bump `ψ₀`
(`∫ ψ₀ = 1`) preserves polynomial degree, and associativity/commutativity of convolution relates
`φ ⋆ σ` to `ψ₀ ⋆ σ`. Intended Mathlib home: alongside `Mathlib/Analysis/Convolution`. -/

namespace ConvolutionDegreeBound

open MeasureTheory

open scoped ContDiff

-- ---------------------------------------------------------------------------
-- Private helpers for conv_left_comm_mul
-- ---------------------------------------------------------------------------

/-- `ContinuousLinearMap.mul ℝ ℝ` satisfies the associativity coherence condition for
`convolution_assoc`. -/
private lemma mul_bilin_assoc : ∀ (x y z : ℝ),
    ((ContinuousLinearMap.mul ℝ ℝ) ((ContinuousLinearMap.mul ℝ ℝ) x y)) z
      = (ContinuousLinearMap.mul ℝ ℝ) x ((ContinuousLinearMap.mul ℝ ℝ) y z) := by
  intro x y z; simp [mul_assoc]

/-- Local integrability of `‖σ‖` follows from local integrability of `σ`. -/
private lemma locallyIntegrable_norm {σ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume) :
    LocallyIntegrable (fun y => ‖σ y‖) volume := by
  intro x; obtain ⟨s, hs, hint⟩ := hσ x; exact ⟨s, hs, hint.norm⟩

/-- Continuity of `‖σ‖ ⋆ ‖ψ‖` when `σ` is locally integrable, `ψ` continuous with compact
support. -/
private lemma norm_conv_continuous {σ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous (convolution (fun y => ‖σ y‖) (fun y => ‖ψ y‖)
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
  hψc.norm.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_norm hσ) hψ.norm

/-- LHS associativity step: `(φ ⋆ σ) ⋆ ψ = φ ⋆ (σ ⋆ ψ)` pointwise. -/
private lemma conv_assoc_lhs {σ φ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (x : ℝ) :
    convolution (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) ψ
        (ContinuousLinearMap.mul ℝ ℝ) volume x
      = convolution φ (convolution σ ψ (ContinuousLinearMap.mul ℝ ℝ) volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  refine convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) mul_bilin_assoc
    hφ.aestronglyMeasurable hσ.aestronglyMeasurable hψ.aestronglyMeasurable ?_ ?_ ?_
  · exact Filter.Eventually.of_forall
      (fun y => ConvolutionPolynomial.convolutionExists_left_mul hφ hφc hσ y)
  · exact Filter.Eventually.of_forall
      (fun y => ConvolutionPolynomial.convolutionExists_right_mul
        (locallyIntegrable_norm hσ) hψ.norm hψc.norm y)
  · exact ConvolutionPolynomial.convolutionExists_left_mul hφ.norm hφc.norm
      (norm_conv_continuous hσ hψ hψc).locallyIntegrable x

/-- RHS associativity step: `(φ ⋆ ψ) ⋆ σ = φ ⋆ (ψ ⋆ σ)` pointwise. -/
private lemma conv_assoc_rhs {σ φ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (x : ℝ) :
    convolution (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) σ
        (ContinuousLinearMap.mul ℝ ℝ) volume x
      = convolution φ (convolution ψ σ (ContinuousLinearMap.mul ℝ ℝ) volume)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  refine convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) mul_bilin_assoc
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable hσ.aestronglyMeasurable ?_ ?_ ?_
  · exact Filter.Eventually.of_forall
      (fun y => ConvolutionPolynomial.convolutionExists_left_mul hφ hφc hψ.locallyIntegrable y)
  · exact Filter.Eventually.of_forall
      (fun y => ConvolutionPolynomial.convolutionExists_left_mul hψ.norm hψc.norm
        (locallyIntegrable_norm hσ) y)
  · have hcom :
        convolution (fun y => ‖ψ y‖) (fun y => ‖σ y‖) (ContinuousLinearMap.mul ℝ ℝ) volume
          = convolution (fun y => ‖σ y‖) (fun y => ‖ψ y‖) (ContinuousLinearMap.mul ℝ ℝ) volume :=
      ConvolutionPolynomial.convolution_comm_mul _ _
    rw [hcom]
    exact ConvolutionPolynomial.convolutionExists_left_mul hφ.norm hφc.norm
      (norm_conv_continuous hσ hψ hψc).locallyIntegrable x

-- ---------------------------------------------------------------------------
-- Public theorem (1 of 2) — needed by the helpers below
-- ---------------------------------------------------------------------------

/-- `(φ ⋆ σ) ⋆ ψ = (φ ⋆ ψ) ⋆ σ` for the real (`mul`) convolution, with `σ` locally integrable
and `φ, ψ` continuous with compact support. -/
theorem conv_left_comm_mul {σ φ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    convolution (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) ψ
        (ContinuousLinearMap.mul ℝ ℝ) volume
      = convolution (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) σ
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  -- LHS: `(φ ⋆ σ) ⋆ ψ = φ ⋆ (σ ⋆ ψ)`
  have hLHS := conv_assoc_lhs hσ hφ hφc hψ hψc x
  -- RHS: `(φ ⋆ ψ) ⋆ σ = φ ⋆ (ψ ⋆ σ)`
  have hRHS := conv_assoc_rhs hσ hφ hφc hψ hψc x
  rw [hLHS, hRHS]
  -- inner factors agree by commutativity: `σ ⋆ ψ = ψ ⋆ σ`
  congr 1
  exact ConvolutionPolynomial.convolution_comm_mul σ ψ

-- ---------------------------------------------------------------------------
-- Private helpers for exists_uniform_degree_bound
-- ---------------------------------------------------------------------------

/-- Orientation bridge: `(p.eval) ⋆ ψ` as a convolution equals the explicit integral form
used by `natDegree_poly_conv_eq`. -/
private lemma poly_conv_bridge (p : Polynomial ℝ) (ψ : ℝ → ℝ) :
    convolution (fun x => p.eval x) ψ (ContinuousLinearMap.mul ℝ ℝ) volume
      = fun x => ∫ y, p.eval (x - y) * ψ y := by
  rw [ConvolutionPolynomial.convolution_comm_mul]
  funext x
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- Route A: `(φ ⋆ ψ₀) ⋆ σ = q1.eval` via rewriting through `(φ ⋆ σ) ⋆ ψ₀ = pφ ⋆ ψ₀`. -/
private lemma route_A_eq {σ φ ψ₀ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφcont : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ₀cont : Continuous ψ₀) (hψ₀c : HasCompactSupport ψ₀)
    {pφ : Polynomial ℝ}
    (hpφ : convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => pφ.eval t)
    {q1 : Polynomial ℝ}
    (hq1 : (fun x => ∫ y, pφ.eval (x - y) * ψ₀ y) = fun x => q1.eval x) :
    convolution (convolution φ ψ₀ (ContinuousLinearMap.mul ℝ ℝ) volume) σ
        (ContinuousLinearMap.mul ℝ ℝ) volume
      = fun x => q1.eval x := by
  rw [← conv_left_comm_mul hσ hφcont hφc hψ₀cont hψ₀c, hpφ, poly_conv_bridge, hq1]

/-- Route B: `(φ ⋆ ψ₀) ⋆ σ = q2.eval` via rewriting through `(ψ₀ ⋆ φ) ⋆ σ = p₀ ⋆ φ`. -/
private lemma route_B_eq {σ φ ψ₀ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφcont : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ₀cont : Continuous ψ₀) (hψ₀c : HasCompactSupport ψ₀)
    {p₀ : Polynomial ℝ}
    (hp₀ : convolution ψ₀ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => p₀.eval t)
    {q2 : Polynomial ℝ}
    (hq2 : (fun x => ∫ y, p₀.eval (x - y) * φ y) = fun x => q2.eval x) :
    convolution (convolution φ ψ₀ (ContinuousLinearMap.mul ℝ ℝ) volume) σ
        (ContinuousLinearMap.mul ℝ ℝ) volume
      = fun x => q2.eval x := by
  rw [ConvolutionPolynomial.convolution_comm_mul φ ψ₀,
    ← conv_left_comm_mul hσ hψ₀cont hψ₀c hφcont hφc, hp₀, poly_conv_bridge, hq2]

-- ---------------------------------------------------------------------------
-- Public theorem (2 of 2)
-- ---------------------------------------------------------------------------

/-- **Uniform degree bound.** If convolving a fixed locally integrable `σ` against every `C^∞`
compactly-supported kernel `φ` is an everywhere polynomial, then there is a single `d : ℕ` bounding
the degree of *all* of them simultaneously, expressed as the vanishing of the `(d+1)`-st iterated
derivative.

The proof is elementary and Baire-free. Fix a normalized smooth bump `ψ₀` with `∫ ψ₀ = 1`; by
hypothesis `ψ₀ ⋆ σ` is a polynomial `p₀`, and we show `d := p₀.natDegree` works. For any test `φ`,
with `φ ⋆ σ = pφ`, compute `(φ ⋆ ψ₀) ⋆ σ` two ways via convolution associativity/commutativity
(`conv_left_comm_mul`): one route gives `pφ ⋆ ψ₀`, which has `natDegree = pφ.natDegree` since
convolving against `ψ₀` preserves degree (`∫ ψ₀ = 1 ≠ 0`, `natDegree_poly_conv_eq`); the other
gives `p₀ ⋆ φ`, which has `natDegree ≤ p₀.natDegree` (`poly_conv_isPoly`). Both represent the same
function, so `pφ.natDegree ≤ p₀.natDegree` (`Polynomial.funext`), and the bound follows from
`iteratedDeriv_succ_eq_zero_of_natDegree_le`. -/
theorem exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ p : Polynomial ℝ,
        convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => p.eval t) :
    ∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      iteratedDeriv (d + 1) (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) = 0 := by
  -- a fixed smooth compactly-supported bump with `∫ ψ₀ = 1`
  let b0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  set ψ₀ : ℝ → ℝ := b0.normed volume with hψ₀def
  have hψ₀sm : ContDiff ℝ ∞ ψ₀ := b0.contDiff_normed
  have hψ₀cont : Continuous ψ₀ := hψ₀sm.continuous
  have hψ₀c : HasCompactSupport ψ₀ := b0.hasCompactSupport_normed
  have hψ₀int : (∫ y, ψ₀ y) = 1 := b0.integral_normed
  have hψ₀mom : (∫ y, ψ₀ y) ≠ 0 := by rw [hψ₀int]; exact one_ne_zero
  -- degree of `ψ₀ ⋆ σ` gives the uniform bound `d₀`
  obtain ⟨p₀, hp₀⟩ := H ψ₀ hψ₀sm hψ₀c
  refine ⟨p₀.natDegree, fun φ hφ hφc => ?_⟩
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨pφ, hpφ⟩ := H φ hφ hφc
  -- it suffices to bound `pφ.natDegree` by `p₀.natDegree`
  suffices hbound : pφ.natDegree ≤ p₀.natDegree by
    rw [hpφ]
    exact IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le hbound
  -- Route A: via `(φ ⋆ σ) ⋆ ψ₀ = pφ ⋆ ψ₀`, degree `= pφ.natDegree`
  obtain ⟨q1, hq1, hq1deg⟩ := ConvolutionPolynomial.natDegree_poly_conv_eq hψ₀cont hψ₀c pφ hψ₀mom
  -- Route B: via `(ψ₀ ⋆ σ) ⋆ φ = p₀ ⋆ φ`, degree `≤ p₀.natDegree`
  obtain ⟨q2, hq2, hq2deg, -⟩ := ConvolutionPolynomial.poly_conv_isPoly hφcont hφc p₀
  -- the two polynomial representations of `F` agree, so `q1 = q2`
  have hFA := route_A_eq hσ hφcont hφc hψ₀cont hψ₀c hpφ hq1
  have hFB := route_B_eq hσ hφcont hφc hψ₀cont hψ₀c hp₀ hq2
  have hq12 : q1 = q2 :=
    Polynomial.funext (fun r => congrFun (hFA.symm.trans hFB) r)
  rw [← hq1deg, hq12]
  exact hq2deg

end ConvolutionDegreeBound
