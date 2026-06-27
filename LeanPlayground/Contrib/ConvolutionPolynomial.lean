import Mathlib

/-! # Convolution of polynomials with test functions, and commutativity for the `mul` pairing.
Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/

namespace ConvolutionPolynomial

open MeasureTheory

open scoped ContDiff

/-- Commutativity of the real convolution taken against scalar multiplication `mul ℝ ℝ`. -/
theorem convolution_comm_mul (f g : ℝ → ℝ) :
    convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume
      = convolution g f (ContinuousLinearMap.mul ℝ ℝ) volume := by
  nth_rewrite 1 [← ContinuousLinearMap.flip_mul]
  rw [convolution_flip]

/-- `φ ⋆ σ` exists pointwise when `φ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_left_mul {φ σ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hσ : LocallyIntegrable σ volume) :
    ConvolutionExists φ σ (ContinuousLinearMap.mul ℝ ℝ) volume :=
  hφc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hφ hσ

/-- `σ ⋆ ψ` exists pointwise when `ψ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_right_mul {σ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ConvolutionExists σ ψ (ContinuousLinearMap.mul ℝ ℝ) volume :=
  hψc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hσ hψ

end ConvolutionPolynomial
