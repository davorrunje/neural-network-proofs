import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM

/-! # Mollification: definition and the convolution identity.

Split out of `Mollify.lean` so both the consumer `Mollify.exists_nonpoly_mollify` and the
Baire-category leaf `TestFunctionDegreeBound.exists_uniform_degree_bound` can refer to `mollify`
without a circular import. -/

namespace UniversalApproximation.Leshno

open MeasureTheory

open scoped ContDiff

/-- Mollification of `σ` by a smooth compactly-supported kernel `φ` (convolution). -/
noncomputable def mollify (σ φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, σ (x - y) * φ y

/-- `mollify σ φ` is the Mathlib (scalar-multiplication) convolution `φ ⋆ σ`: indeed
`(φ ⋆ σ) x = ∫ t, φ t * σ (x - t)`, whose integrand agrees with `σ (x - t) * φ t` by `mul_comm`. -/
theorem mollify_eq_convolution (σ φ : ℝ → ℝ) :
    mollify σ φ = convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

end UniversalApproximation.Leshno
