import NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM
import NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import NeuralNetworkProofs.UniversalApproximation.Leshno.SmoothEngine
import NeuralNetworkProofs.UniversalApproximation.Leshno.Mollify
import NeuralNetworkProofs.UniversalApproximation.Leshno.Ridge
import NeuralNetworkProofs.UniversalApproximation.Leshno.Converse
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem

/-! # The Leshno (1993) universal approximation theorem (`M`-class activations).

Root re-export of the top-down scaffold proving the headline equivalence

  `leshno_dense_iff {σ} (hσ : ClassM σ) : DenselyApproximates σ ↔ ¬ IsAEPolynomial σ`

for the Leshno activation class `M` (locally bounded; closure of the discontinuity set is
Lebesgue-null). A single-hidden-layer network with activation `σ` densely approximates every
continuous function on every compact `K ⊆ ℝⁿ` **iff** `σ` is not (Lebesgue-a.e.) a polynomial.

## Module layout

* `ClassM` — the activation class `M`, `IsAEPolynomial`, `IsPolynomialFun`.
* `Family` — the generator family `genFun`/`genSpan`, the continuous core `T`, `T_isClosed`,
  `DenselyApproximates`, and the reduction `denselyApproximates_of_forall_T_eq_top`.
* `SmoothEngine` — the smooth derivative-trick engine (`Sg`, `deriv_pow_mem`, `exists_deriv_ne`,
  `smooth_engine`).
* `Mollify` — mollification (`mollify`, `contDiff_mollify`, `exists_nonpoly_mollify`,
  `mollify_ridge_mem_T`).
* `Ridge` — the univariate ⇒ multivariate lift (`UnivariateDense`, `ridge_mem_T`, `ridge_density`).
* `Converse` — the converse direction (`aePolynomial_not_dense`).
* `Theorem` — the final assembly (`univariate_density`, `leshno_dense`, `leshno_dense_iff`).

## Admit inventory (now `sorry`-free)

The headline `leshno_dense_iff` and its supporting theorems are fully proved as *glue*. Every deep
analytic leaf originally scaffolded is now proved: the development has **0 `sorry` leaves**. So
`lean_verify`/`#print axioms` on the top-level theorems should report only
`[propext, Classical.choice, Quot.sound]` once the compiled `.olean` artifacts are rebuilt.

**Proved (no longer leaves):**
* `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly` (Contrib) — vanishing `n`-th derivative
  ⇒ polynomial of `degree < n`. *Proved.*
* `RidgePowersSpan.ridgePow_span` (Contrib) — homogeneous polynomials are spanned by ridge powers
  (polarization). *Proved.*
* `SmoothEngine.deriv_pow_mem` — `t ↦ tᵏ · g⁽ᵏ⁾(λt+b)` lies in the closure of `Sg g`. *Proved* (so
  `SmoothEngine.smooth_engine` is now fully `sorryAx`-free).
* `Mollify.contDiff_mollify` — the mollification of an `M`-class `σ` by a smooth compactly-supported
  kernel is `C^∞`. *Proved.*
* `TestFunctionDegreeBound.exists_uniform_degree_bound` (Contrib) — a uniform polynomial-degree
  bound for all mollifications `mollify σ φ`. *Proved* via an algebraic degree-invariance argument
  (convolution associativity + "polynomial ⋆ test function preserves degree when the kernel's `0`-th
  moment is nonzero"), sidestepping the Baire/`BaireSpace` route entirely. New Contrib supports:
  `ConvolutionPolynomial.monomial_conv_isPoly`, `…poly_conv_isPoly`, `…natDegree_poly_conv_eq`,
  `…convolution_comm_mul`, `IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le`.
* `Mollify.exists_nonpoly_mollify` — a non-a.e.-polynomial `M`-class `σ` admits a kernel whose
  mollification is not an everywhere polynomial. **Now fully proved** (`sorryAx`-free) from the
  degree bound above plus `ConvolutionIteratedDeriv.iteratedDeriv_convolution_left`,
  `SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero`, and
  `PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing`.
* `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` (Contrib) — uniform
  Riemann-sum approximation of the convolution for an a.e.-continuous (M-class) kernel; the analytic
  core consumed by `Mollify.mollify_ridge_mem_T`. **Now proved** (`sorryAx`-free) by the classical
  good/bad-cell argument — cells split into good cells (uniform continuity of the kernel on a
  compact complement of a metric thickening of the discontinuity-closure) and bad cells (measure
  controlled by `tendsto_measure_cthickening_of_isCompact`), with the budgets uniform in the
  translation parameter. New Contrib supports: `UniformRiemannConvolution.exists_uniform_bound`,
  `…uniformContinuousOn_off_disc`, `…exists_cthickening_measure_lt`.

With this last leaf closed, `Mollify.mollify_ridge_mem_T`, `univariate_density`, `leshno_dense`, and
`leshno_dense_iff` are all `sorryAx`-free at the source level.

Everything else — the `ClassM`/`Family`/`T` infrastructure, `exists_deriv_ne` (**proved**, not a
leaf), `smooth_engine`, the ridge lift, the converse, and the final assembly — is proved outright.
-/
