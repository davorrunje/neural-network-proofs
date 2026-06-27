import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family
import LeanPlayground.UniversalApproximation.Leshno.SmoothEngine
import LeanPlayground.UniversalApproximation.Leshno.Mollify
import LeanPlayground.UniversalApproximation.Leshno.Ridge
import LeanPlayground.UniversalApproximation.Leshno.Converse
import LeanPlayground.UniversalApproximation.Leshno.Theorem

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

## Admit inventory (documented `sorry` leaves)

The headline `leshno_dense_iff` and its supporting theorems are fully proved as *glue*. Of the deep
analytic leaves originally scaffolded, all but one are now proved. Exactly **one `sorry`** remains in
the whole development — a single documented research leaf with a precise blocker note — so
`lean_verify`/`#print axioms` reporting `sorryAx` on the top-level theorems (and on
`Mollify.mollify_ridge_mem_T`, which consumes that leaf) is expected and fully accounted for.

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

**Remaining documented research leaf (1 `sorry`):**
* `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` (Contrib) — uniform
  Riemann-sum approximation of the convolution for an a.e.-continuous (M-class) kernel; the analytic
  core consumed by `Mollify.mollify_ridge_mem_T` (the latter is otherwise fully assembled). *Blocked*
  on measure-theoretic infrastructure absent from Mathlib (a parameter-uniform Riemann/Lebesgue
  criterion, or measurability of the uncountable-index oscillation supremum); see its docstring for
  the two investigated routes and the remaining tractable good/bad-cell approach.

Everything else — the `ClassM`/`Family`/`T` infrastructure, `exists_deriv_ne` (**proved**, not a
leaf), `smooth_engine`, the ridge lift, the converse, and the final assembly — is proved outright.
-/
