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

The headline `leshno_dense_iff` and its supporting theorems are fully proved as *glue*. Of the six
deep analytic leaves originally scaffolded, **four are now proved** and **two remain** (each a
self-contained fact, recorded here so `lean_verify` reporting `sorryAx` is expected and accounted
for).

**Proved (no longer leaves):**
* `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly` (Contrib) — vanishing `n`-th derivative
  ⇒ polynomial of `degree < n`. *Proved.*
* `RidgePowersSpan.ridgePow_span` (Contrib) — homogeneous polynomials are spanned by ridge powers
  (polarization). *Proved.*
* `SmoothEngine.deriv_pow_mem` — `t ↦ tᵏ · g⁽ᵏ⁾(λt+b)` lies in the closure of `Sg g`. *Proved* (so
  `SmoothEngine.smooth_engine` is now fully `sorryAx`-free).
* `Mollify.contDiff_mollify` — the mollification of an `M`-class `σ` by a smooth compactly-supported
  kernel is `C^∞`. *Proved.*

**Remaining documented leaves (2):**
* `Mollify.exists_nonpoly_mollify` — a non-a.e.-polynomial `M`-class `σ` admits a kernel whose
  mollification is not an everywhere polynomial. (Distribution theory: uniform degree bound +
  moment-vanishing antiderivatives + distributional polynomial recovery.)
* `Mollify.mollify_ridge_mem_T` — every dilated/translated ridge of a mollified `M`-class `σ` lands
  in the continuous core `T`. (Uniform Riemann-sum approximation of the convolution; the M-class
  analytic core.)

Everything else — the `ClassM`/`Family`/`T` infrastructure, `exists_deriv_ne` (**proved**, not a
leaf), `smooth_engine`, the ridge lift, the converse, and the final assembly — is proved outright.
-/
