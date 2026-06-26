import Mathlib

/-! # A function with a vanishing iterated derivative is a polynomial.
Intended Mathlib home: `Mathlib/Analysis/Calculus/IteratedDeriv/` (confirm with maintainers).

This is the analytic *converse* of the standard Mathlib facts that a polynomial's
iterated derivative eventually vanishes (`Polynomial.iterate_derivative_eq_zero`,
`Polynomial.iterate_derivative_eq_zero_of_degree_lt`). Those go from polynomial to
"derivative is zero"; here we go the other way: vanishing `n`-th derivative forces the
function to *be* a polynomial of degree `< n`. As of the toolchain pin
(`v4.32.0-rc1`) no such statement was found via `lean_leansearch`/`lean_loogle`
(searches returned only the forward direction and the analytic-order characterisation
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`). -/

namespace IteratedDerivPolynomial

open Polynomial

/-- If the `n`-th iterated derivative of `f : ℝ → ℝ` vanishes identically, then `f`
agrees (everywhere) with a polynomial function of degree `< n`. Needed for the Leshno smooth-engine
step (a nonpolynomial smooth function has some nonvanishing derivative of every order).
Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1.

Proof strategy (for the later non-`sorry` cycle): induction on `n` via `iteratedDeriv_succ`
(the `n`-th derivative is the first derivative of the `(n-1)`-th). Base case `n = 0` gives
`f = 0` directly. In the step, a function on `ℝ` whose derivative is everywhere `0` is constant
(`is_const_of_fderiv_eq_zero`); integrating the polynomial of degree `< n - 1`
obtained from the inductive hypothesis raises the degree by one to `< n`. -/
theorem iteratedDeriv_eq_zero_imp_poly {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (h : ∀ x, iteratedDeriv n f x = 0) :
    ∃ p : Polynomial ℝ, (∀ x, f x = p.eval x) ∧ p.natDegree < n := by
  sorry

end IteratedDerivPolynomial
