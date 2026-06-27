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

/-- Every real polynomial `q` has a polynomial antiderivative `Q` (`Q.derivative = q`) with
`Q.degree ≤ q.degree + 1`. Built coefficientwise as `∑ i, monomial (i+1) (q.coeff i / (i+1))`. -/
theorem exists_antideriv (q : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, derivative Q = q ∧ Q.degree ≤ q.degree + 1 := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), monomial (i + 1) (q.coeff i / (i + 1)), ?_, ?_⟩
  · rw [map_sum]
    conv_rhs => rw [q.as_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [derivative_monomial, Nat.add_sub_cancel]
    congr 1
    push_cast
    have : ((i : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · refine (degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
    rcases eq_or_ne (q.coeff i) 0 with hci | hci
    · simp [hci]
    · refine (degree_monomial_le _ _).trans ?_
      have hile : (i : WithBot ℕ) ≤ q.degree := le_degree_of_ne_zero hci
      calc ((i + 1 : ℕ) : WithBot ℕ) = (i : WithBot ℕ) + 1 := by push_cast; rfl
        _ ≤ q.degree + 1 := by gcongr

/-- If the `n`-th iterated derivative of `f : ℝ → ℝ` vanishes identically, then `f`
agrees (everywhere) with a polynomial function of degree `< n` (as `Polynomial.degree`, so the
zero polynomial — `degree = ⊥` — is covered at `n = 0`). Needed for the Leshno smooth-engine
step (a nonpolynomial smooth function has some nonvanishing derivative of every order).
Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1.

Proof: induction on `n` via `iteratedDeriv_succ'` (the `n`-th derivative is the `(n-1)`-th
derivative of `deriv f`). Base case `n = 0` gives `f = 0`, take `p = 0`. In the step, the IH
yields a polynomial `q` with `deriv f = q.eval` and `q.degree < n`; we integrate `q` to a
polynomial antiderivative `Q` (built coefficientwise, with `Q.derivative = q`), so
`deriv (f - Q.eval) = 0`, hence `f - Q.eval` is constant (`is_const_of_deriv_eq_zero`) and
`f = (Q + C c).eval` with `(Q + C c).degree < n + 1`. -/
theorem iteratedDeriv_eq_zero_imp_poly {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ∞) f) (h : ∀ x, iteratedDeriv n f x = 0) :
    ∃ p : Polynomial ℝ, (∀ x, f x = p.eval x) ∧ p.degree < (n : ℕ) := by
  induction n generalizing f with
  | zero =>
    simp only [iteratedDeriv_zero] at h
    refine ⟨0, fun x => ?_, ?_⟩
    · simp [h x]
    · simp [degree_zero]
  | succ n ih =>
    -- `f` is differentiable and `deriv f` is `ContDiff ℝ (↑n)`.
    have hsucc : ContDiff ℝ ((n : ℕ∞) + 1) f := by
      convert hf using 2
      push_cast
      rfl
    have hdiff : Differentiable ℝ f := (contDiff_succ_iff_deriv.mp hsucc).1
    have hderiv : ContDiff ℝ (n : ℕ∞) (deriv f) := (contDiff_succ_iff_deriv.mp hsucc).2.2
    -- IH on `deriv f`.
    have hh : ∀ x, iteratedDeriv n (deriv f) x = 0 := by
      intro x
      rw [← iteratedDeriv_succ']
      exact h x
    obtain ⟨q, hq, hqdeg⟩ := ih hderiv hh
    -- Antiderivative `Q` of `q`.
    obtain ⟨Q, hQ, hQdeg⟩ := exists_antideriv q
    -- `deriv (fun x => f x - Q.eval x) = 0`.
    have hQderiv : ∀ x, HasDerivAt (fun x => Q.eval x) (q.eval x) x := by
      intro x
      have := Q.hasDerivAt x
      rwa [hQ] at this
    have hconst : ∀ x y, f x - Q.eval x = f y - Q.eval y := by
      have hdiffsub : Differentiable ℝ (fun x => f x - Q.eval x) := by
        exact hdiff.sub (Q.differentiable)
      have hzero : ∀ x, deriv (fun x => f x - Q.eval x) x = 0 := by
        intro x
        have hfx : HasDerivAt f (deriv f x) x := (hdiff x).hasDerivAt
        have : HasDerivAt (fun x => f x - Q.eval x) (deriv f x - q.eval x) x :=
          hfx.sub (hQderiv x)
        rw [this.deriv, hq x, sub_self]
      exact fun x y => is_const_of_deriv_eq_zero hdiffsub hzero x y
    -- The constant `c = f 0 - Q.eval 0`.
    set c := f 0 - Q.eval 0 with hc
    refine ⟨Q + C c, fun x => ?_, ?_⟩
    · have := hconst x 0
      rw [← hc] at this
      have : f x = Q.eval x + c := by linarith
      rw [this]
      simp
    · -- degree (Q + C c) ≤ n < n + 1
      have hn : (q.degree : WithBot ℕ) + 1 ≤ (n : ℕ) := by
        rcases eq_or_ne q.degree ⊥ with hb | hb
        · simp [hb]
        · obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hb
          rw [← hm] at hqdeg ⊢
          have : m < n := WithBot.coe_lt_coe.mp hqdeg
          calc (m : WithBot ℕ) + 1 = ((m + 1 : ℕ) : WithBot ℕ) := by push_cast; rfl
            _ ≤ (n : ℕ) := by exact_mod_cast Nat.succ_le_of_lt this
      have hQc : (Q + C c).degree ≤ (n : ℕ) := by
        refine (degree_add_le _ _).trans (max_le ?_ ?_)
        · exact hQdeg.trans hn
        · exact degree_C_le.trans (by exact_mod_cast Nat.zero_le _)
      refine lt_of_le_of_lt hQc ?_
      exact_mod_cast Nat.lt_succ_self n

/-- The converse direction: a polynomial of `natDegree ≤ d` has vanishing `(d+1)`-st iterated
derivative (as a function `ℝ → ℝ`). -/
theorem iteratedDeriv_succ_eq_zero_of_natDegree_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p.natDegree ≤ d) :
    iteratedDeriv (d + 1) (fun x => p.eval x) = 0 := by
  have key : ∀ (n : ℕ) (q : Polynomial ℝ),
      deriv^[n] (fun x => q.eval x) = fun x => (derivative^[n] q).eval x := by
    intro n
    induction n with
    | zero => intro q; rfl
    | succ k ih =>
      intro q
      rw [Function.iterate_succ', Function.comp_apply, ih q]
      funext x
      rw [Polynomial.deriv, Function.iterate_succ', Function.comp_apply]
  rw [iteratedDeriv_eq_iterate, key (d + 1) p,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_of_le hp)]
  funext x
  rw [Polynomial.eval_zero]
  rfl

end IteratedDerivPolynomial
