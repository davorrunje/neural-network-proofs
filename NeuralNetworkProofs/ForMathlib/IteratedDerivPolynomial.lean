/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue

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

-- ---------------------------------------------------------------------------
-- Private helpers for `exists_antideriv`
-- ---------------------------------------------------------------------------

/-- The antiderivative sum has the correct derivative: the `i`-th summand differentiates
to the `i`-th monomial of `q`. -/
private lemma antideriv_sum_derivative (q : Polynomial ℝ) :
    derivative (∑ i ∈ Finset.range (q.natDegree + 1), monomial (i + 1) (q.coeff i / (i + 1)))
      = q := by
  rw [map_sum]
  conv_rhs => rw [q.as_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_monomial, Nat.add_sub_cancel]
  congr 1
  push_cast
  have : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The antiderivative sum has degree `≤ q.degree + 1`. -/
private lemma antideriv_sum_degree (q : Polynomial ℝ) :
    (∑ i ∈ Finset.range (q.natDegree + 1),
        monomial (i + 1) (q.coeff i / (i + 1))).degree ≤ q.degree + 1 := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
  rcases eq_or_ne (q.coeff i) 0 with hci | hci
  · simp [hci]
  · refine (degree_monomial_le _ _).trans ?_
    have hile : (i : WithBot ℕ) ≤ q.degree := le_degree_of_ne_zero hci
    calc ((i + 1 : ℕ) : WithBot ℕ) = (i : WithBot ℕ) + 1 := by push_cast; rfl
      _ ≤ q.degree + 1 := by gcongr

/-- Every real polynomial `q` has a polynomial antiderivative `Q` (`Q.derivative = q`) with
`Q.degree ≤ q.degree + 1`. Built coefficientwise as `∑ i, monomial (i+1) (q.coeff i / (i+1))`. -/
theorem exists_antideriv (q : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, derivative Q = q ∧ Q.degree ≤ q.degree + 1 := by
  exact ⟨_, antideriv_sum_derivative q, antideriv_sum_degree q⟩

-- ---------------------------------------------------------------------------
-- Private helpers for `iteratedDeriv_eq_zero_imp_poly`
-- ---------------------------------------------------------------------------

/-- Cast the `ContDiff` hypothesis from `↑(n+1)` to `(↑n : ℕ∞) + 1`. -/
private lemma contDiff_succ_cast {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) : ContDiff ℝ ((n : ℕ∞) + 1) f := by
  exact_mod_cast hf

/-- Extract `Differentiable ℝ f` from `ContDiff ℝ ((↑n) + 1) f`. -/
private lemma differentiable_of_contDiff_succ {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ ((n : ℕ∞) + 1) f) : Differentiable ℝ f :=
  (contDiff_succ_iff_deriv.mp hf).1

/-- Extract `ContDiff ℝ ↑n (deriv f)` from `ContDiff ℝ ((↑n) + 1) f`. -/
private lemma contDiff_deriv_of_succ {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ ((n : ℕ∞) + 1) f) : ContDiff ℝ (n : ℕ∞) (deriv f) :=
  (contDiff_succ_iff_deriv.mp hf).2.2

/-- The `n`-th iterated derivative of `deriv f` equals the `(n+1)`-th of `f`, so it vanishes. -/
private lemma iteratedDeriv_deriv_eq_zero {f : ℝ → ℝ} {n : ℕ}
    (h : ∀ x, iteratedDeriv (n + 1) f x = 0) :
    ∀ x, iteratedDeriv n (deriv f) x = 0 := fun x => by
  rw [← iteratedDeriv_succ']; exact h x

/-- `HasDerivAt (fun x => Q.eval x) (q.eval x) x` when `Q.derivative = q`. -/
private lemma hasDerivAt_antideriv (Q q : Polynomial ℝ) (hQ : derivative Q = q) (x : ℝ) :
    HasDerivAt (fun x => Q.eval x) (q.eval x) x := by
  have := Q.hasDerivAt x; rwa [hQ] at this

/-- If `deriv f = q.eval` and `HasDerivAt Q.eval (q.eval ·)`, then `deriv (f - Q.eval) = 0`. -/
private lemma deriv_sub_antideriv_eq_zero {f : ℝ → ℝ} {Q q : Polynomial ℝ}
    (hdiff : Differentiable ℝ f)
    (hq : ∀ x, deriv f x = q.eval x)
    (hQderiv : ∀ x, HasDerivAt (fun x => Q.eval x) (q.eval x) x) :
    ∀ x, deriv (fun x => f x - Q.eval x) x = 0 := fun x => by
  have hfx : HasDerivAt f (deriv f x) x := (hdiff x).hasDerivAt
  have : HasDerivAt (fun x => f x - Q.eval x) (deriv f x - q.eval x) x :=
    hfx.sub (hQderiv x)
  rw [this.deriv, hq x, sub_self]

/-- If `deriv (f - Q.eval) = 0` everywhere, then `f - Q.eval` is constant. -/
private lemma sub_antideriv_const {f : ℝ → ℝ} {Q : Polynomial ℝ}
    (hdiff : Differentiable ℝ f)
    (hzero : ∀ x, deriv (fun x => f x - Q.eval x) x = 0) :
    ∀ x y, f x - Q.eval x = f y - Q.eval y :=
  is_const_of_deriv_eq_zero (hdiff.sub Q.differentiable) hzero

/-- If `q.degree < n` (as a `WithBot ℕ` inequality), then `q.degree + 1 ≤ n`. -/
private lemma degree_add_one_le_of_lt {q : Polynomial ℝ} {n : ℕ}
    (hqdeg : q.degree < (n : ℕ)) : (q.degree : WithBot ℕ) + 1 ≤ (n : ℕ) := by
  rcases eq_or_ne q.degree ⊥ with hb | hb
  · simp [hb]
  · obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← hm] at hqdeg ⊢
    have : m < n := WithBot.coe_lt_coe.mp hqdeg
    calc (m : WithBot ℕ) + 1 = ((m + 1 : ℕ) : WithBot ℕ) := by push_cast; rfl
      _ ≤ (n : ℕ) := by exact_mod_cast Nat.succ_le_of_lt this

/-- `(Q + C c).degree ≤ n` when `Q.degree ≤ q.degree + 1` and `q.degree + 1 ≤ n`. -/
private lemma degree_add_const_le {Q q : Polynomial ℝ} {n : ℕ} (c : ℝ)
    (hQdeg : Q.degree ≤ q.degree + 1)
    (hn : (q.degree : WithBot ℕ) + 1 ≤ (n : ℕ)) :
    (Q + C c).degree ≤ (n : ℕ) :=
  (degree_add_le _ _).trans (max_le (hQdeg.trans hn)
    (degree_C_le.trans (by exact_mod_cast Nat.zero_le _)))

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
    exact ⟨0, fun x => by simp [h x], by simp [degree_zero]⟩
  | succ n ih =>
    have hsucc : ContDiff ℝ ((n : ℕ∞) + 1) f := contDiff_succ_cast hf
    have hdiff : Differentiable ℝ f := differentiable_of_contDiff_succ hsucc
    have hderiv : ContDiff ℝ (n : ℕ∞) (deriv f) := contDiff_deriv_of_succ hsucc
    obtain ⟨q, hq, hqdeg⟩ := ih hderiv (iteratedDeriv_deriv_eq_zero h)
    obtain ⟨Q, hQ, hQdeg⟩ := exists_antideriv q
    have hQderiv : ∀ x, HasDerivAt (fun x => Q.eval x) (q.eval x) x :=
      hasDerivAt_antideriv Q q hQ
    have hconst : ∀ x y, f x - Q.eval x = f y - Q.eval y :=
      sub_antideriv_const hdiff (deriv_sub_antideriv_eq_zero hdiff hq hQderiv)
    set c := f 0 - Q.eval 0 with hc
    have hn : (q.degree : WithBot ℕ) + 1 ≤ (n : ℕ) := degree_add_one_le_of_lt hqdeg
    refine ⟨Q + C c, fun x => ?_, lt_of_le_of_lt (degree_add_const_le c hQdeg hn) ?_⟩
    · have heq := hconst x 0
      rw [← hc] at heq
      have : f x = Q.eval x + c := by linarith
      rw [this]; simp
    · exact_mod_cast Nat.lt_succ_self n

/-- The `n`-th iterate of `deriv` applied to a polynomial's evaluation map is the evaluation map of
the `n`-th iterate of `Polynomial.derivative`:
`deriv^[n] (fun x => q.eval x) = fun x => (derivative^[n] q).eval x`. -/
theorem iteratedDeriv_eval (n : ℕ) (q : Polynomial ℝ) :
    deriv^[n] (fun x => q.eval x) = fun x => (derivative^[n] q).eval x := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    funext x
    rw [Polynomial.deriv, Function.iterate_succ', Function.comp_apply]

/-- The converse direction: a polynomial of `natDegree ≤ d` has vanishing `(d+1)`-st iterated
derivative (as a function `ℝ → ℝ`). -/
theorem iteratedDeriv_succ_eq_zero_of_natDegree_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p.natDegree ≤ d) :
    iteratedDeriv (d + 1) (fun x => p.eval x) = 0 := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eval (d + 1) p,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_of_le hp)]
  funext x
  rw [Polynomial.eval_zero]
  rfl

end IteratedDerivPolynomial
