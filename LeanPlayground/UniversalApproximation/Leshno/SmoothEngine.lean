import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.Contrib.IteratedDerivPolynomial

/-! # The univariate smooth derivative-trick engine for the Leshno UAT.

This file works abstractly on `C(↥I, ℝ)` for a compact real set `I`, with the (closed) span of
all dilated/translated copies of a fixed `g : ℝ → ℝ`. The univariate target of the Leshno (1993)
universal-approximation theorem, in its smooth-activation reduction, is the statement that the
closure of this span is everything (`⊤`) whenever `g` is smooth and not (everywhere) a polynomial.

* `Sg g I hg` — the `ℝ`-submodule of `C(↥I, ℝ)` spanned by `t ↦ g (λ t + b)` over all `(λ, b)`;
* `deriv_pow_mem` (B1, **leaf**) — `t ↦ tᵏ · g⁽ᵏ⁾(λ t + b)` lies in the closure of `Sg g`;
* `exists_deriv_ne` (B2) — a smooth non-polynomial has a nonzero `k`-th derivative for each `k`;
* `smooth_engine` (B3, glue) — the closed span is all of `C(↥I, ℝ)`.
-/

namespace UniversalApproximation.Leshno

open Topology IteratedDerivPolynomial

/-- The span of dilated/translated copies of `g`, inside `C(I,ℝ)` for a compact real set `I`. -/
def Sg (g : ℝ → ℝ) (I : Set ℝ) (hg : Continuous g) : Submodule ℝ C(↥I, ℝ) :=
  Submodule.span ℝ (Set.range fun lb : ℝ × ℝ =>
    (⟨fun t => g (lb.1 * (t : ℝ) + lb.2), by fun_prop⟩ : C(↥I, ℝ)))

/-- B1 (leaf). For smooth `g`, the function `t ↦ tᵏ · g⁽ᵏ⁾(λt+b)` lies in the closure of `Sg g`:
it is a uniform-on-`I` limit of iterated finite differences in `λ` of `t ↦ g(λt+b)`.

Proof strategy (reserved for a later cycle). The map `λ ↦ g(λ t + b)` is differentiable with
`∂_λ g(λ t + b) = t · g'(λ t + b)` (chain rule, `HasDerivAt`). Hence for each fixed `t` the
difference quotient `(g((λ + s) t + b) − g(λ t + b)) / s` tends to `t · g'(λ t + b)` as `s → 0`.
As a function of `t ∈ I`, the difference quotient is `s⁻¹` times a difference of two generators of
`Sg g` (the maps `t ↦ g((λ+s) t + b)` and `t ↦ g(λ t + b)`), so it lies in `Sg g`. The convergence
is *uniform* on the compact set `I`: `g'` is uniformly continuous on the compact image
`{ (λ + θ s) t + b : t ∈ I, θ ∈ [0,1] }`, which lets one bound the error uniformly. Therefore the
uniform limit `t ↦ t · g'(λ t + b)` lies in the topological closure of `Sg g`. Iterating this
argument `k` times (induction on `k`, using `iteratedDeriv_succ` to turn `g⁽ᵏ⁾` into the derivative
of `g⁽ᵏ⁻¹⁾`, and the binomial/Leibniz structure of iterated finite differences) yields the claim
`t ↦ tᵏ · g⁽ᵏ⁾(λ t + b) ∈ closure (Sg g)`. This is a genuinely analytic uniform-convergence fact
and is left as a documented `sorry` for this cycle. -/
theorem deriv_pow_mem {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g) (I : Set ℝ) (hI : IsCompact I)
    (k : ℕ) (lam b : ℝ) :
    (⟨fun t => (t : ℝ) ^ k * iteratedDeriv k g (lam * (t : ℝ) + b), by
        have := hg.continuous_iteratedDeriv k le_top; fun_prop⟩ : C(↥I, ℝ))
      ∈ (Sg g I hg.continuous).topologicalClosure := by
  sorry

/-- B2. A smooth non(everywhere-)polynomial has, for every order `k`, a point where the
`k`-th derivative is nonzero. This is the contrapositive of
`iteratedDeriv_eq_zero_imp_poly`: if `g⁽ᵏ⁾` vanished everywhere, `g` would be a polynomial. -/
theorem exists_deriv_ne {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g)
    (hnp : ¬ IsPolynomialFun g) (k : ℕ) : ∃ b, iteratedDeriv k g b ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp, _⟩ :=
    iteratedDeriv_eq_zero_imp_poly (f := g) (n := k) (hg.of_le le_top) h
  exact hnp ⟨p, funext hp⟩

/-- B3 (glue). For smooth non-polynomial `g`, the closed span of its dilations/translations is all
of `C(I,ℝ)` on every compact set `I`. -/
theorem smooth_engine {g : ℝ → ℝ} (hg : ContDiff ℝ ⊤ g) (hnp : ¬ IsPolynomialFun g)
    (I : Set ℝ) (hI : IsCompact I) :
    (Sg g I hg.continuous).topologicalClosure = ⊤ := by
  haveI : CompactSpace (↥I) := isCompact_iff_compactSpace.mp hI
  set C := (Sg g I hg.continuous).topologicalClosure with hC
  -- Step 1+2: every monomial `t ↦ tᵏ` lies in the closure `C`.
  have hmono : ∀ k : ℕ, (⟨fun t => (t : ℝ) ^ k, by fun_prop⟩ : C(↥I, ℝ)) ∈ C := by
    intro k
    obtain ⟨b, hb⟩ := exists_deriv_ne hg hnp k
    have hmem := deriv_pow_mem hg I hI k 0 b
    -- the generator `t ↦ tᵏ · g⁽ᵏ⁾(0·t+b) = (g⁽ᵏ⁾ b) • (t ↦ tᵏ)`.
    have hsmul : (⟨fun t => (t : ℝ) ^ k * iteratedDeriv k g (0 * (t : ℝ) + b), by
          have := hg.continuous_iteratedDeriv k le_top; fun_prop⟩ : C(↥I, ℝ))
        = iteratedDeriv k g b • (⟨fun t => (t : ℝ) ^ k, by fun_prop⟩ : C(↥I, ℝ)) := by
      ext t
      simp [mul_comm]
    rw [hsmul] at hmem
    have := C.smul_mem (iteratedDeriv k g b)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this
  -- Step 3: every polynomial function lies in `C` (by polynomial induction, `C` a submodule).
  have hpoly : ∀ p : Polynomial ℝ, p.toContinuousMapOn I ∈ C := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        have : (p + q).toContinuousMapOn I = p.toContinuousMapOn I + q.toContinuousMapOn I := by
          ext t; simp
        rw [this]; exact C.add_mem hp hq
    | monomial n a =>
        have : (Polynomial.monomial n a).toContinuousMapOn I
            = a • (⟨fun t => (t : ℝ) ^ n, by fun_prop⟩ : C(↥I, ℝ)) := by
          ext t; simp
        rw [this]; exact C.smul_mem a (hmono n)
  -- Step 4: polynomial functions are dense (Stone–Weierstrass); `C` is closed and contains them.
  -- It suffices that `C` (as a set) is all of `C(↥I,ℝ)`.
  rw [eq_top_iff]
  intro f _
  -- Polynomial functions are a dense subset, and `C` is a closed superset, so `C` contains `f`.
  have hSW : closure (polynomialFunctions I : Set C(↥I, ℝ)) = Set.univ := by
    have := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (polynomialFunctions I) (polynomialFunctions_separatesPoints I)
    have h2 := congrArg (fun s : Subalgebra ℝ C(↥I, ℝ) => (s : Set C(↥I, ℝ))) this
    rwa [Subalgebra.topologicalClosure_coe, Algebra.coe_top] at h2
  have hsub : (polynomialFunctions I : Set C(↥I, ℝ)) ⊆ (C : Set C(↥I, ℝ)) := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p, rfl⟩
    exact hpoly p
  have hclosed : closure (polynomialFunctions I : Set C(↥I, ℝ)) ⊆ (C : Set C(↥I, ℝ)) :=
    closure_minimal hsub (Sg g I hg.continuous).isClosed_topologicalClosure
  have : f ∈ (C : Set C(↥I, ℝ)) := hclosed (by rw [hSW]; trivial)
  exact this

end UniversalApproximation.Leshno
