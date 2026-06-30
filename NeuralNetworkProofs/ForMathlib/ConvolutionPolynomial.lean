/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Convolution of polynomials with test functions, and commutativity for the `mul` pairing.

Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/


namespace ConvolutionPolynomial

open MeasureTheory

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

-- ---------------------------------------------------------------------------
-- Private supporting lemmas
-- ---------------------------------------------------------------------------

/-- A continuous function times a continuous compactly-supported function is integrable. -/
private lemma integrable_mul_of_compactSupport {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun y => g y * ψ y) volume :=
  (hg.mul hψ).integrable_of_hasCompactSupport hψc.mul_left

/-- Pointwise expansion of `(x - y)^n * ψ y` as a finite sum via `sub_pow`. -/
private lemma monomial_conv_expand (n : ℕ) (x y : ℝ) (ψ : ℝ → ℝ) :
    (x - y) ^ n * ψ y =
      ∑ m ∈ Finset.range (n + 1),
        (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
  rw [sub_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- Each summand `x^m * ((-1)^(m+n) * y^(n-m) * C(n,m)) * ψ y` is integrable in `y`. -/
private lemma monomial_conv_summand_integrable {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (n : ℕ) (x : ℝ) (m : ℕ) :
    Integrable
      (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
      volume := by
  have hrw : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
      = fun y => (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
    funext y; ring
  rw [hrw]
  exact integrable_mul_of_compactSupport hψ hψc _ (by fun_prop)

/-- The m-th coefficient `c m = ∫ y, ((-1)^(m+n) * y^(n-m) * C(n,m)) * ψ y`. -/
private noncomputable def monomialConvCoeff (ψ : ℝ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun m => ∫ y, ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y

/-- Pulling the constant `x^m` out of the integral for coefficient `c m`. -/
private lemma monomial_conv_integral_eq (n : ℕ) (x : ℝ) (m : ℕ) (ψ : ℝ → ℝ) :
    ∫ y, x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y
      = x ^ m * monomialConvCoeff ψ n m := by
  have hrw : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
      = fun y => x ^ m * (((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y) := by
    funext y; ring
  rw [hrw, MeasureTheory.integral_const_mul]
  simp [monomialConvCoeff]

/-- The `n`-th coefficient of `monomialConvCoeff ψ n` equals `∫ ψ`. -/
private lemma monomialConvCoeff_top {ψ : ℝ → ℝ} (n : ℕ) :
    monomialConvCoeff ψ n n = ∫ y, ψ y := by
  simp only [monomialConvCoeff, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have : (-1 : ℝ) ^ (n + n) = 1 := (Even.add_self n).neg_one_pow
  rw [this]; ring

/-- Each monomial in the assembled polynomial has degree `≤ n`. -/
private lemma monomial_conv_poly_deg_le (n m : ℕ) (c : ℕ → ℝ)
    (hm : m ∈ Finset.range (n + 1)) :
    (Polynomial.monomial m (c m)).natDegree ≤ n :=
  (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hm))

/-- For `poly_conv_isPoly`: each smul-monomial piece has degree `≤ p.natDegree`. -/
private lemma poly_conv_piece_deg_le {p : Polynomial ℝ} (qf : ℕ → Polynomial ℝ)
    (hqfd : ∀ k, (qf k).natDegree ≤ k) (k : ℕ)
    (hk : k ∈ Finset.range (p.natDegree + 1)) :
    (p.coeff k • qf k).natDegree ≤ p.natDegree :=
  (Polynomial.natDegree_smul_le _ _).trans
    ((hqfd k).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- For `poly_conv_isPoly`: summands for `k < p.natDegree` have zero coefficient at the top. -/
private lemma poly_conv_off_diag_coeff_zero {p : Polynomial ℝ} (qf : ℕ → Polynomial ℝ)
    (hqfd : ∀ k, (qf k).natDegree ≤ k) (k : ℕ)
    (hk : k ∈ Finset.range (p.natDegree + 1)) (hkn : k ≠ p.natDegree) :
    (p.coeff k • qf k).coeff p.natDegree = 0 := by
  rw [Polynomial.coeff_smul, smul_eq_mul]
  have hlt : (qf k).natDegree < p.natDegree :=
    lt_of_le_of_lt (hqfd k)
      (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkn)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

/-- Integrability of `p.coeff k * (x - y)^k * ψ y` in `y`. -/
private lemma poly_conv_summand_integrable {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (p : Polynomial ℝ) (x : ℝ) (k : ℕ) :
    Integrable (fun y => p.coeff k * (x - y) ^ k * ψ y) volume := by
  have hrw : (fun y => p.coeff k * (x - y) ^ k * ψ y)
      = fun y => (p.coeff k * (x - y) ^ k) * ψ y := by funext y; ring
  rw [hrw]
  exact integrable_mul_of_compactSupport hψ hψc _ (by fun_prop)

-- ---------------------------------------------------------------------------
-- Main theorems
-- ---------------------------------------------------------------------------

/-- Convolving the monomial `x ↦ xⁿ` with a continuous compactly-supported `ψ` gives a polynomial
of degree `≤ n` whose `n`-th coefficient is the `0`-th moment `∫ ψ`. -/
theorem monomial_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (n : ℕ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, (x - y) ^ n * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ n ∧ q.coeff n = ∫ y, ψ y := by
  set c := monomialConvCoeff ψ n with hc_def
  refine ⟨∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (c m), ?_, ?_, ?_⟩
  · -- the convolution equals the polynomial's evaluation
    funext x
    have hsum : (fun y => (x - y) ^ n * ψ y)
        = fun y => ∑ m ∈ Finset.range (n + 1),
            (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y :=
      funext (fun y => monomial_conv_expand n x y ψ)
    rw [hsum, MeasureTheory.integral_finsetSum]
    · simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [monomial_conv_integral_eq n x m ψ, mul_comm (x ^ m) (c m)]
    · intro m _
      exact monomial_conv_summand_integrable hψ hψc n x m
  · -- degree bound: each monomial has degree ≤ n
    exact Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun m hm => monomial_conv_poly_deg_le n m c hm)
  · -- the n-th coefficient picks out the m = n term
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
      exact monomialConvCoeff_top n
    · intro m hm hmn
      rw [Polynomial.coeff_monomial, if_neg hmn]
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

/-- Convolving a polynomial `p` (as a function) with a continuous compactly-supported `ψ` gives a
polynomial of `natDegree ≤ p.natDegree`, whose `p.natDegree`-th coefficient is
`p.leadingCoeff * ∫ ψ`. -/
theorem poly_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, p.eval (x - y) * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ p.natDegree ∧ q.coeff p.natDegree = p.leadingCoeff * ∫ y, ψ y := by
  -- for each `k`, monomial_conv_isPoly gives `q_k` representing `∫ (x-y)^k ψ`
  choose qf hqf hqfd hqfc using fun k : ℕ => monomial_conv_isPoly hψ hψc k
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • qf k, ?_, ?_, ?_⟩
  · -- the convolution equals the evaluation of `q`
    funext x
    have hsum : (fun y => p.eval (x - y) * ψ y)
        = fun y => ∑ k ∈ Finset.range (p.natDegree + 1),
            (p.coeff k * (x - y) ^ k) * ψ y := by
      funext y
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    rw [hsum, MeasureTheory.integral_finsetSum]
    · simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hre : (fun y => p.coeff k * (x - y) ^ k * ψ y)
          = fun y => p.coeff k * ((x - y) ^ k * ψ y) := by funext y; ring
      rw [hre, MeasureTheory.integral_const_mul, congrFun (hqf k) x]
    · intro k _
      exact poly_conv_summand_integrable hψ hψc p x k
  · -- degree bound
    exact Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun k hk => poly_conv_piece_deg_le qf hqfd k hk)
  · -- top coefficient: only k = p.natDegree contributes
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single p.natDegree]
    · rw [Polynomial.coeff_smul, smul_eq_mul, hqfc, Polynomial.coeff_natDegree]
    · intro k hk hkn
      exact poly_conv_off_diag_coeff_zero qf hqfd k hk hkn
    · intro hn
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self p.natDegree)) hn

/-- When `∫ ψ ≠ 0`, the convolution of a polynomial `p` with `ψ` preserves the degree exactly. -/
theorem natDegree_poly_conv_eq {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (p : Polynomial ℝ) (hmom : (∫ y, ψ y) ≠ 0) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, p.eval (x - y) * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with hp | hp
  · -- `p = 0`: the convolution is the zero function, represented by the zero polynomial
    refine ⟨0, ?_, by simp [hp]⟩
    subst hp
    funext x
    simp
  · -- `p ≠ 0`: reuse `poly_conv_isPoly`; the top coefficient is nonzero, forcing equality
    obtain ⟨q, hq, hqle, hqc⟩ := poly_conv_isPoly hψ hψc p
    refine ⟨q, hq, le_antisymm hqle ?_⟩
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hqc]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) hmom

end ConvolutionPolynomial
