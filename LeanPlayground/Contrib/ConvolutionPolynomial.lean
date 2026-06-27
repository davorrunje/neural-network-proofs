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

/-- Convolving the monomial `x ↦ xⁿ` with a continuous compactly-supported `ψ` gives a polynomial
of degree `≤ n` whose `n`-th coefficient is the `0`-th moment `∫ ψ`. -/
theorem monomial_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (n : ℕ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, (x - y) ^ n * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ n ∧ q.coeff n = ∫ y, ψ y := by
  -- integrability of `(continuous g) * ψ`, used for each summand of `sub_pow`
  have hint : ∀ (g : ℝ → ℝ), Continuous g → Integrable (fun y => g y * ψ y) volume :=
    fun g hg => (hg.mul hψ).integrable_of_hasCompactSupport (hψc.mul_left)
  -- the `m`-th coefficient: `∫ y, ((-1)^(m+n) * y^(n-m) * (n.choose m)) * ψ y`
  set c : ℕ → ℝ := fun m =>
    ∫ y, ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y with hc
  refine ⟨∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (c m), ?_, ?_, ?_⟩
  · -- the convolution equals `∑ m, c m * x^m`, which is the polynomial's evaluation
    funext x
    have hsum : (fun y => (x - y) ^ n * ψ y)
        = fun y => ∑ m ∈ Finset.range (n + 1),
            (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
      funext y
      rw [sub_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hsum]
    rw [MeasureTheory.integral_finsetSum]
    · simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have hre : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
          = fun y => x ^ m * (((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y) := by
        funext y; ring
      rw [hre, MeasureTheory.integral_const_mul, mul_comm (x ^ m) (c m), hc]
    · intro m _
      have : (fun y => x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ)) * ψ y)
          = fun y => (x ^ m * ((-1 : ℝ) ^ (m + n) * y ^ (n - m) * (n.choose m : ℝ))) * ψ y := by
        funext y; ring
      rw [this]
      exact hint _ (by fun_prop)
  · -- degree bound: each monomial has degree `≤ m ≤ n`
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
    refine (Polynomial.natDegree_monomial_le _).trans ?_
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  · -- the `n`-th coefficient picks out the `m = n` term: `c n = ∫ ψ`
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl, hc]
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      have : (-1 : ℝ) ^ (n + n) = 1 := (Even.add_self n).neg_one_pow
      rw [this]; ring
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
  -- integrability of `(continuous g) * ψ`
  have hint : ∀ (g : ℝ → ℝ), Continuous g → Integrable (fun y => g y * ψ y) volume :=
    fun g hg => (hg.mul hψ).integrable_of_hasCompactSupport (hψc.mul_left)
  -- for each `k`, Task 2 gives a polynomial `q_k` representing `∫ (x-y)^k ψ`
  choose qf hqf hqfd hqfc using fun k : ℕ => monomial_conv_isPoly hψ hψc k
  -- assemble `q := ∑ k, p.coeff k • q_k`
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • qf k, ?_, ?_, ?_⟩
  · -- the convolution equals the evaluation of `q`
    funext x
    -- expand `p.eval (x - y)` as a sum of monomials and integrate term-by-term
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
      rw [hre, MeasureTheory.integral_const_mul]
      have := congrFun (hqf k) x
      rw [this]
    · intro k _
      have : (fun y => p.coeff k * (x - y) ^ k * ψ y)
          = fun y => (p.coeff k * (x - y) ^ k) * ψ y := by funext y; ring
      rw [this]
      exact hint _ (by fun_prop)
  · -- degree bound
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
    refine (Polynomial.natDegree_smul_le _ _).trans ?_
    exact (hqfd k).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · -- top coefficient: only `k = p.natDegree` contributes
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single p.natDegree]
    · rw [Polynomial.coeff_smul, smul_eq_mul, hqfc, Polynomial.coeff_natDegree]
    · intro k hk hkn
      rw [Polynomial.coeff_smul, smul_eq_mul]
      have hlt : (qf k).natDegree < p.natDegree :=
        lt_of_le_of_lt (hqfd k) (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkn)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
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
