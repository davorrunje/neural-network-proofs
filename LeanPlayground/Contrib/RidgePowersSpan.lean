import Mathlib

/-! # Powers of linear functionals span the homogeneous polynomials.
Intended Mathlib home: `Mathlib/LinearAlgebra/Polynomial` / `Mathlib/RingTheory/MvPolynomial`
(polarization; confirm with maintainers).

This is the polarization identity for symmetric tensors, phrased at the level of polynomial
*functions* on `Fin n → ℝ`. As of the toolchain pin (`v4.32.0-rc1`) no off-the-shelf statement
was found via `lean_leansearch`/`lean_loogle`. The closest existing material is
`MvPolynomial.homogeneousSubmodule` (the submodule of homogeneous polynomials of a given degree),
`MvPolynomial.homogeneousSubmodule_eq_finsupp_supported`, and `MvPolynomial.evalₗ`
(`MvPolynomial.evalₗ_apply : evalₗ K σ p e = eval e p`), all of which we reuse to phrase the
right-hand side; none of them give the "powers of linear forms span" statement directly, so it is
proved here from scratch (see `ridgePow_span` for the proof outline).

## Choice of right-hand side

The left-hand side is the span of the *functions* `x ↦ (∑ i, a i * x i) ^ k`, so the right-hand
side must also be a `Submodule ℝ ((Fin n → ℝ) → ℝ)`. We take it to be the image, under the
evaluation-as-a-function linear map `MvPolynomial.evalₗ ℝ (Fin n) : MvPolynomial (Fin n) ℝ →ₗ[ℝ]
(Fin n → ℝ) → ℝ`, of the canonical Mathlib submodule of homogeneous degree-`k` polynomials
`MvPolynomial.homogeneousSubmodule (Fin n) ℝ k`. -/

namespace RidgePowersSpan

open MvPolynomial

variable {n : ℕ}

/-- The linear form polynomial `∑ i, C (a i) * X i`. -/
private noncomputable def linForm (a : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, C (a i) * X i

/-- The ridge-power polynomial `(∑ i, C (a i) * X i) ^ k`. -/
private noncomputable def ridgePoly (k : ℕ) (a : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  (linForm a) ^ k

private theorem linForm_isHomogeneous (a : Fin n → ℝ) : (linForm a).IsHomogeneous 1 := by
  unfold linForm
  apply IsHomogeneous.sum
  intro i _
  simpa using isHomogeneous_C_mul_X (a i) i

private theorem ridgePoly_isHomogeneous (k : ℕ) (a : Fin n → ℝ) :
    (ridgePoly k a).IsHomogeneous k := by
  unfold ridgePoly
  simpa using (linForm_isHomogeneous a).pow k

private theorem eval_ridgePoly (k : ℕ) (a x : Fin n → ℝ) :
    eval x (ridgePoly k a) = (∑ i, a i * x i) ^ k := by
  unfold ridgePoly linForm
  simp

/-- The "diagonal scaling" algebra hom `X i ↦ C (a i) * X i`. -/
private noncomputable def scaleHom (a : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (fun i => C (a i) * X i)

/-- `scaleHom` scales the coefficient of `monomial e` by `∏ i, a i ^ e i`. -/
private theorem coeff_scaleHom (a : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (e : Fin n →₀ ℕ) :
    coeff e (scaleHom a p) = (∏ i, a i ^ e i) * coeff e p := by
  unfold scaleHom
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [aeval_monomial]
    have hprod : (d.prod fun i k => (C (a i) * X i) ^ k)
        = monomial d (∏ i, a i ^ d i) := by
      rw [Finsupp.prod]
      simp only [mul_pow, ← C_pow]
      rw [Finset.prod_mul_distrib, prod_X_pow_eq_monomial, ← map_prod, C_mul_monomial, mul_one]
      congr 1
      rw [Finset.prod_subset (Finset.subset_univ _)]
      intro x _ hx
      simp only [Finsupp.mem_support_iff, not_not] at hx
      rw [hx, pow_zero]
    rw [hprod, algebraMap_eq, C_mul_monomial, coeff_monomial, coeff_monomial]
    by_cases h : d = e
    · subst h; simp; ring
    · simp [h]
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

private theorem scaleHom_ridgePoly (k : ℕ) (a : Fin n → ℝ) :
    scaleHom a (ridgePoly k 1) = ridgePoly k a := by
  unfold scaleHom ridgePoly linForm
  rw [map_pow]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_mul, aeval_C, aeval_X]
  simp

/-- `coeff d (ridgePoly k a) = (∏ i, a i ^ d i) * coeff d (ridgePoly k 1)`. -/
private theorem coeff_ridgePoly (k : ℕ) (a : Fin n → ℝ) (d : Fin n →₀ ℕ) :
    coeff d (ridgePoly k a) = (∏ i, a i ^ d i) * coeff d (ridgePoly k 1) := by
  rw [← scaleHom_ridgePoly k a, coeff_scaleHom]

/-- The coefficient of `ridgePoly k 1` at `d` is the (nonzero) multinomial coefficient. -/
private theorem coeff_ridgePoly_one (k : ℕ) (d : Fin n →₀ ℕ) (hd : d.degree = k) :
    coeff d (ridgePoly k 1) = (Nat.multinomial Finset.univ d : ℝ) := by
  unfold ridgePoly linForm
  simp only [Pi.one_apply, map_one, one_mul]
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [← C_eq_coe_nat, MvPolynomial.coeff_C_mul, MvPolynomial.prod_X_pow, coeff_monomial]
  have hmem : (⇑d) ∈ Finset.univ.piAntidiag k := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← Finsupp.degree_eq_sum, hd]
  have hind : (Finsupp.indicator Finset.univ fun i (_ : i ∈ Finset.univ) => (⇑d) i) = d := by
    ext i; simp [Finsupp.indicator_apply]
  rw [Finset.sum_eq_single (⇑d)]
  · rw [if_pos hind, mul_one]
  · intro x _ hxd
    rw [if_neg, mul_zero]
    intro hcontra
    apply hxd
    ext i
    have := congrArg (fun (g : Fin n →₀ ℕ) => g i) hcontra
    simpa [Finsupp.indicator_apply] using this
  · intro hcontra; exact absurd hmem hcontra

/-- The polynomial-level polarization identity: the powers of linear forms span (over ℝ) the
homogeneous degree-`k` polynomials. -/
private theorem ridgePoly_span (k : ℕ) :
    Submodule.span ℝ (Set.range (ridgePoly (n := n) k))
      = MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  set W := Submodule.span ℝ (Set.range (ridgePoly (n := n) k)) with hW
  set H := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k with hH
  have hle : W ≤ H := by
    rw [hW, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ridgePoly_isHomogeneous k a
  -- It suffices to show the dual annihilators agree.
  rw [← Subspace.dualAnnihilator_inj]
  refine le_antisymm ?_ (Submodule.dualAnnihilator_anti hle)
  -- Any functional `f` annihilating all `ridgePoly k a` annihilates every degree-`k` monomial.
  intro f hf
  rw [Submodule.mem_dualAnnihilator] at hf ⊢
  -- Reduce `H` to the span of degree-`k` monomials.
  intro p hp
  rw [hH, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨d, hd, rfl⟩ := h
    simp only [Set.mem_setOf_eq] at hd
    -- `f (monomial d 1) = 0` for `d.degree = k`.
    change f (monomial d 1) = 0
    -- `T` = support of the "all-ones" ridge power; it contains every degree-`k` exponent.
    set T := (ridgePoly k (1 : Fin n → ℝ)).support with hT
    -- Every `ridgePoly k a` is supported in `T`.
    have hsupp : ∀ a : Fin n → ℝ, (ridgePoly k a).support ⊆ T := by
      intro a e he
      rw [hT, MvPolynomial.mem_support_iff]
      rw [MvPolynomial.mem_support_iff, coeff_ridgePoly] at he
      exact fun h => he (by rw [h, mul_zero])
    -- `f (ridgePoly k a)` as a finite sum over `T`.
    have hfsum : ∀ a : Fin n → ℝ,
        f (ridgePoly k a) = ∑ e ∈ T, coeff e (ridgePoly k a) * f (monomial e 1) := by
      intro a
      conv_lhs => rw [ridgePoly, ← ridgePoly, MvPolynomial.as_sum (ridgePoly k a)]
      rw [Finset.sum_subset (hsupp a)]
      · rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [show (monomial e) (coeff e (ridgePoly k a))
              = coeff e (ridgePoly k a) • monomial e 1 by
              rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
      · intro e _ he
        rw [MvPolynomial.notMem_support_iff] at he
        rw [he, map_zero]
    -- Build the polynomial in `a` whose evaluation is `f (ridgePoly k a)`.
    set P : MvPolynomial (Fin n) ℝ :=
      ∑ e ∈ T, monomial e (f (monomial e 1) * coeff e (ridgePoly k 1)) with hP
    have hevalP : ∀ a : Fin n → ℝ, eval a P = f (ridgePoly k a) := by
      intro a
      rw [hfsum a, hP, map_sum]
      refine Finset.sum_congr rfl ?_
      intro e _
      rw [MvPolynomial.eval_monomial, coeff_ridgePoly k a e,
        Finsupp.prod_fintype _ _ (fun i => pow_zero (a i))]
      ring
    -- `P` vanishes identically, hence is zero.
    have hP0 : P = 0 := by
      apply MvPolynomial.funext
      intro a
      rw [hevalP a, map_zero]
      exact hf _ (Submodule.subset_span ⟨a, rfl⟩)
    -- Read off the coefficient at `d`.
    have hdT : d ∈ T := by
      rw [hT, MvPolynomial.mem_support_iff, coeff_ridgePoly_one k d hd]
      exact_mod_cast (Nat.multinomial_pos Finset.univ d).ne'
    have hcoeff : coeff d P = f (monomial d 1) * coeff d (ridgePoly k 1) := by
      rw [hP, coeff_sum, Finset.sum_eq_single d]
      · rw [coeff_monomial, if_pos rfl]
      · intro e _ hed; rw [coeff_monomial, if_neg hed]
      · intro h; exact absurd hdT h
    rw [hP0, coeff_zero] at hcoeff
    have hne : coeff d (ridgePoly k 1) ≠ 0 := by
      rw [coeff_ridgePoly_one k d hd]
      exact_mod_cast (Nat.multinomial_pos Finset.univ d).ne'
    exact (mul_eq_zero.mp hcoeff.symm).resolve_right hne
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- The powers `x ↦ (∑ i, a i * x i) ^ k`, ranging over `a : Fin n → ℝ`, span (over ℝ) the space
of homogeneous polynomial functions of degree `k` on `Fin n → ℝ` (polarization of symmetric
tensors). Needed for the Leshno ridge-function step; cf. Leshno et al. 1993 / Pinkus, Acta
Numerica 1999, Thm 3.1.

The right-hand side is the image of `MvPolynomial.homogeneousSubmodule (Fin n) ℝ k` under the
evaluation linear map `MvPolynomial.evalₗ ℝ (Fin n)`; see the file docstring for the rationale.

Proof: the statement is transported (via `Submodule.map_span` and `evalₗ`) from the polynomial-
level identity `ridgePoly_span`, which says that the powers `(∑ i, C (a i) * X i) ^ k` span
`homogeneousSubmodule k` in `MvPolynomial (Fin n) ℝ`. The easy inclusion uses
`IsHomogeneous.{sum,pow}`; the hard inclusion is the polarization/duality argument: a functional
annihilating every power gives, via `MvPolynomial.funext` over the infinite field ℝ, a polynomial
in `a` that vanishes identically, forcing each monomial coefficient (a nonzero multinomial,
`Nat.multinomial_pos`) times the functional's value to be zero — so the functional annihilates
every degree-`k` monomial. Equality of dual annihilators then gives the inclusion via
`Subspace.dualAnnihilator_inj`. -/
theorem ridgePow_span (k : ℕ) :
    Submodule.span ℝ
        (Set.range fun a : Fin n → ℝ =>
          (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k))
      = Submodule.map (MvPolynomial.evalₗ ℝ (Fin n))
          (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) := by
  rw [← ridgePoly_span k, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; rw [evalₗ_apply]; exact eval_ridgePoly k a x⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; rw [evalₗ_apply]; exact (eval_ridgePoly k a x).symm⟩

end RidgePowersSpan
