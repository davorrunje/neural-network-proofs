import Mathlib
import NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial
import NeuralNetworkProofs.ForMathlib.SmoothCompactAntideriv

/-! # Distributional characterization of polynomials (degree ≤ d).
Intended Mathlib home: `Mathlib/Analysis/Distribution/…` (confirm with maintainers). -/

namespace PolynomialDistribution

open MeasureTheory

open scoped ContDiff

/-- Abstract factorization: if a functional `L` vanishes on `ker T`, it factors through `T`. -/
private lemma exists_factor {W : Type*} [AddCommGroup W] [Module ℝ W]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] W) (L : V →ₗ[ℝ] ℝ) (h : LinearMap.ker T ≤ LinearMap.ker L) :
    ∃ ℓ : W →ₗ[ℝ] ℝ, ∀ v, L v = ℓ (T v) := by
  -- The functional `L` descends to the quotient `V ⧸ ker T`.
  set Lq : (V ⧸ LinearMap.ker T) →ₗ[ℝ] ℝ := (LinearMap.ker T).liftQ L h with hLq
  -- The map `T` descends to an injective map `Tq` from the quotient into `W`.
  set Tq : (V ⧸ LinearMap.ker T) →ₗ[ℝ] W := (LinearMap.ker T).liftQ T (le_refl _) with hTq
  have hTq_inj : Function.Injective Tq := by
    rw [← LinearMap.ker_eq_bot]
    exact (LinearMap.ker T).ker_liftQ_eq_bot' T rfl
  -- View `Tq` as an isomorphism onto its range, giving a functional on that submodule.
  let e : (V ⧸ LinearMap.ker T) ≃ₗ[ℝ] ↥(LinearMap.range Tq) :=
    LinearEquiv.ofInjective Tq hTq_inj
  let φ : ↥(LinearMap.range Tq) →ₗ[ℝ] ℝ :=
    Lq ∘ₗ (e.symm : ↥(LinearMap.range Tq) →ₗ[ℝ] _)
  -- Extend the functional along the submodule inclusion to all of `W`.
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend φ
  refine ⟨ℓ, fun v => ?_⟩
  have hmem : Tq ((LinearMap.ker T).mkQ v) ∈ LinearMap.range Tq := LinearMap.mem_range_self _ _
  have hev : e ((LinearMap.ker T).mkQ v) = ⟨Tq ((LinearMap.ker T).mkQ v), hmem⟩ := by
    apply Subtype.ext; simp [e, LinearEquiv.ofInjective_apply]
  have h1 : Lq ((LinearMap.ker T).mkQ v) = L v := (LinearMap.ker T).liftQ_apply L v
  have h2 : Tq ((LinearMap.ker T).mkQ v) = T v := (LinearMap.ker T).liftQ_apply T v
  have hφ : φ ⟨Tq ((LinearMap.ker T).mkQ v), hmem⟩ = L v := by
    simp only [φ, LinearMap.comp_apply, ← hev, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, h1]
  have hℓφ := DFunLike.congr_fun hℓ
    (⟨Tq ((LinearMap.ker T).mkQ v), hmem⟩ : ↥(LinearMap.range Tq))
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hℓφ
  rw [← h2, ← hφ, ← hℓφ]

/-- The `ℝ`-submodule of `C^∞` compactly-supported test functions `ℝ → ℝ`. -/
private def testSpace : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | ContDiff ℝ ∞ g ∧ HasCompactSupport g}
  add_mem' := fun hg hg' => ⟨hg.1.add hg'.1, hg.2.add hg'.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hg => ⟨hg.1.const_smul c, hg.2.smul_left⟩

/-- For a `C^∞` compactly-supported `g`, the monomial-weighted `y ^ k * g y` is integrable. -/
private lemma integrable_pow_mul {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (k : ℕ) : Integrable (fun y => y ^ k * g y) volume := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_pow k).mul hg.continuous
  · exact (hgc.mul_left (f := fun y : ℝ => y ^ k))

theorem aePolynomial_of_annihilates_moment_vanishing {f : ℝ → ℝ} (d : ℕ)
    (hf : LocallyIntegrable f volume)
    (hann : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∀ j ≤ d, ∫ y, (y ^ j) * g y = 0) → ∫ y, g y * f y = 0) :
    ∃ p : Polynomial ℝ, f =ᵐ[volume] fun t => p.eval t := by
  -- The moment map `M` sending a test function to its first `d+1` moments.
  let M : testSpace →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  { toFun := fun g k => ∫ y, y ^ (k : ℕ) * (g : ℝ → ℝ) y
    map_add' := fun g g' => by
      funext k
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add (integrable_pow_mul g.2.1 g.2.2 k) (integrable_pow_mul g'.2.1 g'.2.2 k)]
      congr 1; funext y; ring
    map_smul' := fun c g => by
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
      rw [← integral_const_mul]
      congr 1; funext y; ring }
  -- The annihilation functional `L g = ∫ g · f`.
  let L : testSpace →ₗ[ℝ] ℝ :=
  { toFun := fun g => ∫ y, (g : ℝ → ℝ) y * f y
    map_add' := fun g g' => by
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add]
      · congr 1; funext y; ring
      · exact (hf.integrable_smul_left_of_hasCompactSupport g.2.1.continuous g.2.2)
      · exact (hf.integrable_smul_left_of_hasCompactSupport g'.2.1.continuous g'.2.2)
    map_smul' := fun c g => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1; funext y; ring }
  -- `ker M ⊆ ker L`, since vanishing moments imply annihilation by hypothesis.
  have hker : LinearMap.ker M ≤ LinearMap.ker L := by
    intro g hg
    simp only [LinearMap.mem_ker] at hg ⊢
    apply hann (g : ℝ → ℝ) g.2.1 g.2.2
    intro j hj
    have := congrFun hg ⟨j, by omega⟩
    exact this
  -- Factor `L` through `M`, obtaining the polynomial coefficients.
  obtain ⟨ℓ, hℓ⟩ := exists_factor M L hker
  set c : Fin (d + 1) → ℝ := fun k => ℓ (Pi.single k 1) with hc
  have hℓsum : ∀ w : Fin (d + 1) → ℝ, ℓ w = ∑ k, w k * c k := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show Pi.single k (w k) = w k • Pi.single k (1 : ℝ) by
      rw [← Pi.single_smul]; simp, map_smul]
    simp [hc]
  -- Hence: for every test function, `∫ g·f = ∑ k, (∫ y^k g) · c k`.
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ y, g y * f y = ∑ k : Fin (d + 1), (∫ y, y ^ (k : ℕ) * g y) * c k := by
    intro g hg hgc
    have hmem : g ∈ testSpace := ⟨hg, hgc⟩
    have hLg : L ⟨g, hmem⟩ = ∫ y, g y * f y := rfl
    rw [← hLg, hℓ ⟨g, hmem⟩, hℓsum]
    rfl
  -- The candidate polynomial.
  set p : Polynomial ℝ :=
    ∑ k : Fin (d + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ) with hp
  have hpeval : ∀ y : ℝ, p.eval y = ∑ k : Fin (d + 1), c k * y ^ (k : ℕ) := by
    intro y
    simp [hp, Polynomial.eval_finsetSum]
  refine ⟨p, ?_⟩
  have hf' : LocallyIntegrable (fun t => p.eval t) volume := (p.continuous).locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq hf hf'
  intro g hg hgc
  -- `ContDiff ℝ ∞` vs the `(↑⊤)` shape in the lemma statement.
  have hg' : ContDiff ℝ ∞ g := hg
  simp only [smul_eq_mul]
  -- RHS: `∫ g · p.eval = ∑ k, c k * ∫ y^k g`.
  have hrhs : ∫ y, g y * p.eval y = ∑ k : Fin (d + 1), c k * ∫ y, y ^ (k : ℕ) * g y := by
    calc ∫ y, g y * p.eval y
        = ∫ y, ∑ k : Fin (d + 1), c k * (y ^ (k : ℕ) * g y) := by
          congr 1; funext y; rw [hpeval]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
          intro k _; ring
      _ = ∑ k : Fin (d + 1), ∫ y, c k * (y ^ (k : ℕ) * g y) := by
          rw [MeasureTheory.integral_finsetSum]
          intro k _
          exact (integrable_pow_mul hg' hgc k).const_mul (c k)
      _ = ∑ k : Fin (d + 1), c k * ∫ y, y ^ (k : ℕ) * g y := by
          apply Finset.sum_congr rfl; intro k _; rw [integral_const_mul]
  rw [hrhs, key g hg' hgc]
  apply Finset.sum_congr rfl
  intro k _; rw [mul_comm]

end PolynomialDistribution
