import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family

/-! # Converse direction of Leshno UAT: a.e.-polynomial activation is not dense.

If `σ` agrees Lebesgue-a.e. with a polynomial `p` of degree `d`, then on `K = [0,1] ⊆ ℝ¹` every
generator `x ↦ σ(⟪w,x⟫+b)` agrees a.e. (in the coordinate `t`) with a polynomial of degree `≤ d`,
hence so does every `g ∈ genSpan σ K`. A continuous test function whose coordinate profile is
`t ↦ t^(d+1)` cannot be uniformly approximated by such, because the space of degree-`≤ d`
polynomial functions on `[0,1]` is finite-dimensional (hence closed) and the monomial `t^(d+1)`
restricted to the infinite set `[0,1]` is not in it. -/

namespace UniversalApproximation.Leshno

open MeasureTheory
open scoped RealInnerProductSpace

/-- Coordinate embedding `ℝ → ℝ¹`. -/
noncomputable def cvec (t : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => t)

theorem continuous_cvec : Continuous cvec := by unfold cvec; fun_prop

@[simp] theorem cvec_apply (t : ℝ) : (cvec t) 0 = t := by simp [cvec]

/-- The unit interval as a subtype/domain for continuous functions. -/
abbrev II : Set ℝ := Set.Icc (0 : ℝ) 1

/-- Restriction of a polynomial to a continuous function on `[0,1]`, as a linear map. -/
noncomputable def restrictLM : Polynomial ℝ →ₗ[ℝ] C(↥II, ℝ) where
  toFun p := ⟨fun t => p.eval (t : ℝ), by fun_prop⟩
  map_add' p q := by ext t; simp
  map_smul' c p := by ext t; simp

@[simp] theorem restrictLM_apply (p : Polynomial ℝ) (t : ↥II) :
    (restrictLM p) t = p.eval (t : ℝ) := rfl

/-- The space of polynomial functions of degree `≤ d` on `[0,1]`. -/
noncomputable def Pd (d : ℕ) : Submodule ℝ C(↥II, ℝ) :=
  (Polynomial.degreeLE ℝ d).map restrictLM

instance (d : ℕ) : FiniteDimensional ℝ (Pd d) := by
  have : FiniteDimensional ℝ (Polynomial.degreeLE ℝ d) := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    infer_instance
  exact FiniteDimensional.instSubtypeMemSubmoduleMap ℝ restrictLM (Polynomial.degreeLE ℝ d)

theorem Pd_isClosed (d : ℕ) : IsClosed (Pd d : Set C(↥II, ℝ)) :=
  Submodule.closed_of_finiteDimensional _

/-- A polynomial of degree `≤ d`, restricted to `[0,1]`, lies in `Pd d`. -/
theorem restrictLM_mem_Pd {d : ℕ} {q : Polynomial ℝ} (hq : q.degree ≤ d) :
    restrictLM q ∈ Pd d :=
  Submodule.mem_map.mpr ⟨q, Polynomial.mem_degreeLE.mpr hq, rfl⟩

/-- The monomial `t^(d+1)` restricted to `[0,1]` is NOT a degree-`≤ d` polynomial function. -/
theorem monomial_notMem_Pd (d : ℕ) : restrictLM (Polynomial.X ^ (d + 1)) ∉ Pd d := by
  rintro hmem
  obtain ⟨q, hq, hqeq⟩ := Submodule.mem_map.mp hmem
  rw [Polynomial.mem_degreeLE] at hq
  -- `q` and `X^(d+1)` agree on the infinite set `[0,1]`, hence are equal as polynomials.
  have hinf : {x | Polynomial.eval x q = Polynomial.eval x (Polynomial.X ^ (d + 1))}.Infinite := by
    apply Set.Infinite.mono _ (Set.Icc_infinite (by norm_num : (0:ℝ) < 1))
    intro t ht
    have := congrFun (congrArg (fun f : C(↥II, ℝ) => (f : ↥II → ℝ)) hqeq) ⟨t, ht⟩
    simpa [restrictLM] using this
  have : q = Polynomial.X ^ (d + 1) := Polynomial.eq_of_infinite_eval_eq _ _ hinf
  rw [this, Polynomial.degree_X_pow] at hq
  have hlt : (d : WithBot ℕ) < (d : WithBot ℕ) + 1 := by
    exact_mod_cast (Nat.lt_succ_self d)
  exact absurd hq hlt.not_ge

/-- The affine map `t ↦ a*t+b` (with `a ≠ 0`) is quasi measure preserving for Lebesgue measure. -/
theorem quasiMeasurePreserving_affine {a b : ℝ} (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => a * t + b) volume volume := by
  have hmul : Measure.QuasiMeasurePreserving (fun t : ℝ => a * t) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Real.map_volume_mul_left ha]
    exact Measure.smul_absolutelyContinuous
  have hadd : Measure.QuasiMeasurePreserving (fun t : ℝ => t + b) volume volume :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving
  have hcomp := hadd.comp hmul
  have : (fun t : ℝ => t + b) ∘ (fun t : ℝ => a * t) = (fun t : ℝ => a * t + b) := by
    ext t; simp
  rwa [this] at hcomp

/-- Given `σ =ᵐ p.eval`, the rescaled function `t ↦ σ(a*t+b)` agrees a.e. with a polynomial of
degree `≤ p.natDegree` (in fact `p.comp (a•X + b)`). Handles `a = 0` (constant) too. -/
theorem aeEq_poly_of_affine {σ : ℝ → ℝ} {p : Polynomial ℝ} (hp : σ =ᵐ[volume] fun t => p.eval t)
    (a b : ℝ) :
    ∃ q : Polynomial ℝ, q.degree ≤ (p.natDegree : WithBot ℕ) ∧
      (fun t : ℝ => σ (a * t + b)) =ᵐ[volume] fun t => q.eval t := by
  rcases eq_or_ne a 0 with ha | ha
  · -- `a = 0`: `σ b` is constant; use the constant polynomial `C (σ b)`.
    refine ⟨Polynomial.C (σ b), le_trans Polynomial.degree_C_le (by positivity), ?_⟩
    filter_upwards with t
    simp [ha]
  · -- `a ≠ 0`: compose `σ =ᵐ p.eval` with the affine map.
    set L : Polynomial ℝ := Polynomial.C a * Polynomial.X + Polynomial.C b with hL
    refine ⟨p.comp L, ?_, ?_⟩
    · -- degree of comp ≤ natDegree p, via natDegree
      have hLnat : L.natDegree ≤ 1 := by
        rw [hL]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (Polynomial.natDegree_C_mul_le a Polynomial.X)
            (by simp [Polynomial.natDegree_X])
        · simp [Polynomial.natDegree_C]
      have hnat : (p.comp L).natDegree ≤ p.natDegree := by
        refine le_trans Polynomial.natDegree_comp_le ?_
        calc p.natDegree * L.natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hLnat
          _ = p.natDegree := mul_one _
      calc (p.comp L).degree ≤ ((p.comp L).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ (p.natDegree : WithBot ℕ) := by exact_mod_cast hnat
    · have hae := (quasiMeasurePreserving_affine (a := a) (b := b) ha).ae_eq_comp hp
      have hcomp2 : (fun t => p.eval t) ∘ (fun t : ℝ => a * t + b)
          = fun t : ℝ => (p.comp L).eval t := by
        ext t; simp [hL, Polynomial.eval_comp]
      change σ ∘ (fun t : ℝ => a * t + b) =ᵐ[volume] _
      rw [hcomp2] at hae
      exact hae

/-- The compact set `K = cvec '' [0,1] ⊆ ℝ¹`. -/
noncomputable def Kset : Set (EuclideanSpace ℝ (Fin 1)) := cvec '' II

theorem isCompact_Kset : IsCompact Kset :=
  (isCompact_Icc).image continuous_cvec

theorem cvec_mem_Kset {t : ℝ} (ht : t ∈ II) : cvec t ∈ Kset := ⟨t, ht, rfl⟩

/-- Predicate: a function on `K` agrees a.e. on `[0,1]` (in the coordinate `t`) with a polynomial
of degree `≤ d`. The membership proof is universally quantified so the predicate is closed under
`+` and `•`. -/
def AEPolyOn (d : ℕ) (h : ↥Kset → ℝ) : Prop :=
  ∃ q : Polynomial ℝ, q.degree ≤ (d : WithBot ℕ) ∧
    ∀ᵐ t ∂(volume.restrict II), ∀ ht : cvec t ∈ Kset, h ⟨cvec t, ht⟩ = q.eval t

theorem aePolyOn_zero (d : ℕ) : AEPolyOn d (0 : ↥Kset → ℝ) := by
  refine ⟨0, by simp, ?_⟩
  filter_upwards with t ht
  simp

theorem AEPolyOn.add {d : ℕ} {h₁ h₂ : ↥Kset → ℝ} (H₁ : AEPolyOn d h₁) (H₂ : AEPolyOn d h₂) :
    AEPolyOn d (h₁ + h₂) := by
  obtain ⟨q₁, hq₁, hae₁⟩ := H₁
  obtain ⟨q₂, hq₂, hae₂⟩ := H₂
  refine ⟨q₁ + q₂, le_trans (Polynomial.degree_add_le _ _) (max_le hq₁ hq₂), ?_⟩
  filter_upwards [hae₁, hae₂] with t h1 h2 ht
  simp only [Pi.add_apply, Polynomial.eval_add]
  rw [h1 ht, h2 ht]

theorem AEPolyOn.smul {d : ℕ} (c : ℝ) {h : ↥Kset → ℝ} (H : AEPolyOn d h) :
    AEPolyOn d (c • h) := by
  obtain ⟨q, hq, hae⟩ := H
  refine ⟨c • q, le_trans (Polynomial.degree_smul_le _ _) hq, ?_⟩
  filter_upwards [hae] with t h1 ht
  simp only [Pi.smul_apply, smul_eq_mul, Polynomial.eval_smul]
  rw [h1 ht]

/-- Each generator satisfies `AEPolyOn d` for `d = p.natDegree`. -/
theorem aePolyOn_genFun {σ : ℝ → ℝ} {p : Polynomial ℝ}
    (hp : σ =ᵐ[volume] fun t => p.eval t) (w : EuclideanSpace ℝ (Fin 1)) (b : ℝ) :
    AEPolyOn p.natDegree (genFun σ (K := Kset) w b) := by
  obtain ⟨q, hqdeg, hqae⟩ := aeEq_poly_of_affine hp (w 0) b
  refine ⟨q, hqdeg, ?_⟩
  -- restrict the a.e. equality on ℝ to `II`
  have hrestrict := ae_restrict_of_ae hqae (s := II)
  filter_upwards [hrestrict] with t hqt ht
  -- `genFun σ w b ⟨cvec t, ht⟩ = σ (w 0 * t + b)`
  have : genFun σ (K := Kset) w b ⟨cvec t, ht⟩ = σ (w 0 * t + b) := by
    simp only [genFun]
    congr 1
    rw [PiLp.inner_apply]
    simp [mul_comm]
  rw [this]
  exact hqt

/-- Every `g ∈ genSpan σ Kset` satisfies `AEPolyOn p.natDegree`. -/
theorem aePolyOn_of_mem_genSpan {σ : ℝ → ℝ} {p : Polynomial ℝ}
    (hp : σ =ᵐ[volume] fun t => p.eval t) {g : ↥Kset → ℝ} (hg : g ∈ genSpan σ Kset) :
    AEPolyOn p.natDegree g := by
  refine Submodule.span_induction ?_ (aePolyOn_zero _) ?_ ?_ hg
  · rintro f ⟨wb, rfl⟩
    exact aePolyOn_genFun hp wb.1 wb.2
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro a x _ hx
    exact hx.smul a

/-- a.e.-to-everywhere bridge: a closed set with full measure inside `[0,1]` contains all of
`[0,1]`. -/
theorem subset_of_ae_restrict_mem {S : Set ℝ} (hS : IsClosed S)
    (hae : ∀ᵐ t ∂(volume.restrict II), t ∈ S) : II ⊆ S := by
  -- The complement is null on `[0,1]`.
  have hnull : volume (Sᶜ ∩ II) = 0 := by
    rw [← Measure.restrict_apply hS.measurableSet.compl]
    exact hae
  intro t₀ ht₀
  by_contra hmem
  -- `Sᶜ` is an open neighbourhood of `t₀`; intersect with `Ioo 0 1`.
  have hopen : IsOpen (Sᶜ ∩ Set.Ioo (0:ℝ) 1) := hS.isOpen_compl.inter isOpen_Ioo
  have hsub : Sᶜ ∩ Set.Ioo (0:ℝ) 1 ⊆ Sᶜ ∩ II :=
    Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
  -- It is nonempty: `t₀ ∈ Sᶜ` and `t₀ ∈ closure (Ioo 0 1) = Icc 0 1`.
  have hne : (Sᶜ ∩ Set.Ioo (0:ℝ) 1).Nonempty := by
    have ht₀cl : t₀ ∈ closure (Set.Ioo (0:ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]; exact ht₀
    rw [mem_closure_iff] at ht₀cl
    exact ht₀cl Sᶜ hS.isOpen_compl hmem
  have hpos : 0 < volume (Sᶜ ∩ Set.Ioo (0:ℝ) 1) := hopen.measure_pos volume hne
  have : 0 < volume (Sᶜ ∩ II) := lt_of_lt_of_le hpos (measure_mono hsub)
  rw [hnull] at this
  exact lt_irrefl 0 this

/-- **Converse direction of the Leshno UAT.** If `σ` agrees Lebesgue-a.e. with a polynomial, then
`σ` does not densely approximate. -/
theorem aePolynomial_not_dense {σ : ℝ → ℝ} (hp : IsAEPolynomial σ) : ¬ DenselyApproximates σ := by
  obtain ⟨p, hp⟩ := hp
  set d := p.natDegree with hd
  intro hdense
  haveI : CompactSpace (↥II) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- Test function on `K`: `x ↦ (x 0)^(d+1)`.
  set f : C(↥Kset, ℝ) := ⟨fun x => ((x : EuclideanSpace ℝ (Fin 1)) 0) ^ (d + 1), by fun_prop⟩
    with hf
  -- The target monomial restricted to `[0,1]` and its positive distance to `Pd d`.
  set F₀ : C(↥II, ℝ) := restrictLM (Polynomial.X ^ (d + 1)) with hF₀
  have hδ : 0 < Metric.infDist F₀ (Pd d : Set C(↥II, ℝ)) := by
    rw [← Metric.infDist_pos_iff_notMem_closure ⟨0, (Pd d).zero_mem⟩,
      (Pd_isClosed d).closure_eq] at *
    exact monomial_notMem_Pd d
  set δ := Metric.infDist F₀ (Pd d : Set C(↥II, ℝ)) with hδdef
  -- Apply density at `ε = δ/2`.
  obtain ⟨g, hg, hgε⟩ := hdense Kset isCompact_Kset f (ε := δ / 2) (by linarith)
  -- `g` agrees a.e. on `[0,1]` with a polynomial `q` of degree `≤ d`.
  obtain ⟨q, hqdeg, hqae⟩ := aePolyOn_of_mem_genSpan hp hg
  -- a.e. on `[0,1]`: `|t^(d+1) - q.eval t| ≤ δ/2`.
  have hae : ∀ᵐ t ∂(volume.restrict II),
      t ∈ {t : ℝ | |(Polynomial.X ^ (d + 1)).eval t - q.eval t| ≤ δ / 2} := by
    filter_upwards [hqae, ae_restrict_mem (measurableSet_Icc : MeasurableSet II)] with t hqt htII
    have ht : cvec t ∈ Kset := cvec_mem_Kset htII
    have hgt : g ⟨cvec t, ht⟩ = q.eval t := hqt ht
    have hfval : f ⟨cvec t, ht⟩ = (Polynomial.X ^ (d + 1)).eval t := by
      simp [hf, Polynomial.eval_pow]
    have := (hgε ⟨cvec t, ht⟩).le
    rw [hfval, hgt] at this
    exact this
  -- Bridge to everywhere on `[0,1]`.
  have hcont : Continuous fun t : ℝ =>
      |(Polynomial.X ^ (d + 1)).eval t - q.eval t| := by fun_prop
  have hclosed : IsClosed {t : ℝ | |(Polynomial.X ^ (d + 1)).eval t - q.eval t| ≤ δ / 2} :=
    isClosed_le hcont continuous_const
  have hall := subset_of_ae_restrict_mem hclosed hae
  -- Therefore `dist F₀ (restrictLM q) ≤ δ/2`.
  have hdist : dist F₀ (restrictLM q) ≤ δ / 2 := by
    rw [ContinuousMap.dist_le (by linarith)]
    intro x
    have hx : (x : ℝ) ∈ II := x.2
    have := hall hx
    simp only [Set.mem_setOf_eq] at this
    rw [Real.dist_eq, hF₀, restrictLM_apply, restrictLM_apply]
    exact this
  have hinfle : δ ≤ δ / 2 :=
    le_trans (Metric.infDist_le_dist_of_mem (restrictLM_mem_Pd hqdeg)) hdist
  linarith

end UniversalApproximation.Leshno
