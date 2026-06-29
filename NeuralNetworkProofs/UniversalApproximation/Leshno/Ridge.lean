/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import NeuralNetworkProofs.ForMathlib.RidgePowersSpan

/-! # Ridge lift: univariate density ⇒ multivariate density.

Given a univariate-density hypothesis `UnivariateDense σ` (every continuous function on a compact
`I ⊆ ℝ` is approximable by `genSpan σ I`, i.e. `T σ I = ⊤`), we lift it to the multivariate
setting: every continuous ridge `x ↦ h ⟪a, x⟫` lands in `T σ K` (`ridge_mem_T`), and consequently
`T σ K = ⊤` for every compact `K ⊆ ℝⁿ` (`ridge_density`).
-/

namespace UniversalApproximation.Leshno

open scoped RealInnerProductSpace
open Topology RidgePowersSpan

variable {n : ℕ}

/-- Univariate density: every continuous function on a compact `I ⊆ ℝ` is approximable by
`genSpan σ I`. (Here `E = ℝ`, so `⟪w, x⟫ = w * x`.) -/
def UnivariateDense (σ : ℝ → ℝ) : Prop :=
  ∀ (I : Set ℝ), IsCompact I → T σ I = ⊤

/-- Core ridge-transfer lemma. If the ridge image `{⟪a, x⟫ : x ∈ K}` is contained in a *compact*
set `I ⊆ ℝ`, then `x ↦ h ⟪a, x⟫` is approximable by `genSpan σ K`. The compactness of `I` is what
lets us invoke `UnivariateDense σ` (density on compact univariate sets). -/
theorem approxByGen_ridge_of_compact_image {σ : ℝ → ℝ} (hσu : UnivariateDense σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (a : EuclideanSpace ℝ (Fin n)) (h : C(ℝ, ℝ))
    {I : Set ℝ} (hI : IsCompact I) (hsub : ∀ x ∈ K, (⟪a, x⟫ : ℝ) ∈ I) :
    ApproxByGen σ K (fun x : ↥K => h ⟪a, (x : EuclideanSpace ℝ (Fin n))⟫) := by
  -- The map `φ : ↥K → ↥I` sending `x ↦ ⟪a, x⟫`.
  set φ : ↥K → ↥I := fun x => ⟨⟪a, (x : EuclideanSpace ℝ (Fin n))⟫, hsub x x.2⟩ with hφ
  -- The precomposition linear map `Φ : (↥I → ℝ) →ₗ[ℝ] (↥K → ℝ)`.
  set Φ : (↥I → ℝ) →ₗ[ℝ] (↥K → ℝ) := LinearMap.funLeft ℝ ℝ φ with hΦ
  -- `Φ` carries each univariate generator into `genSpan σ K`.
  have hgen : ∀ wb : ℝ × ℝ, Φ (genFun σ wb.1 wb.2) ∈ genSpan σ K := by
    rintro ⟨w, b⟩
    have heq : Φ (genFun σ w b)
        = (fun x : ↥K => σ (w * (⟪a, (x : EuclideanSpace ℝ (Fin n))⟫ + 0) + b)) := by
      funext x
      simp only [hΦ, LinearMap.funLeft_apply, genFun, hφ]
      have : (⟪w, (φ x : ℝ)⟫ : ℝ) = w * (φ x : ℝ) := by
        simp [RCLike.inner_apply, mul_comm]
      rw [this]
      simp [hφ]
    rw [heq]
    exact genFun_reparam_mem σ K w a 0 b
  -- Hence `Φ` carries `genSpan σ I` into `genSpan σ K`.
  have hmap : ∀ g ∈ genSpan σ I, Φ g ∈ genSpan σ K := by
    intro g hg
    have him := Submodule.apply_mem_span_image_of_mem_span (R := ℝ) (R₂ := ℝ) Φ
      (s := Set.range fun wb : ℝ × ℝ => genFun σ wb.1 wb.2) hg
    refine Submodule.span_le.mpr ?_ him
    rintro _ ⟨_, ⟨wb, rfl⟩, rfl⟩
    exact hgen wb
  -- `h` viewed on `↥I` lies in `T σ I = ⊤`, hence is `ApproxByGen σ I`.
  have hmemI : (⟨fun s : ↥I => h (s : ℝ), by fun_prop⟩ : C(↥I, ℝ)) ∈ T σ I := by
    rw [hσu I hI]; exact Submodule.mem_top
  -- Now do the ε-transfer.
  intro ε hε
  obtain ⟨g, hg, hgε⟩ := hmemI ε hε
  refine ⟨Φ g, hmap g hg, fun x => ?_⟩
  have hval : Φ g x = g (φ x) := rfl
  rw [hval]
  have := hgε (φ x)
  simpa [hφ] using this

/-- Every continuous ridge `x ↦ h ⟪a, x⟫` lands in `T σ K` (for compact `K`). -/
theorem ridge_mem_T {σ : ℝ → ℝ} (hσu : UnivariateDense σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (a : EuclideanSpace ℝ (Fin n)) (h : C(ℝ, ℝ)) :
    (⟨fun x : ↥K => h ⟪a, (x : EuclideanSpace ℝ (Fin n))⟫, by fun_prop⟩ : C(↥K, ℝ)) ∈ T σ K := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (⟪a, x⟫ : ℝ)) := by fun_prop
  refine approxByGen_ridge_of_compact_image hσu K a h (I := (fun x => (⟪a, x⟫ : ℝ)) '' K)
    (hK.image hcont) ?_
  intro x hx
  exact ⟨x, hx, rfl⟩

/-- The same continuous core, but realised as a submodule of *plain* functions `↥K → ℝ`. It is
defeq, on the carrier, to `T σ K`, but lives in `↥K → ℝ`, which lets us absorb spans of (possibly
unbundled) functions before re-bundling. -/
def Tplain (σ : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ ((↥K) → ℝ) where
  carrier := {f | ApproxByGen σ K f}
  add_mem' := by
    intro a b ha hb ε hε
    obtain ⟨ga, hga, hgaε⟩ := ha (ε / 2) (by linarith)
    obtain ⟨gb, hgb, hgbε⟩ := hb (ε / 2) (by linarith)
    refine ⟨ga + gb, Submodule.add_mem _ hga hgb, fun x => ?_⟩
    have : a x + b x - (ga x + gb x) = (a x - ga x) + (b x - gb x) := by ring
    change |(a + b) x - (ga + gb) x| < ε
    simp only [Pi.add_apply]
    calc |a x + b x - (ga x + gb x)|
        = |(a x - ga x) + (b x - gb x)| := by rw [this]
      _ ≤ |a x - ga x| + |b x - gb x| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgaε x) (hgbε x)
      _ = ε := by ring
  zero_mem' := by
    intro ε hε
    exact ⟨0, Submodule.zero_mem _, fun x => by simp [hε]⟩
  smul_mem' := by
    intro c a ha ε hε
    rcases eq_or_ne c 0 with hc | hc
    · subst hc; exact ⟨0, Submodule.zero_mem _, fun x => by simp [hε]⟩
    · obtain ⟨g, hg, hgε⟩ := ha (ε / |c|) (by positivity)
      refine ⟨c • g, Submodule.smul_mem _ c hg, fun x => ?_⟩
      change |(c • a) x - (c • g) x| < ε
      simp only [Pi.smul_apply, smul_eq_mul]
      have heq : |c * a x - c * g x| = |c| * |a x - g x| := by rw [← mul_sub, abs_mul]
      rw [heq]
      have hcpos : 0 < |c| := abs_pos.mpr hc
      calc |c| * |a x - g x| < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hgε x) hcpos
        _ = ε := by field_simp

/-- Bridge: a continuous `h` lies in `T σ K` iff its underlying function lies in `Tplain σ K`. -/
theorem mem_T_iff_mem_Tplain {σ : ℝ → ℝ} {K : Set (EuclideanSpace ℝ (Fin n))} (h : C(↥K, ℝ)) :
    h ∈ T σ K ↔ (h : ↥K → ℝ) ∈ Tplain σ K := Iff.rfl

/-- The ridge density theorem: `T σ K = ⊤` for every compact `K ⊆ ℝⁿ`. -/
theorem ridge_density {σ : ℝ → ℝ} (hσu : UnivariateDense σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    T σ K = ⊤ := by
  haveI := isCompact_iff_compactSpace.mp hK
  -- Each ridge power `x ↦ ⟪a, x⟫ ^ k` lies (as an unbundled function) in `Tplain σ K`.
  have hridgePow : ∀ (a : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      (fun x : ↥K => (⟪a, (x : EuclideanSpace ℝ (Fin n))⟫ : ℝ) ^ k) ∈ Tplain σ K := by
    intro a k
    have := ridge_mem_T hσu K hK a ((ContinuousMap.id ℝ) ^ k)
    rw [mem_T_iff_mem_Tplain] at this
    simpa using this
  -- The inclusion `↥K → (Fin n → ℝ)` and precomposition `Λ`.
  set incl : ↥K → (Fin n → ℝ) := fun x => (x : EuclideanSpace ℝ (Fin n)) with hincl
  set Λ : ((Fin n → ℝ) → ℝ) →ₗ[ℝ] (↥K → ℝ) := LinearMap.funLeft ℝ ℝ incl with hΛ
  -- `Λ` carries the ridge-power generators of `ridgePow_span` into `Tplain σ K`.
  have hΛridge : ∀ (k : ℕ) (a : Fin n → ℝ),
      Λ (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k) ∈ Tplain σ K := by
    intro k a
    have h1 := hridgePow ((WithLp.equiv 2 (Fin n → ℝ)).symm a) k
    have heq : (Λ (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k))
        = (fun x : ↥K =>
            (⟪(WithLp.equiv 2 (Fin n → ℝ)).symm a, (x : EuclideanSpace ℝ (Fin n))⟫ : ℝ) ^ k) := by
      funext x
      simp only [hΛ, LinearMap.funLeft_apply, hincl]
      congr 1
      rw [PiLp.inner_apply]
      simp [RCLike.inner_apply, mul_comm]
    rw [heq]; exact h1
  -- `Λ` carries any homogeneous-degree-`k` polynomial *function* into `Tplain σ K`.
  have hΛhom : ∀ (k : ℕ) (q : MvPolynomial (Fin n) ℝ),
      q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      Λ (MvPolynomial.evalₗ ℝ (Fin n) q) ∈ Tplain σ K := by
    intro k q hq
    have hspan : MvPolynomial.evalₗ ℝ (Fin n) q
        ∈ Submodule.span ℝ
            (Set.range fun a : Fin n → ℝ => (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k)) := by
      rw [RidgePowersSpan.ridgePow_span k]
      exact Submodule.mem_map_of_mem hq
    have := Submodule.apply_mem_span_image_of_mem_span (R := ℝ) (R₂ := ℝ) Λ
      (s := Set.range fun a : Fin n → ℝ => (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k)) hspan
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hΛridge k a
  -- Coordinate functions as continuous maps on `↥K`.
  set coordCM : Fin n → C(↥K, ℝ) :=
    fun i => ⟨fun x => (x : EuclideanSpace ℝ (Fin n)) i, by fun_prop⟩ with hcoord
  -- `⇑(aeval coordCM p) = Λ (evalₗ p)` for every `p`.
  have hcoe : ∀ p : MvPolynomial (Fin n) ℝ,
      (⇑(MvPolynomial.aeval coordCM p) : ↥K → ℝ) = Λ (MvPolynomial.evalₗ ℝ (Fin n) p) := by
    intro p
    funext x
    simp only [hΛ, LinearMap.funLeft_apply, MvPolynomial.evalₗ_apply, hincl]
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_mul, MvPolynomial.eval_X]
        change ((MvPolynomial.aeval coordCM p) x) * (coordCM i x) = _
        rw [hp]; rfl
  -- Every polynomial function lies in `T σ K`.
  have hpoly_mem : ∀ p : MvPolynomial (Fin n) ℝ, MvPolynomial.aeval coordCM p ∈ T σ K := by
    intro p
    rw [mem_T_iff_mem_Tplain, hcoe p]
    have hsum : MvPolynomial.evalₗ ℝ (Fin n) p
        = ∑ k ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.evalₗ ℝ (Fin n) (MvPolynomial.homogeneousComponent k p) := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    exact hΛhom k _ (MvPolynomial.homogeneousComponent_mem k p)
  -- The subalgebra of polynomial functions.
  set A : Subalgebra ℝ C(↥K, ℝ) := (MvPolynomial.aeval coordCM).range with hA
  -- `A` separates points (its coordinate functions do).
  have hsep : A.SeparatesPoints := by
    intro u v huv
    have hne : (fun i => (u : EuclideanSpace ℝ (Fin n)).ofLp i)
        ≠ (fun i => (v : EuclideanSpace ℝ (Fin n)).ofLp i) := by
      intro hcontra
      exact huv (Subtype.ext (by ext i; exact congrFun hcontra i))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨(coordCM i : ↥K → ℝ), ⟨coordCM i, ?_, rfl⟩, ?_⟩
    · exact ⟨MvPolynomial.X i, by simp [hcoord]⟩
    · simpa [hcoord] using hi
  -- `A ⊆ T σ K`.
  have hAle : (A : Set C(↥K, ℝ)) ⊆ (T σ K : Set C(↥K, ℝ)) := by
    rintro f ⟨p, rfl⟩
    exact hpoly_mem p
  -- Stone–Weierstrass + closedness of `T`.
  rw [eq_top_iff]
  intro f _
  have hclosed := T_isClosed σ hK
  have hclF : f ∈ A.topologicalClosure :=
    ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints A hsep f
  have hsubclosure : (A.topologicalClosure : Set C(↥K, ℝ)) ⊆ (T σ K : Set C(↥K, ℝ)) := by
    rw [Subalgebra.topologicalClosure_coe]
    exact closure_minimal hAle hclosed
  exact hsubclosure hclF

end UniversalApproximation.Leshno
