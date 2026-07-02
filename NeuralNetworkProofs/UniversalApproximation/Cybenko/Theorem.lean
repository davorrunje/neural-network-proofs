/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Cybenko.Activation
import NeuralNetworkProofs.UniversalApproximation.Cybenko.Discriminatory
import NeuralNetworkProofs.UniversalApproximation.Cybenko.Family
import NeuralNetworkProofs.UniversalApproximation.Cybenko.Riesz

/-!
# Universal Approximation Theorem (Cybenko, scaffold)

This file contains the Hahn–Banach reduction (proved), the main
`universal_approximation` theorem and its ε-form corollary.
-/

namespace UniversalApproximation.Cybenko

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A continuous linear functional `f` on a normed `ℝ`-space that is *strictly bounded
below* by a constant `u` on a submodule `V` (i.e. `u < f b` for every `b ∈ V`) must
vanish identically on `V`.

This is the linear-algebra core of the backward direction of
`dense_iff_forall_functional_eq_zero`: geometric Hahn–Banach only yields a strict lower
bound on the separating functional, but scaling elements of the subspace forces that
functional to be zero on the subspace. -/
private lemma eq_zero_of_lt_on_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E →L[ℝ] ℝ) {u : ℝ} (hfb : ∀ b ∈ V, u < f b) :
    ∀ b ∈ V, f b = 0 := by
  intro b hb
  by_contra hfb0
  have key : ∀ t : ℝ, u < t * f b := by
    intro t
    have hmem : (t • b) ∈ V := V.smul_mem t hb
    have := hfb (t • b) hmem
    rwa [map_smul, smul_eq_mul] at this
  have := key ((u - 1) / f b)
  rw [div_mul_cancel₀ _ hfb0] at this
  linarith

/-- **PROVED.** A subspace `V` of `C(K, ℝ)` is dense (its topological closure is
everything) iff every continuous linear functional vanishing on `V` is the zero
functional. This is the Hahn–Banach reduction underlying the UAT proof.

The forward direction uses continuity of `L`: it vanishes on `V`, hence on the
closure of `V`, which is everything. The backward direction is the contrapositive:
if `V` is not dense, pick a point `x` outside the closed convex set
`V.topologicalClosure` and apply geometric Hahn–Banach
(`geometric_hahn_banach_point_closed`) to obtain a continuous functional `f`
separating `x` from the closure. A linear functional bounded below on the subspace
`V` must vanish on `V`, so `f` is a nonzero functional vanishing on `V`,
contradicting the right-hand side. -/
theorem dense_iff_forall_functional_eq_zero
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (V : Submodule ℝ C(↥K, ℝ)) :
    V.topologicalClosure = ⊤ ↔
      ∀ L : C(↥K, ℝ) →L[ℝ] ℝ, (∀ g ∈ V, L g = 0) → L = 0 := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  constructor
  · intro hdense L hL
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ (V.topologicalClosure : Set C(↥K, ℝ)) := by
      rw [hdense]; trivial
    have hxclo : x ∈ closure (V : Set C(↥K, ℝ)) := by
      rwa [Submodule.topologicalClosure_coe] at hx
    have hcont : Continuous (L : C(↥K, ℝ) → ℝ) := L.continuous
    have hclo : (closure (V : Set C(↥K, ℝ))) ⊆ {y | L y = 0} := by
      apply (IsClosed.closure_subset_iff (isClosed_eq hcont continuous_const)).mpr
      intro y hy
      exact hL y hy
    have := hclo hxclo
    simpa using this
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, x ∉ V.topologicalClosure := by
      by_contra hall
      push Not at hall
      exact hne (by ext y; simp [hall y])
    have hxset : x ∉ (V.topologicalClosure : Set C(↥K, ℝ)) := hx
    have hclosed : IsClosed (V.topologicalClosure : Set C(↥K, ℝ)) :=
      V.isClosed_topologicalClosure
    have hconv : Convex ℝ (V.topologicalClosure : Set C(↥K, ℝ)) :=
      V.topologicalClosure.convex
    obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hconv hclosed hxset
    have hVsub : (V : Set C(↥K, ℝ)) ⊆ (V.topologicalClosure : Set C(↥K, ℝ)) :=
      V.le_topologicalClosure
    have hfV : ∀ b ∈ V, f b = 0 :=
      eq_zero_of_lt_on_submodule V f (fun b hb => hfb b (hVsub hb))
    have hf0 : f = 0 := h f hfV
    have hfx0 : f x = 0 := by rw [hf0]; rfl
    have hu0 : u < 0 := by
      have := hfb 0 (V.topologicalClosure.zero_mem)
      simpa using this
    rw [hfx0] at hfx
    linarith

/-- **Universal Approximation Theorem** (Cybenko, scaffold). The single-hidden-layer
family with a continuous sigmoidal activation is dense in `C(K, ℝ)`.

Proof: reduce density to "every continuous functional vanishing on the family is
zero" via `dense_iff_forall_functional_eq_zero`. Represent such a functional `L`
by a signed measure `μ` (`riesz_repr`). Since every generator lies in the family,
`L` vanishes on all generators, i.e. `μ` annihilates every `x ↦ σ(⟪w,x⟫ + b)`. By
`sigmoidal_discriminatory`, `μ = 0`, hence `L = 0`. -/
theorem universal_approximation
    (σ : ℝ → ℝ) (hσ : Sigmoidal σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    (S σ hσ.continuous (K := K)).topologicalClosure = ⊤ := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  rw [dense_iff_forall_functional_eq_zero hK]
  intro L hL
  obtain ⟨μ, hrepr, hzero⟩ := riesz_repr L
  have hgen : ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
      signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0 := by
    intro w b
    have hmem : generator σ hσ.continuous (K := K) w b ∈ S σ hσ.continuous (K := K) :=
      generator_mem_S σ hσ.continuous w b
    have hL0 := hL _ hmem
    rw [hrepr] at hL0
    exact hL0
  have hμ : μ = 0 := sigmoidal_discriminatory hσ μ hgen
  exact hzero.mpr hμ

/-- **ε-form corollary.** Every continuous function on the compact set `K` can be
approximated to arbitrary precision in the sup-norm by an element of the
single-hidden-layer family.

(The `[CompactSpace ↥K]` instance is needed so that the sup-norm `‖·‖` on
`C(↥K, ℝ)` is available in the statement; it is implied by `hK` and is supplied
automatically at every call site via `isCompact_iff_compactSpace`.) -/
theorem universal_approximation_eps
    (σ : ℝ → ℝ) (hσ : Sigmoidal σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) [CompactSpace ↥K]
    (f : C(↥K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ S σ hσ.continuous (K := K), ‖f - g‖ < ε := by
  have hdense := universal_approximation σ hσ hK
  have hmem : f ∈ closure (S σ hσ.continuous (K := K) : Set C(↥K, ℝ)) := by
    have h1 : f ∈ ((S σ hσ.continuous (K := K)).topologicalClosure : Set C(↥K, ℝ)) := by
      rw [hdense]; trivial
    rwa [Submodule.topologicalClosure_coe] at h1
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨g, hg, hdist⟩ := hmem ε hε
  refine ⟨g, hg, ?_⟩
  rw [dist_eq_norm] at hdist
  exact hdist

end UniversalApproximation.Cybenko
