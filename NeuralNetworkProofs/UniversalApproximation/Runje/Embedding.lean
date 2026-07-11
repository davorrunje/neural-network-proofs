/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Unconstrained Pi-side embedding span + Leshno bridge (Runje et al.)

`genSpanPi σ df` is the single-hidden-layer span on the module of *total* functions
`(Fin df → ℝ) → ℝ`, written with the explicit dot product `σ (∑ c, w c * x c + b)` so that **no**
inner-product instance on the Pi type is required.

`leshno_bridge` transports Leshno's `DenselyApproximates` — which is stated on
`EuclideanSpace ℝ (Fin df)` — to this Pi-side span, through the isometry
`e := EuclideanSpace.equiv (Fin df) ℝ` (whose real inner product is exactly the coordinate dot
product, `inner_eq_dot`). `exists_vector_embedding` packages the bridge for a whole finite family
of continuous targets.

This embedding drives the partial-monotone construction, a secondary result of the Deep
Constrained Monotonic Neural Networks development of Runje et al.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Leshno
open scoped RealInnerProductSpace

/-- A single Pi-side hidden unit `x ↦ σ (∑ c, w c * x c + b)`, a total function. -/
def genFunPi (σ : ℝ → ℝ) {df : ℕ} (w : Fin df → ℝ) (b : ℝ) : (Fin df → ℝ) → ℝ :=
  fun x => σ ((∑ c, w c * x c) + b)

/-- The Pi-side single-hidden-layer span, inside the module of *all* functions
`(Fin df → ℝ) → ℝ`. -/
def genSpanPi (σ : ℝ → ℝ) (df : ℕ) : Submodule ℝ ((Fin df → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : (Fin df → ℝ) × ℝ => genFunPi σ wb.1 wb.2)

/-- The real Euclidean inner product on `EuclideanSpace ℝ (Fin df)` is the coordinate dot
product `∑ c, w c * v c`. -/
lemma inner_eq_dot {df : ℕ} (w v : EuclideanSpace ℝ (Fin df)) :
    (⟪w, v⟫ : ℝ) = ∑ c, w c * v c := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- **The Leshno bridge.** If `σ` densely approximates (Leshno, on `EuclideanSpace`), then every
`ContinuousOn ψ K` on a compact `K ⊆ (Fin df → ℝ)` is uniformly approximated on `K` by a *total*
element `g` of the Pi-side span `genSpanPi σ df`.

We transport along the isometry `e := EuclideanSpace.equiv (Fin df) ℝ`: pull `K` and `ψ` back to
`Ke := e ⁻¹' K` (still compact) and to a continuous map on `↥Ke`, invoke Leshno to obtain a span
element `ge`, extract a finite `Finsupp` combination of Euclidean hidden units, and rebuild it as
the *total* sum of the corresponding Pi-side units `genFunPi σ (e w) b`. Each Pi-side unit agrees
with its Euclidean counterpart under `e` by `inner_eq_dot`, so the approximation bound transfers. -/
theorem leshno_bridge {σ : ℝ → ℝ} (hd : DenselyApproximates σ) {df : ℕ}
    {K : Set (Fin df → ℝ)} (hK : IsCompact K) (ψ : (Fin df → ℝ) → ℝ)
    (hψ : ContinuousOn ψ K) {η : ℝ} (hη : 0 < η) :
    ∃ g ∈ genSpanPi σ df, ∀ u ∈ K, |ψ u - g u| < η := by
  set e := EuclideanSpace.equiv (Fin df) ℝ with he
  set Ke : Set (EuclideanSpace ℝ (Fin df)) := e ⁻¹' K with hKedef
  -- `Ke` is compact: `e` is a homeomorphism and `K` is compact.
  have hKe : IsCompact Ke := e.toHomeomorph.isCompact_preimage.mpr hK
  -- Package `ψ` as a continuous map `ψe : C(↥Ke, ℝ)` via `ψ ∘ e`.
  have hemb : Continuous fun v : ↥Ke => (⟨e ↑v, v.2⟩ : ↥K) :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  let emb : C(↥Ke, ↥K) := ⟨_, hemb⟩
  let ψr : C(↥K, ℝ) := ⟨K.restrict ψ, hψ.restrict⟩
  let ψe : C(↥Ke, ℝ) := ψr.comp emb
  -- Leshno gives a Euclidean span element `ge` approximating `ψe`.
  obtain ⟨ge, hge_mem, hge_ε⟩ := hd Ke hKe ψe hη
  -- Extract a finite `Finsupp` linear combination of Euclidean hidden units.
  rw [genSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hge_mem
  obtain ⟨cf, hcf⟩ := hge_mem
  -- Rebuild it as the corresponding *total* Pi-side combination.
  refine ⟨cf.sum fun wb a => a • genFunPi σ (e wb.1) wb.2, ?_, ?_⟩
  · -- Membership in `genSpanPi`: a finite sum of scalar multiples of generators.
    rw [genSpanPi, Finsupp.sum]
    apply Submodule.sum_mem
    intro wb _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(e wb.1, wb.2), rfl⟩)
  · -- Transfer the bound pointwise: for `u ∈ K`, use `v := e.symm u ∈ Ke`.
    intro u hu
    set v : EuclideanSpace ℝ (Fin df) := e.symm u with hv
    have hev : e v = u := by rw [hv]; exact e.apply_symm_apply u
    have hvKe : v ∈ Ke := by rw [hKedef, Set.mem_preimage, hev]; exact hu
    -- Each Pi-side unit at `u` equals its Euclidean counterpart at `⟨v, _⟩` (by `inner_eq_dot`).
    have key : ∀ wb : EuclideanSpace ℝ (Fin df) × ℝ,
        genFunPi σ (e wb.1) wb.2 u = genFun σ wb.1 wb.2 ⟨v, hvKe⟩ := by
      intro wb
      change genFunPi σ (e wb.1) wb.2 u = σ (⟪wb.1, v⟫ + wb.2)
      rw [← hev]
      simp only [genFunPi]
      rw [inner_eq_dot wb.1 v]
      rfl
    have hψeq : ψ u = ψe ⟨v, hvKe⟩ := by change ψ u = ψ (e v); rw [hev]
    have hgeq : (cf.sum fun wb a => a • genFunPi σ (e wb.1) wb.2) u = ge ⟨v, hvKe⟩ := by
      rw [← hcf]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun wb _ => by rw [key wb]
    rw [hψeq, hgeq]
    exact hge_ε ⟨v, hvKe⟩

/-- Vector form of the bridge: a whole finite family `ψ : Fin N → (Fin df → ℝ) → ℝ` of
continuous-on-`K` targets is simultaneously approximated to accuracy `η` by a family `φ` of
elements of `genSpanPi σ df`. -/
theorem exists_vector_embedding {σ : ℝ → ℝ} (hd : DenselyApproximates σ) {df N : ℕ}
    {K : Set (Fin df → ℝ)} (hK : IsCompact K) (ψ : Fin N → (Fin df → ℝ) → ℝ)
    (hψ : ∀ i, ContinuousOn (ψ i) K) {η : ℝ} (hη : 0 < η) :
    ∃ φ : Fin N → (Fin df → ℝ) → ℝ, (∀ i, φ i ∈ genSpanPi σ df) ∧
      ∀ i, ∀ u ∈ K, |ψ i u - φ i u| < η := by
  choose φ hφmem hφε using fun i => leshno_bridge hd hK (ψ i) (hψ i) hη
  exact ⟨φ, hφmem, hφε⟩

end UniversalApproximation.Runje
