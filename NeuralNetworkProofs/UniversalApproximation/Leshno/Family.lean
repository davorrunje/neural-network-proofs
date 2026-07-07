/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM

/-! # The generator family, span, and the continuous-core submodule `T`.

This file builds the linear-algebraic / topological scaffold of the Leshno (1993) universal
approximation theorem:

* `genFun σ w b` — a single hidden unit `x ↦ σ (⟪w, x⟫ + b)`, a (possibly discontinuous)
  function `↥K → ℝ`;
* `genSpan σ K` — the linear span of all hidden units, a submodule of the module of *all*
  functions `↥K → ℝ` (generators may be discontinuous, so we cannot stay inside `C(↥K, ℝ)`);
* `ApproxByGen σ K h` — `h` is approximable in sup-norm by elements of `genSpan σ K`;
* `T σ K` — the *continuous core*: the submodule of `C(↥K, ℝ)` of continuous functions that are
  approximable by `genSpan σ K`;
* `genFun_reparam_mem` — the span is invariant under affine reparametrisation of the argument;
* `T_isClosed` — `T σ K` is closed (a sup-norm limit of approximable functions is approximable);
* `DenselyApproximates σ` — the target conclusion: on every compact `K ⊆ ℝⁿ`, every continuous
  function is approximable by `genSpan σ K`;
* `denselyApproximates_of_forall_T_eq_top` — the reduction: if `T σ K = ⊤` for every compact `K`,
  then `σ` densely approximates.
-/

namespace UniversalApproximation.Leshno

open scoped RealInnerProductSpace
open Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single hidden unit: the (possibly discontinuous) function `x ↦ σ (⟪w, x⟫ + b)`. -/
def genFun (σ : ℝ → ℝ) {K : Set E} (w : E) (b : ℝ) : ↥K → ℝ :=
  fun x => σ (⟪w, (x : E)⟫ + b)

/-- The linear span of all hidden units, inside the module of *all* functions `↥K → ℝ`. -/
def genSpan (σ : ℝ → ℝ) (K : Set E) : Submodule ℝ (↥K → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : E × ℝ => genFun σ wb.1 wb.2)

/-- `h` is approximable in sup-norm by elements of `genSpan σ K`. -/
def ApproxByGen (σ : ℝ → ℝ) (K : Set E) (h : ↥K → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ g ∈ genSpan σ K, ∀ x, |h x - g x| < ε

/-- The continuous core: continuous functions approximable by `genSpan σ K`. -/
def T (σ : ℝ → ℝ) (K : Set E) : Submodule ℝ C(↥K, ℝ) where
  carrier := {h | ApproxByGen σ K (h : ↥K → ℝ)}
  add_mem' := by
    intro a b ha hb ε hε
    obtain ⟨ga, hga, hgaε⟩ := ha (ε / 2) (by linarith)
    obtain ⟨gb, hgb, hgbε⟩ := hb (ε / 2) (by linarith)
    refine ⟨ga + gb, Submodule.add_mem _ hga hgb, fun x => ?_⟩
    have hx : ((a + b : C(↥K, ℝ)) : ↥K → ℝ) x = a x + b x := rfl
    have hgx : (ga + gb) x = ga x + gb x := rfl
    rw [hx, hgx]
    have hrw : a x + b x - (ga x + gb x) = (a x - ga x) + (b x - gb x) := by ring
    rw [hrw]
    calc |(a x - ga x) + (b x - gb x)|
        ≤ |a x - ga x| + |b x - gb x| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgaε x) (hgbε x)
      _ = ε := by ring
  zero_mem' := by
    intro ε hε
    refine ⟨0, Submodule.zero_mem _, fun x => ?_⟩
    have hx : ((0 : C(↥K, ℝ)) : ↥K → ℝ) x = 0 := rfl
    simp [hx, hε]
  smul_mem' := by
    intro c a ha ε hε
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      refine ⟨0, Submodule.zero_mem _, fun x => ?_⟩
      simp [hε]
    · obtain ⟨g, hg, hgε⟩ := ha (ε / |c|) (by positivity)
      refine ⟨c • g, Submodule.smul_mem _ c hg, fun x => ?_⟩
      have hx : ((c • a : C(↥K, ℝ)) : ↥K → ℝ) x = c * a x := rfl
      have hgx : (c • g) x = c * g x := rfl
      rw [hx, hgx]
      have : |c * a x - c * g x| = |c| * |a x - g x| := by
        rw [← mul_sub, abs_mul]
      rw [this]
      have hcpos : 0 < |c| := abs_pos.mpr hc
      calc |c| * |a x - g x| < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hgε x) hcpos
        _ = ε := by field_simp

/-- The span is invariant under affine reparametrisation of the argument. -/
theorem genFun_reparam_mem (σ : ℝ → ℝ) (K : Set E) (lam : ℝ) (w : E) (b c : ℝ) :
    (fun x : ↥K => σ (lam * (⟪w, (x : E)⟫ + b) + c)) ∈ genSpan σ K := by
  have heq : (fun x : ↥K => σ (lam * (⟪w, (x : E)⟫ + b) + c))
      = genFun σ (lam • w) (lam * b + c) := by
    ext x; simp only [genFun]; rw [real_inner_smul_left]; ring_nf
  rw [heq]
  exact Submodule.subset_span ⟨(lam • w, lam * b + c), rfl⟩

/-- `T σ K` is closed (for compact `K`): a sup-norm limit of approximable continuous functions is
approximable.

The carrier of `T` is defined by *uniform* (sup over all of `K`) approximability. For *compact*
`K`, `↥K` is a `CompactSpace`, so `C(↥K, ℝ)` is a metric space whose distance is the sup-norm;
compact-convergence then coincides with uniform convergence and the triangle-inequality argument
goes through. (For non-compact `K` the carrier need not be closed, which is why compactness is
required here.) -/
theorem T_isClosed (σ : ℝ → ℝ) {K : Set E} (hK : IsCompact K) :
    IsClosed (T σ K : Set C(↥K, ℝ)) := by
  haveI := isCompact_iff_compactSpace.mp hK
  apply isClosed_of_closure_subset
  intro h hh
  rw [Metric.mem_closure_iff] at hh
  -- Goal: `h ∈ T σ K`, i.e. `ApproxByGen σ K ⇑h`.
  intro ε hε
  -- Pick `h' ∈ T` within `ε/2` of `h` in sup-norm.
  obtain ⟨h', hh'mem, hh'dist⟩ := hh (ε / 2) (by linarith)
  -- `h'` is approximable: get `g ∈ genSpan` within `ε/2` of `h'` pointwise.
  obtain ⟨g, hg, hgε⟩ := hh'mem (ε / 2) (by linarith)
  refine ⟨g, hg, fun x => ?_⟩
  -- Pointwise: `|h x - h' x| ≤ dist h h' < ε/2`, and `|h' x - g x| < ε/2`; triangle.
  have hpt : |h x - h' x| ≤ dist h h' := by
    have := ContinuousMap.dist_apply_le_dist (f := h) (g := h') x
    rwa [Real.dist_eq] at this
  calc |h x - g x| = |(h x - h' x) + (h' x - g x)| := by ring_nf
    _ ≤ |h x - h' x| + |h' x - g x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt hpt hh'dist) (hgε x)
    _ = ε := by ring

/-- The target conclusion: on every compact `K ⊆ ℝⁿ`, every continuous function is approximable
by `genSpan σ K`. -/
def DenselyApproximates (σ : ℝ → ℝ) : Prop :=
  ∀ {n} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → ∀ (f : C(↥K, ℝ)) {ε},
    0 < ε → ∃ g ∈ genSpan σ K, ∀ x, |f x - g x| < ε

/-- The reduction: if `T σ K = ⊤` for every compact `K`, then `σ` densely approximates. -/
theorem denselyApproximates_of_forall_T_eq_top {σ : ℝ → ℝ}
    (h : ∀ {n} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → T σ K = ⊤) :
    DenselyApproximates σ := by
  intro n K hK f ε hε
  have hmem : f ∈ T σ K := by rw [h K hK]; exact Submodule.mem_top
  exact hmem ε hε

end UniversalApproximation.Leshno
