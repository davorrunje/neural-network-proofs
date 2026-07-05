/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib

/-!
# Saturating activations and point reflection

This file develops the foundational analysis for the Sartor et al. saturating-activation
universal approximation results (arXiv, Definition 3.3 and Proposition 3.8).

An activation `σ : ℝ → ℝ` is *right-saturating* (`σ ∈ 𝒮⁺`) if it has a finite limit at `+∞`,
and *left-saturating* (`σ ∈ 𝒮⁻`) if it has a finite limit at `−∞` (Definition 3.3).

The *point reflection* `reflect σ x = −σ(−x)` (Proposition 3.8) is an involution that preserves
monotonicity and swaps the saturation side: `σ` is left-saturating iff `reflect σ` is
right-saturating, and dually.

* `RightSaturating` — `σ` has a finite limit at `atTop` (Definition 3.3, `𝒮⁺`).
* `LeftSaturating` — `σ` has a finite limit at `atBot` (Definition 3.3 dual, `𝒮⁻`).
* `reflect` — the point reflection `x ↦ −σ(−x)` (Proposition 3.8).
* `reflect_reflect` — `reflect` is an involution.
* `reflect_monotone` — `reflect` preserves monotonicity.
* `reflect_rightSaturating` / `reflect_leftSaturating` — `reflect` swaps the saturation side.
-/

namespace UniversalApproximation.Monotone

open Filter Topology

/-- Definition 3.3 (`𝒮⁺`): an activation `σ` is *right-saturating* if it has a finite limit as
its argument tends to `+∞`. -/
def RightSaturating (σ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto σ Filter.atTop (nhds L)

/-- Definition 3.3 (dual, `𝒮⁻`): an activation `σ` is *left-saturating* if it has a finite limit
as its argument tends to `−∞`. -/
def LeftSaturating (σ : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto σ Filter.atBot (nhds L)

/-- Proposition 3.8: the *point reflection* of an activation, `reflect σ x = −σ(−x)`. -/
def reflect (σ : ℝ → ℝ) : ℝ → ℝ := fun x => -σ (-x)

/-- The point reflection is an involution: `reflect (reflect σ) = σ`. -/
theorem reflect_reflect (σ : ℝ → ℝ) : reflect (reflect σ) = σ := by
  funext x
  simp only [reflect, neg_neg]

/-- Proposition 3.8: the point reflection of a monotone activation is monotone. -/
theorem reflect_monotone {σ : ℝ → ℝ} (hσ : Monotone σ) : Monotone (reflect σ) := by
  intro a b h
  simp only [reflect, neg_le_neg_iff]
  exact hσ (neg_le_neg h)

/-- Proposition 3.8 (`σ ∈ 𝒮⁻ → reflect σ ∈ 𝒮⁺`): if `σ` is left-saturating, then its point
reflection is right-saturating. -/
theorem reflect_rightSaturating {σ : ℝ → ℝ} (h : LeftSaturating σ) :
    RightSaturating (reflect σ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨-L, ?_⟩
  have hneg : Filter.Tendsto (fun x : ℝ => -x) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr Filter.tendsto_id
  exact (hL.comp hneg).neg

/-- Proposition 3.8 (`σ ∈ 𝒮⁺ → reflect σ ∈ 𝒮⁻`): if `σ` is right-saturating, then its point
reflection is left-saturating. -/
theorem reflect_leftSaturating {σ : ℝ → ℝ} (h : RightSaturating σ) :
    LeftSaturating (reflect σ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨-L, ?_⟩
  have hneg : Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
    Filter.tendsto_neg_atTop_iff.mpr Filter.tendsto_id
  exact (hL.comp hneg).neg

end UniversalApproximation.Monotone
