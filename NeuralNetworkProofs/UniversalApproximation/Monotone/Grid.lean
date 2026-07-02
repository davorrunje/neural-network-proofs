/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs

/-!
# The uniform grid and neighbour sandwich

This file builds the uniform grid on the unit cube `Set.Icc (0 : Fin d → ℝ) 1` used in the
approximation half of the Mikulincer–Reichman universal approximation result for monotone neural
networks (arXiv:2207.05275, Result 1).

For a resolution `m`, grid points are indexed by `k : Fin d → Fin (m + 1)`, with coordinate value
`(k i : ℝ) / m`; all grid points lie in the unit cube.  The map from indices to points is monotone
(for the coordinatewise Pi order) and, when `0 < m`, injective, so it yields a *monotone dataset*:
sampling a monotone `f` at the grid gives a labelling that respects the order, which is exactly the
hypothesis consumed by the interpolation theorem (Task 3).

* `gridPoint` — the point of a grid index; `gridPoint_mem_Icc`, `gridPoint_monotone`,
  `gridPoint_injective` its basic order/injectivity facts.
* `grid` — the finite set of grid points.
* `gridEnum` — an injective enumeration `Fin _ → (Fin d → ℝ)` of the grid, with
  `gridEnum_monotone_dataset` the monotone-dataset property for a monotone `f`.
* `grid_neighbors` — for `x` in the cube, grid indices whose points sandwich `x` coordinatewise with
  per-coordinate gap at most `1 / m`.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- The grid point of index `k : Fin d → Fin (m + 1)`: coordinate `i` has value `(k i : ℝ) / m`. -/
noncomputable def gridPoint {d : ℕ} (m : ℕ) (k : Fin d → Fin (m + 1)) : Fin d → ℝ :=
  fun i => (k i : ℝ) / m

/-- Every grid point lies in the unit cube `Set.Icc 0 1`. -/
theorem gridPoint_mem_Icc {d : ℕ} (m : ℕ) (k : Fin d → Fin (m + 1)) :
    gridPoint m k ∈ Set.Icc (0 : Fin d → ℝ) 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> simp [gridPoint]
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [gridPoint, Pi.zero_apply]
      positivity
    · simp only [gridPoint, Pi.one_apply]
      rw [div_le_one (by exact_mod_cast hm)]
      have : (k i : ℕ) ≤ m := Nat.lt_succ_iff.mp (k i).is_lt
      exact_mod_cast this

/-- The index-to-point map is monotone for the coordinatewise (Pi) orders. -/
theorem gridPoint_monotone {d : ℕ} (m : ℕ) : Monotone (gridPoint (d := d) m) := by
  intro k l hkl i
  simp only [gridPoint]
  gcongr
  exact_mod_cast hkl i

/-- When `0 < m`, distinct grid indices give distinct grid points. -/
theorem gridPoint_injective {d : ℕ} {m : ℕ} (hm : 0 < m) :
    Function.Injective (gridPoint (d := d) m) := by
  intro k l h
  funext i
  have hi : (k i : ℝ) / m = (l i : ℝ) / m := congrFun h i
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (k i : ℝ) = (l i : ℝ) := by
    field_simp at hi
    exact hi
  have : (k i : ℕ) = (l i : ℕ) := by exact_mod_cast this
  exact Fin.ext this

/-- The finite set of grid points at resolution `m`. -/
noncomputable def grid {d : ℕ} (m : ℕ) : Finset (Fin d → ℝ) :=
  Finset.univ.image (gridPoint (d := d) m)

/-- An injective enumeration of the grid indices by `Fin _`, and hence of the grid points via
`gridPoint`.  Concretely, `gridEnum m := gridPoint m ∘ e.symm` where `e` is the canonical
enumeration of the index type `Fin d → Fin (m + 1)`. -/
noncomputable def gridEnum {d : ℕ} (m : ℕ) :
    Fin (Fintype.card (Fin d → Fin (m + 1))) → (Fin d → ℝ) :=
  fun j => gridPoint m ((Fintype.equivFin (Fin d → Fin (m + 1))).symm j)

/-- Every enumerated grid point lies in the unit cube. -/
theorem gridEnum_mem_Icc {d : ℕ} (m : ℕ) (j : Fin (Fintype.card (Fin d → Fin (m + 1)))) :
    gridEnum m j ∈ Set.Icc (0 : Fin d → ℝ) 1 :=
  gridPoint_mem_Icc m _

/-- When `0 < m`, the grid enumeration is injective. -/
theorem gridEnum_injective {d : ℕ} {m : ℕ} (hm : 0 < m) :
    Function.Injective (gridEnum (d := d) m) := by
  intro a b h
  have := gridPoint_injective (d := d) hm h
  exact (Fintype.equivFin (Fin d → Fin (m + 1))).symm.injective this

/-- Sampling a monotone `f` at the enumerated grid yields a *monotone dataset*: whenever two grid
points are ordered, their `f`-values are ordered.  This is exactly the hypothesis consumed by the
interpolation theorem.  Only monotonicity of `f` on the cube is used (all grid points are in it). -/
theorem gridEnum_monotone_dataset {d : ℕ} (m : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    (a b : Fin (Fintype.card (Fin d → Fin (m + 1)))) (hab : gridEnum m a ≤ gridEnum m b) :
    f (gridEnum m a) ≤ f (gridEnum m b) :=
  hmono (gridEnum_mem_Icc m a) (gridEnum_mem_Icc m b) hab

/-- The clamped floor index of `x i` at resolution `m`: `min (⌊m · x i⌋₊) m`, as an element of
`Fin (m + 1)`.  Used as the lower grid neighbour's index. -/
noncomputable def floorIndex {d : ℕ} (m : ℕ) (x : Fin d → ℝ) (i : Fin d) : Fin (m + 1) :=
  ⟨min ⌊(m : ℝ) * x i⌋₊ m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The clamped ceil index of `x i` at resolution `m`: `min (⌈m · x i⌉₊) m`, as an element of
`Fin (m + 1)`.  Used as the upper grid neighbour's index. -/
noncomputable def ceilIndex {d : ℕ} (m : ℕ) (x : Fin d → ℝ) (i : Fin d) : Fin (m + 1) :=
  ⟨min ⌈(m : ℝ) * x i⌉₊ m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- For `x` in the unit cube and `0 < m`, there are grid indices `k₋ ≤ k₊` (as points) whose grid
points sandwich `x` coordinatewise, `gridPoint m k₋ ≤ x ≤ gridPoint m k₊`, with per-coordinate gap
at most `1 / m`.  Both endpoints are grid points, hence lie in the unit cube. -/
theorem grid_neighbors {d : ℕ} {m : ℕ} (hm : 0 < m) (x : Fin d → ℝ)
    (hx : x ∈ Set.Icc (0 : Fin d → ℝ) 1) :
    ∃ kl kr : Fin d → Fin (m + 1),
      gridPoint m kl ≤ x ∧ x ≤ gridPoint m kr ∧
      ∀ i, gridPoint m kr i - gridPoint m kl i ≤ 1 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : ∀ i, (0 : ℝ) ≤ x i := fun i => by simpa using hx.1 i
  have hx1 : ∀ i, x i ≤ 1 := fun i => by simpa using hx.2 i
  -- for `x i ∈ [0,1]` the clamps are inert: `⌊m·xᵢ⌋₊ ≤ m` and `⌈m·xᵢ⌉₊ ≤ m`.
  have ha0 : ∀ i, (0 : ℝ) ≤ (m : ℝ) * x i := fun i => by
    have := hx0 i; positivity
  have ham : ∀ i, (m : ℝ) * x i ≤ m := fun i => by
    calc (m : ℝ) * x i ≤ (m : ℝ) * 1 := by gcongr; exact hx1 i
      _ = m := by ring
  have hfloor_le : ∀ i, ⌊(m : ℝ) * x i⌋₊ ≤ m := fun i =>
    (Nat.floor_le_of_le (ham i)).trans (by simp)
  have hceil_le : ∀ i, ⌈(m : ℝ) * x i⌉₊ ≤ m := fun i => Nat.ceil_le.mpr (ham i)
  refine ⟨floorIndex m x, ceilIndex m x, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · -- `⌊m·xᵢ⌋₊ / m ≤ x i`
    simp only [gridPoint, floorIndex, Fin.val_mk, min_eq_left (hfloor_le i)]
    rw [div_le_iff₀ hmR]
    calc (⌊(m : ℝ) * x i⌋₊ : ℝ) ≤ (m : ℝ) * x i := Nat.floor_le (ha0 i)
      _ = x i * m := by ring
  · -- `x i ≤ ⌈m·xᵢ⌉₊ / m`
    simp only [gridPoint, ceilIndex, Fin.val_mk, min_eq_left (hceil_le i)]
    rw [le_div_iff₀ hmR]
    calc x i * m = (m : ℝ) * x i := by ring
      _ ≤ (⌈(m : ℝ) * x i⌉₊ : ℝ) := Nat.le_ceil _
  · -- gap: `(⌈m·xᵢ⌉₊ - ⌊m·xᵢ⌋₊) / m ≤ 1 / m`
    simp only [gridPoint, ceilIndex, floorIndex, Fin.val_mk,
      min_eq_left (hfloor_le i), min_eq_left (hceil_le i)]
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hmR]
    have : (⌈(m : ℝ) * x i⌉₊ : ℝ) ≤ (⌊(m : ℝ) * x i⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one ((m : ℝ) * x i)
    linarith

end UniversalApproximation.Monotone
