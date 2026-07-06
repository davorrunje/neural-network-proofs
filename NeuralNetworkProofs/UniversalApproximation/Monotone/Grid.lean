/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs

/-!
# The uniform grid and neighbour sandwich

This file builds the uniform grid on the unit cube `Set.Icc (0 : Fin d → ℝ) 1` used in the
approximation half of the Mikulincer–Reichman universal approximation result for monotone neural
networks (arXiv:2207.05275, Result 1).

The grid uses `m + 1` subdivisions per axis, so grid points are indexed by `k : Fin d → Fin (m + 2)`
with coordinate value `(k i : ℝ) / (m + 1)`.  Because the denominator `m + 1` is always positive,
the grid is genuine for every `m` (no `0 < m` side condition): all grid points lie in the unit cube,
the index-to-point map is monotone (for the coordinatewise Pi order) and injective, and it yields a
*monotone dataset* — sampling a monotone `f` at the grid gives a labelling that respects the order,
which is exactly the hypothesis consumed by the interpolation theorem.

* `gridPoint` — the point of a grid index; `gridPoint_mem_Icc`, `gridPoint_injective` its basic
  order/injectivity facts.
* `gridEnum` — an injective enumeration `Fin _ → (Fin d → ℝ)` of the grid, with
  `gridEnum_monotone_dataset` the monotone-dataset property for a `MonotoneOn` `f`.
* `grid_neighbors` — for `x` in the cube, grid indices whose points sandwich `x` coordinatewise with
  per-coordinate gap at most `1 / (m + 1)`.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- The grid point of index `k : Fin d → Fin (m + 2)` at resolution `m + 1`: coordinate `i` has
value `(k i : ℝ) / (m + 1)`.  The denominator `m + 1` is always positive, so the grid needs no
`0 < m` side condition. -/
noncomputable def gridPoint {d : ℕ} (m : ℕ) (k : Fin d → Fin (m + 2)) : Fin d → ℝ :=
  fun i => (k i : ℝ) / (m + 1)

/-- Every grid point lies in the unit cube `Set.Icc 0 1`. -/
theorem gridPoint_mem_Icc {d : ℕ} (m : ℕ) (k : Fin d → Fin (m + 2)) :
    gridPoint m k ∈ Set.Icc (0 : Fin d → ℝ) 1 := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [gridPoint, Pi.zero_apply]
    positivity
  · simp only [gridPoint, Pi.one_apply]
    rw [div_le_one (by positivity)]
    have : (k i : ℕ) ≤ m + 1 := Nat.lt_succ_iff.mp (k i).is_lt
    exact_mod_cast this

/-- Distinct grid indices give distinct grid points. -/
theorem gridPoint_injective {d : ℕ} (m : ℕ) :
    Function.Injective (gridPoint (d := d) m) := by
  intro k l h
  funext i
  have hm' : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hi : (k i : ℝ) / ((m : ℝ) + 1) = (l i : ℝ) / ((m : ℝ) + 1) := congrFun h i
  have : (k i : ℝ) = (l i : ℝ) := (div_left_inj' hm').1 hi
  exact Fin.ext (by exact_mod_cast this)

/-- An injective enumeration of the grid indices by `Fin _`, and hence of the grid points via
`gridPoint`.  Concretely, `gridEnum m := gridPoint m ∘ e.symm` where `e` is the canonical
enumeration of the index type `Fin d → Fin (m + 2)`. -/
noncomputable def gridEnum {d : ℕ} (m : ℕ) :
    Fin (Fintype.card (Fin d → Fin (m + 2))) → (Fin d → ℝ) :=
  fun j => gridPoint m ((Fintype.equivFin (Fin d → Fin (m + 2))).symm j)

/-- Every enumerated grid point lies in the unit cube. -/
theorem gridEnum_mem_Icc {d : ℕ} (m : ℕ) (j : Fin (Fintype.card (Fin d → Fin (m + 2)))) :
    gridEnum m j ∈ Set.Icc (0 : Fin d → ℝ) 1 :=
  gridPoint_mem_Icc m _

/-- The grid enumeration is injective. -/
theorem gridEnum_injective {d : ℕ} (m : ℕ) :
    Function.Injective (gridEnum (d := d) m) := by
  intro a b h
  have := gridPoint_injective (d := d) m h
  exact (Fintype.equivFin (Fin d → Fin (m + 2))).symm.injective this

/-- Sampling a monotone `f` at the enumerated grid yields a *monotone dataset*: whenever two grid
points are ordered, their `f`-values are ordered.  This is exactly the hypothesis consumed by the
interpolation theorem.  Only `MonotoneOn f` on the cube is used (all grid points lie in it). -/
theorem gridEnum_monotone_dataset {d : ℕ} (m : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hmono : MonotoneOn f (Set.Icc (0 : Fin d → ℝ) 1))
    (a b : Fin (Fintype.card (Fin d → Fin (m + 2)))) (hab : gridEnum m a ≤ gridEnum m b) :
    f (gridEnum m a) ≤ f (gridEnum m b) :=
  hmono (gridEnum_mem_Icc m a) (gridEnum_mem_Icc m b) hab

/-- The clamped floor index of `x i` at resolution `m + 1`: `min ⌊(m + 1) · x i⌋₊ (m + 1)`, as an
element of `Fin (m + 2)`.  Used as the lower grid neighbour's index. -/
noncomputable def floorIndex {d : ℕ} (m : ℕ) (x : Fin d → ℝ) (i : Fin d) : Fin (m + 2) :=
  ⟨min ⌊((m : ℝ) + 1) * x i⌋₊ (m + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The clamped ceil index of `x i` at resolution `m + 1`: `min ⌈(m + 1) · x i⌉₊ (m + 1)`, as an
element of `Fin (m + 2)`.  Used as the upper grid neighbour's index. -/
noncomputable def ceilIndex {d : ℕ} (m : ℕ) (x : Fin d → ℝ) (i : Fin d) : Fin (m + 2) :=
  ⟨min ⌈((m : ℝ) + 1) * x i⌉₊ (m + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- For `x` in the unit cube, there are grid indices `kl`, `kr` whose grid points sandwich `x`
coordinatewise, `gridPoint m kl ≤ x ≤ gridPoint m kr`, with per-coordinate gap at most
`1 / (m + 1)`.  Both endpoints are grid points, hence lie in the unit cube. -/
theorem grid_neighbors {d : ℕ} (m : ℕ) (x : Fin d → ℝ)
    (hx : x ∈ Set.Icc (0 : Fin d → ℝ) 1) :
    ∃ kl kr : Fin d → Fin (m + 2),
      gridPoint m kl ≤ x ∧ x ≤ gridPoint m kr ∧
      ∀ i, gridPoint m kr i - gridPoint m kl i ≤ 1 / (m + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hx0 : ∀ i, (0 : ℝ) ≤ x i := fun i => by simpa using hx.1 i
  have hx1 : ∀ i, x i ≤ 1 := fun i => by simpa using hx.2 i
  -- for `x i ∈ [0,1]` the clamps are inert: `⌊(m+1)·xᵢ⌋₊ ≤ m+1` and `⌈(m+1)·xᵢ⌉₊ ≤ m+1`.
  have ha0 : ∀ i, (0 : ℝ) ≤ ((m : ℝ) + 1) * x i := fun i => by
    have := hx0 i; positivity
  have ham : ∀ i, ((m : ℝ) + 1) * x i ≤ ((m + 1 : ℕ) : ℝ) := fun i => by
    calc ((m : ℝ) + 1) * x i ≤ ((m : ℝ) + 1) * 1 := by gcongr; exact hx1 i
      _ = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hfloor_le : ∀ i, ⌊((m : ℝ) + 1) * x i⌋₊ ≤ m + 1 := fun i => by
    simpa using Nat.floor_le_of_le (ham i)
  have hceil_le : ∀ i, ⌈((m : ℝ) + 1) * x i⌉₊ ≤ m + 1 := fun i => Nat.ceil_le.mpr (ham i)
  refine ⟨floorIndex m x, ceilIndex m x, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · -- `⌊(m+1)·xᵢ⌋₊ / (m+1) ≤ x i`
    simp only [gridPoint, floorIndex, Fin.val_mk, min_eq_left (hfloor_le i)]
    rw [div_le_iff₀ hmR]
    calc (⌊((m : ℝ) + 1) * x i⌋₊ : ℝ) ≤ ((m : ℝ) + 1) * x i := Nat.floor_le (ha0 i)
      _ = x i * (m + 1) := by ring
  · -- `x i ≤ ⌈(m+1)·xᵢ⌉₊ / (m+1)`
    simp only [gridPoint, ceilIndex, Fin.val_mk, min_eq_left (hceil_le i)]
    rw [le_div_iff₀ hmR]
    calc x i * ((m : ℝ) + 1) = ((m : ℝ) + 1) * x i := by ring
      _ ≤ (⌈((m : ℝ) + 1) * x i⌉₊ : ℝ) := Nat.le_ceil _
  · -- gap: `(⌈(m+1)·xᵢ⌉₊ - ⌊(m+1)·xᵢ⌋₊) / (m+1) ≤ 1 / (m+1)`
    simp only [gridPoint, ceilIndex, floorIndex, Fin.val_mk,
      min_eq_left (hfloor_le i), min_eq_left (hceil_le i)]
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hmR]
    have : (⌈((m : ℝ) + 1) * x i⌉₊ : ℝ) ≤ (⌊((m : ℝ) + 1) * x i⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one (((m : ℝ) + 1) * x i)
    linarith

end UniversalApproximation.Monotone
