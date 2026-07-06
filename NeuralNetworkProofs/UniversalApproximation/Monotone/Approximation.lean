/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Interpolation
import NeuralNetworkProofs.UniversalApproximation.Monotone.Grid

/-!
# Monotone universal approximation (Theorem 2)

This file proves the approximation half of the Mikulincer–Reichman universal approximation result
for monotone neural networks (arXiv:2207.05275, Result 1): every continuous, monotone `f` on the
unit cube `Set.Icc (0 : Fin d → ℝ) 1` is uniformly `ε`-approximated by a monotone threshold network
of depth `4`.

The proof samples `f` on a uniform grid fine enough (by uniform continuity of `f` on the compact
cube) that adjacent grid values differ by at most `ε`, interpolates the sampled dataset exactly with
`monotone_interpolation`, and sandwiches every cube point between its grid neighbours: both `N x`
and `f x` land in an interval of `f`-width at most `ε`.

* `monotone_approximation` — the headline.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- On the compact unit cube, a `ContinuousOn` function is uniformly continuous: for `ε > 0` there
is `δ > 0` such that any two cube points within (sup-metric) distance `δ` have `f`-values within
`ε`.  Extracted so the main proof only manipulates the resulting `δ`. -/
private theorem exists_delta_uniform {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : Fin d → ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Set.Icc (0 : Fin d → ℝ) 1, ∀ b ∈ Set.Icc (0 : Fin d → ℝ) 1,
      dist a b ≤ δ → |f a - f b| ≤ ε := by
  have hcpt : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  have huc : UniformContinuousOn f (Set.Icc (0 : Fin d → ℝ) 1) :=
    hcpt.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨δ / 2, by positivity, fun a ha b hb hab => ?_⟩
  have hlt : dist a b < δ := lt_of_le_of_lt hab (by linarith)
  have := hδ' a ha b hb hlt
  rw [Real.dist_eq] at this
  exact le_of_lt this

/-- **Monotone universal approximation (Theorem 2).**  Every function `f` that is continuous and
monotone (along the coordinatewise order) on the unit cube `Set.Icc (0 : Fin d → ℝ) 1` can be
uniformly `ε`-approximated on the cube by a monotone threshold network of depth `4`: for every
`ε > 0` there is a monotone `MonoNet d` of depth `4` whose denotation is within `ε` of `f` at every
cube point.  This is the approximation half of Mikulincer–Reichman (arXiv:2207.05275) Result 1. -/
theorem monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |N.toFun x - f x| ≤ ε := by
  -- bridge the frozen longhand monotonicity hypothesis to `MonotoneOn`
  have hmonoOn : MonotoneOn f (Set.Icc (0 : Fin d → ℝ) 1) :=
    fun a ha b hb hab => hmono ha hb hab
  -- uniform continuity gives a modulus `δ`
  obtain ⟨δ, hδ, hunif⟩ := exists_delta_uniform f hf hε
  -- choose a resolution `m` with grid gap `1 / (m + 1) ≤ δ`
  obtain ⟨m, hmδ0⟩ := exists_nat_one_div_lt hδ
  have hmδ : (1 : ℝ) / (m + 1) ≤ δ := le_of_lt hmδ0
  -- interpolate the grid dataset exactly
  obtain ⟨N, hNmono, hNdepth, hNeq⟩ :=
    monotone_interpolation (gridEnum (d := d) m) (fun j => f (gridEnum m j))
      (fun a b hab => gridEnum_monotone_dataset m f hmonoOn a b hab)
      (gridEnum_injective m)
  refine ⟨N, hNmono, hNdepth, fun x hx => ?_⟩
  -- monotone network denotation
  have hNmt : Monotone N.toFun := N.monotone_toFun hNmono
  -- grid points are hit exactly by `N`: `N (gridPoint m k) = f (gridPoint m k)`
  have hgrid : ∀ k : Fin d → Fin (m + 2),
      N.toFun (gridPoint m k) = f (gridPoint m k) := by
    intro k
    have hj := hNeq ((Fintype.equivFin (Fin d → Fin (m + 2))) k)
    simp only [gridEnum, Equiv.symm_apply_apply] at hj
    exact hj
  -- the sandwiching neighbours
  obtain ⟨kl, kr, hxl, hxr, hgap⟩ := grid_neighbors m x hx
  set xl := gridPoint m kl with hxldef
  set xr := gridPoint m kr with hxrdef
  have hxlmem : xl ∈ Set.Icc (0 : Fin d → ℝ) 1 := gridPoint_mem_Icc m kl
  have hxrmem : xr ∈ Set.Icc (0 : Fin d → ℝ) 1 := gridPoint_mem_Icc m kr
  -- `N` sandwiched between the grid values
  have hNl : f xl ≤ N.toFun x := by rw [← hgrid kl]; exact hNmt hxl
  have hNr : N.toFun x ≤ f xr := by rw [← hgrid kr]; exact hNmt hxr
  -- `f` sandwiched between the grid values (monotonicity of `f`)
  have hfl : f xl ≤ f x := hmono hxlmem hx hxl
  have hfr : f x ≤ f xr := hmono hx hxrmem hxr
  -- the interval `[f xl, f xr]` has width at most `ε`
  have hxlr : xl ≤ xr := le_trans hxl hxr
  have hdist : dist xr xl ≤ 1 / (m + 1) := by
    apply dist_le_of_coord (by positivity)
    intro i
    have hle : xl i ≤ xr i := hxlr i
    rw [abs_of_nonneg (by linarith [hle])]
    exact hgap i
  have hwidth : |f xr - f xl| ≤ ε := hunif xr hxrmem xl hxlmem (le_trans hdist hmδ)
  -- both `N x` and `f x` lie in `[f xl, f xr]`, whose width is `≤ ε`
  have hfxl_le_fxr : f xl ≤ f xr := le_trans hfl hfr
  rw [abs_of_nonneg (by linarith [hfl, hfxl_le_fxr])] at hwidth
  rw [abs_le]
  constructor <;> linarith [hNl, hNr, hfl, hfr, hwidth]

end UniversalApproximation.Monotone
