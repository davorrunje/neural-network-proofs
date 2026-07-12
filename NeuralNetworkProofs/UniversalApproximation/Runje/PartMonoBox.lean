/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation
import NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain

/-!
# Partial-monotone universal approximation on general box domains (Runje et al.)

`partial_monotone_approximation_box` generalizes the unit-cube `partial_monotone_approximation`
(a secondary result of the Deep Constrained Monotonic Neural Networks development) to an arbitrary
non-degenerate box `[aF, bF] × [aM, bM]`, by an affine change of variables: pull `f` back to the
unit cube, apply the cube theorem, and fold the rescalings into the network (the feature embedding
via `genSpanPi_comp_cubeOfBox`, the monotone block via `MonoNet.rescaleSuffix`).
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Leshno UniversalApproximation.Monotone

/-- **Partial-monotone universal approximation on a general box.** Every jointly continuous `f`,
coordinatewise monotone in its second (monotone) block on the box `[aF, bF] × [aM, bM]`, is
uniformly approximated within `ε` by a `PartMonoNet`. Reduced to the unit-cube
`partial_monotone_approximation` by the affine box↔cube rescalings of `BoxDomain.lean`. -/
theorem partial_monotone_approximation_box {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (aF bF : Fin df → ℝ) (haF : ∀ j, aF j < bF j)
    (aM bM : Fin dm → ℝ) (haM : ∀ j, aM j < bM j)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2) (Set.Icc aF bF ×ˢ Set.Icc aM bM))
    (hmono : ∀ u ∈ Set.Icc aF bF, ∀ ⦃x y⦄, x ∈ Set.Icc aM bM → y ∈ Set.Icc aM bM →
        x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc aF bF, ∀ x ∈ Set.Icc aM bM, |P.toFun u x - f u x| ≤ ε := by
  -- pull `f` back to the unit cube
  set ftil : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ :=
    fun u x => f (boxOfCube aF bF u) (boxOfCube aM bM x) with hftil
  -- the continuous change-of-variables map on the product cube
  have hcont : Continuous
      (fun p : (Fin df → ℝ) × (Fin dm → ℝ) =>
        ((boxOfCube aF bF p.1, boxOfCube aM bM p.2) : (Fin df → ℝ) × (Fin dm → ℝ))) :=
    ((continuous_boxOfCube aF bF).comp continuous_fst).prodMk
      ((continuous_boxOfCube aM bM).comp continuous_snd)
  have hmaps : Set.MapsTo
      (fun p : (Fin df → ℝ) × (Fin dm → ℝ) => (boxOfCube aF bF p.1, boxOfCube aM bM p.2))
      (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1)
      (Set.Icc aF bF ×ˢ Set.Icc aM bM) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Set.mem_prod.mpr ⟨boxOfCube_mem haF hp.1, boxOfCube_mem haM hp.2⟩
  have hcomp : (fun p : (Fin df → ℝ) × (Fin dm → ℝ) => ftil p.1 p.2)
      = (fun q : (Fin df → ℝ) × (Fin dm → ℝ) => f q.1 q.2) ∘
        (fun p => (boxOfCube aF bF p.1, boxOfCube aM bM p.2)) := by
    funext p; simp only [hftil, Function.comp_apply]
  have hftil_cont : ContinuousOn (fun p => ftil p.1 p.2)
      (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1) := by
    rw [hcomp]; exact hf.comp hcont.continuousOn hmaps
  have hftil_mono : ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1, ∀ ⦃x y⦄,
      x ∈ Set.Icc (0 : Fin dm → ℝ) 1 → y ∈ Set.Icc (0 : Fin dm → ℝ) 1 → x ≤ y →
      ftil u x ≤ ftil u y := by
    intro u hu x y hx hy hxy
    simp only [hftil]
    exact hmono (boxOfCube aF bF u) (boxOfCube_mem haF hu)
      (boxOfCube_mem haM hx) (boxOfCube_mem haM hy) (monotone_boxOfCube haM hxy)
  -- apply the unit-cube theorem
  obtain ⟨Pt, hPtmono, hPtemb, hPtapprox⟩ :=
    partial_monotone_approximation σ hσ hnp ftil hftil_cont hftil_mono hε
  -- coordinatewise rescaling of the monotone block
  set s : Fin dm → ℝ := fun j => 1 / (bM j - aM j) with hs
  set t : Fin dm → ℝ := fun j => -aM j / (bM j - aM j) with ht
  have hs_nonneg : ∀ j, 0 ≤ s j := by
    intro j; simp only [hs]
    exact div_nonneg zero_le_one (sub_pos.mpr (haM j)).le
  refine ⟨⟨Pt.embWidth, fun u => Pt.emb (cubeOfBox aF bF u), Pt.mono.rescaleSuffix s t⟩,
    Pt.mono.rescaleSuffix_isMonotone hPtmono hs_nonneg, fun i => ?_, ?_⟩
  · -- feature-embedding membership, closed under the affine precomposition
    exact genSpanPi_comp_cubeOfBox haF (hPtemb i)
  · -- the uniform bound, transported through the change of variables
    intro u hu x hx
    have hst : (fun j => s j * x j + t j) = cubeOfBox aM bM x := by
      funext j; simp only [hs, ht, cubeOfBox]
      have hne : bM j - aM j ≠ 0 := ne_of_gt (sub_pos.mpr (haM j))
      field_simp; ring
    have e1 : (⟨Pt.embWidth, fun u => Pt.emb (cubeOfBox aF bF u), Pt.mono.rescaleSuffix s t⟩
          : PartMonoNet df dm).toFun u x
        = Pt.toFun (cubeOfBox aF bF u) (cubeOfBox aM bM x) := by
      simp only [PartMonoNet.toFun]
      rw [MonoNet.rescaleSuffix_toFun, hst]
    have hftilval : ftil (cubeOfBox aF bF u) (cubeOfBox aM bM x) = f u x := by
      simp only [hftil, boxOfCube_cubeOfBox haF, boxOfCube_cubeOfBox haM]
    rw [e1, ← hftilval]
    exact hPtapprox (cubeOfBox aF bF u) (cubeOfBox_mem haF hu)
      (cubeOfBox aM bM x) (cubeOfBox_mem haM hx)

end UniversalApproximation.Runje
