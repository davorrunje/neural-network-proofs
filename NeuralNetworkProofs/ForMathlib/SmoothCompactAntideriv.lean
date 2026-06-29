/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # A smooth compactly-supported function with vanishing moments is an iterated derivative
of a smooth compactly-supported function.
Intended Mathlib home: `Mathlib/Analysis/Calculus/BumpFunction/…` (confirm with maintainers). -/


namespace SmoothCompactAntideriv

open MeasureTheory

open scoped ContDiff

/-- The indefinite integral `∫_{-∞}^x h`. -/
noncomputable def antideriv (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Iic x, h y

/-- For `h` continuous and integrable on every `Iic`, the indefinite integral has derivative `h`. -/
private lemma hasDerivAt_antideriv {h : ℝ → ℝ} (hh : Continuous h)
    (hint : ∀ x : ℝ, IntegrableOn h (Set.Iic x)) (x : ℝ) :
    HasDerivAt (antideriv h) (h x) x := by
  have hfun : antideriv h = fun u => (∫ y in Set.Iic x, h y) + ∫ y in x..u, h y := by
    funext u
    rw [antideriv, ← intervalIntegral.integral_Iic_sub_Iic (hint x) (hint u)]; ring
  rw [hfun]
  have hftc : HasDerivAt (fun u => ∫ y in x..u, h y) (h x) x :=
    intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable x x)
      (hh.stronglyMeasurableAtFilter volume (nhds x)) hh.continuousAt
  have hsum := (hasDerivAt_const x (∫ y in Set.Iic x, h y)).add hftc
  rw [zero_add] at hsum
  exact hsum

/-- A continuous compactly-supported function is integrable on every `Set.Iic x`. -/
private lemma integrableOn_Iic_of_compactSupport {h : ℝ → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) (x : ℝ) : IntegrableOn h (Set.Iic x) := by
  exact (hh.integrable_of_hasCompactSupport hhc).integrableOn

/-- The indefinite integral of a `C^∞` compactly-supported `h` is `C^∞`. -/
private lemma contDiff_antideriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) : ContDiff ℝ ∞ (antideriv h) := by
  have hcont : Continuous h := hh.continuous
  have hint := integrableOn_Iic_of_compactSupport hcont hhc
  have hderiv : ∀ x, HasDerivAt (antideriv h) (h x) x :=
    fun x => hasDerivAt_antideriv hcont hint x
  have hdiff : Differentiable ℝ (antideriv h) := fun x => (hderiv x).differentiableAt
  have hderiveq : deriv (antideriv h) = h := by
    funext x; exact (hderiv x).deriv
  rw [contDiff_infty_iff_deriv]
  exact ⟨hdiff, by rw [hderiveq]; exact hh⟩

/-- If `h` is continuous, compactly supported and has integral zero, then its indefinite
integral is compactly supported. -/
private lemma hasCompactSupport_antideriv {h : ℝ → ℝ}
    (hhc : HasCompactSupport h) (hint : ∫ y, h y = 0) :
    HasCompactSupport (antideriv h) := by
  -- The support of `h` is bounded: `tsupport h ⊆ Icc a b`.
  obtain ⟨a, b, hab⟩ :=
    bddBelow_bddAbove_iff_subset_Icc.1 ⟨hhc.bddBelow, hhc.bddAbove⟩
  -- `h` vanishes off `Icc a b`.
  have hzero : ∀ y, y ∉ Set.Icc a b → h y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun hmem => hy (hab hmem))
  -- `antideriv h` vanishes off `Icc a b`, so it is compactly supported.
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := b))
  intro x hx
  rw [antideriv]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hlo | hhi
  · -- `x < a`: the integrand is zero on all of `Iic x`.
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact hzero y (fun hmem => absurd (le_trans hmem.1 hy) (not_le.2 hlo))
  · -- `x > b`: the integral over `Iic x` equals the full integral, which is zero.
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero, hint]
    intro y hy
    exact hzero y (fun hmem => hy (le_trans hmem.2 hhi.le))

/-- **Moment shift under integration.** Integration by parts relates the `j`-th moment of the
indefinite integral of a `C^∞` compactly-supported `h` to the `(j+1)`-th moment of `h`:
`(j+1) * ∫ y, y^j * (antideriv h) y = - ∫ y, y^(j+1) * h y`. -/
private lemma moment_antideriv {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (hint : ∫ y, h y = 0) (j : ℕ) :
    ((j : ℝ) + 1) * ∫ y, y ^ j * antideriv h y = - ∫ y, y ^ (j + 1) * h y := by
  have hcont : Continuous h := hh.continuous
  have hAcont : Continuous (antideriv h) := (contDiff_antideriv hh hhc).continuous
  have hAsupp : HasCompactSupport (antideriv h) := hasCompactSupport_antideriv hhc hint
  have hAderiv : ∀ x, HasDerivAt (antideriv h) (h x) x := fun x =>
    hasDerivAt_antideriv hcont (integrableOn_Iic_of_compactSupport hcont hhc) x
  have hpoly : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (j + 1)) (((j : ℝ) + 1) * x ^ j) x := by
    intro x; simpa using hasDerivAt_pow (j + 1) x
  -- Integrability of the three products appearing in integration by parts.
  have hcpoly : Continuous (fun y : ℝ => ((j : ℝ) + 1) * y ^ j) := by fun_prop
  have hcpoly1 : Continuous (fun y : ℝ => y ^ (j + 1)) := by fun_prop
  have hi_uv' : Integrable (antideriv h * fun y => ((j : ℝ) + 1) * y ^ j) :=
    ((hAcont.mul hcpoly).integrable_of_hasCompactSupport (hAsupp.mul_right))
  have hi_u'v : Integrable (h * fun y => y ^ (j + 1)) :=
    ((hcont.mul hcpoly1).integrable_of_hasCompactSupport (hhc.mul_right))
  have hi_uv : Integrable (antideriv h * fun y => y ^ (j + 1)) :=
    ((hAcont.mul hcpoly1).integrable_of_hasCompactSupport (hAsupp.mul_right))
  -- Integration by parts on (-∞, ∞).
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := antideriv h) (v := fun y => y ^ (j + 1)) (u' := h)
    (v' := fun y => ((j : ℝ) + 1) * y ^ j)
    (fun x _ => hAderiv x) (fun x _ => hpoly x) hi_uv' hi_u'v hi_uv
  rw [← MeasureTheory.integral_const_mul]
  simp only [show ∀ x : ℝ, ((j : ℝ) + 1) * (x ^ j * antideriv h x)
      = antideriv h x * (((j : ℝ) + 1) * x ^ j) from fun x => by ring,
    show ∀ x : ℝ, x ^ (j + 1) * h x = h x * x ^ (j + 1) from fun x => by ring]
  exact key

/-- If `g : ℝ → ℝ` is `C^∞`, compactly supported, and has vanishing moments
`∫ y, (y ^ j) * g y = 0` for all `j ≤ d`, then `g = iteratedDeriv (d+1) φ` for some `C^∞`
compactly-supported `φ`. (The `(d+1)`-fold indefinite integral `∫_{-∞}^x` stays compactly supported
exactly because the moments up to order `d` vanish.) -/
theorem exists_iteratedDeriv_eq_of_moments_zero {g : ℝ → ℝ} (d : ℕ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hmom : ∀ j ≤ d, ∫ y, (y ^ j) * g y = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ iteratedDeriv (d + 1) φ = g := by
  induction d generalizing g with
  | zero =>
    -- Single antiderivative: `∫ g = 0` makes it compactly supported, and its derivative is `g`.
    have hint : ∫ y, g y = 0 := by simpa using hmom 0 (le_refl 0)
    refine ⟨antideriv g, contDiff_antideriv hg hgc, hasCompactSupport_antideriv hgc hint, ?_⟩
    have hderiv : ∀ x, HasDerivAt (antideriv g) (g x) x := fun x =>
      hasDerivAt_antideriv hg.continuous
        (integrableOn_Iic_of_compactSupport hg.continuous hgc) x
    rw [iteratedDeriv_one]
    funext x; exact (hderiv x).deriv
  | succ d ih =>
    -- Step: `h := antideriv g` is `C^∞`, compactly supported, and its moments up to `d` vanish.
    have hint : ∫ y, g y = 0 := by simpa using hmom 0 (Nat.zero_le _)
    have hhsmooth : ContDiff ℝ ∞ (antideriv g) := contDiff_antideriv hg hgc
    have hhsupp : HasCompactSupport (antideriv g) := hasCompactSupport_antideriv hgc hint
    have hhmom : ∀ j ≤ d, ∫ y, y ^ j * antideriv g y = 0 := by
      intro j hj
      have hcoeff : ((j : ℝ) + 1) ≠ 0 := by positivity
      have hkey := moment_antideriv hg hgc hint j
      have hzero : ∫ y, y ^ (j + 1) * g y = 0 := hmom (j + 1) (by omega)
      rw [hzero, neg_zero] at hkey
      exact (mul_eq_zero.1 hkey).resolve_left hcoeff
    obtain ⟨ψ, hψsmooth, hψsupp, hψeq⟩ := ih (g := antideriv g) hhsmooth hhsupp hhmom
    refine ⟨ψ, hψsmooth, hψsupp, ?_⟩
    -- `iteratedDeriv (d+2) ψ = deriv (iteratedDeriv (d+1) ψ) = deriv (antideriv g) = g`.
    rw [iteratedDeriv_succ, hψeq]
    have hderiv : ∀ x, HasDerivAt (antideriv g) (g x) x := fun x =>
      hasDerivAt_antideriv hg.continuous
        (integrableOn_Iic_of_compactSupport hg.continuous hgc) x
    funext x; exact (hderiv x).deriv

end SmoothCompactAntideriv
