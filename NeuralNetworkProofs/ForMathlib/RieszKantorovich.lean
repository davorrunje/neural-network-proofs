/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Riesz–Kantorovich decomposition (order-bounded dual of a vector lattice)

Intended Mathlib home: `Mathlib/Analysis/Order/` (confirm with maintainers).
-/


namespace RieszKantorovich

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

omit [Module ℝ E] [PosSMulMono ℝ E] in
/-- Riesz decomposition property: a positive element below a sum splits along the sum. -/
theorem riesz_decomp {x y z : E} (hz : 0 ≤ z) (hzxy : z ≤ x + y) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ a b, z = a + b ∧ 0 ≤ a ∧ a ≤ x ∧ 0 ≤ b ∧ b ≤ y := by
  refine ⟨z ⊓ x, z - z ⊓ x, ?_, ?_, ?_, ?_, ?_⟩
  · rw [add_sub_cancel]
  · exact le_inf hz hx
  · exact inf_le_right
  · rw [sub_nonneg]; exact inf_le_left
  · rw [sub_le_iff_le_add, add_inf]
    exact le_inf (le_add_of_nonneg_left hy) (by rwa [add_comm])

/-- A linear functional is *order bounded* when, for every positive `f`, the set of values it
takes on the order interval `[0, f]` is bounded above. -/
def IsOrderBounded (L : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ f : E, 0 ≤ f → BddAbove {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}

/-- The Riesz–Kantorovich supremum: the value of `L` maximized over the order interval `[0, f]`. -/
noncomputable def rkSup (L : E →ₗ[ℝ] ℝ) (f : E) : ℝ :=
  sSup {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- The defining set of `rkSup L f` is always nonempty (witnessed by `g = 0`). -/
theorem rkSup_set_nonempty (L : E →ₗ[ℝ] ℝ) {f : E} (hf : 0 ≤ f) :
    {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}.Nonempty :=
  ⟨L 0, 0, le_refl 0, hf, rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- Every value of `L` on the order interval `[0, f]` is below `rkSup L f`. -/
theorem le_rkSup (L : E →ₗ[ℝ] ℝ) {f g : E} (hL : IsOrderBounded L)
    (hf : 0 ≤ f) (hg0 : 0 ≤ g) (hgf : g ≤ f) : L g ≤ rkSup L f :=
  le_csSup (hL f hf) ⟨g, hg0, hgf, rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- `rkSup L f` is nonnegative for positive `f`. -/
theorem rkSup_nonneg (L : E →ₗ[ℝ] ℝ) {f : E} (hL : IsOrderBounded L) (hf : 0 ≤ f) :
    0 ≤ rkSup L f := by
  have h := le_rkSup L hL hf (le_refl (0 : E)) hf
  rwa [map_zero] at h

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- Universal property: `rkSup L f` is below any upper bound for `L` on `[0, f]`. -/
theorem rkSup_le (L : E →ₗ[ℝ] ℝ) {f : E} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ g, 0 ≤ g → g ≤ f → L g ≤ c) : rkSup L f ≤ c :=
  csSup_le (rkSup_set_nonempty L hf) (fun _ ⟨g, hg0, hgf, hgy⟩ => hgy ▸ h g hg0 hgf)

-- `rkSup_add` helpers --------------------------------------------------------

omit [PosSMulMono ℝ E] in
private lemma rkSup_add_le (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    rkSup L (f₁ + f₂) ≤ rkSup L f₁ + rkSup L f₂ := by
  refine rkSup_le L (add_nonneg hf₁ hf₂) ?_
  intro g hg0 hgf
  obtain ⟨a, b, hgab, ha0, haf, hb0, hbf⟩ := riesz_decomp hg0 hgf hf₁ hf₂
  rw [hgab, map_add]
  exact add_le_add (le_rkSup L hL hf₁ ha0 haf) (le_rkSup L hL hf₂ hb0 hbf)

omit [PosSMulMono ℝ E] in
private lemma rkSup_add_ge (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    rkSup L f₁ + rkSup L f₂ ≤ rkSup L (f₁ + f₂) := by
  rw [← le_sub_iff_add_le]
  refine rkSup_le L hf₁ ?_
  intro g₁ hg₁0 hg₁f
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  refine rkSup_le L hf₂ ?_
  intro g₂ hg₂0 hg₂f
  rw [le_sub_iff_add_le, add_comm, ← map_add]
  exact le_rkSup L hL (add_nonneg hf₁ hf₂) (add_nonneg hg₁0 hg₂0)
    (add_le_add hg₁f hg₂f)

omit [PosSMulMono ℝ E] in
/-- `rkSup L` is additive on the positive cone. -/
theorem rkSup_add (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    rkSup L (f₁ + f₂) = rkSup L f₁ + rkSup L f₂ :=
  le_antisymm (rkSup_add_le L hL hf₁ hf₂) (rkSup_add_ge L hL hf₁ hf₂)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- `rkSup L` vanishes at `0`. -/
theorem rkSup_zero (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : rkSup L (0 : E) = 0 := by
  apply le_antisymm
  · refine rkSup_le L (le_refl 0) ?_
    intro g hg0 hgf
    rw [le_antisymm hgf hg0, map_zero]
  · exact rkSup_nonneg L hL (le_refl 0)

-- `rkSup_smul` helpers --------------------------------------------------------

omit [IsOrderedAddMonoid E] in
private lemma rkSup_smul_le (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hcpos : 0 < c)
    {f : E} (hf : 0 ≤ f) : rkSup L (c • f) ≤ c * rkSup L f := by
  have hc : 0 ≤ c := le_of_lt hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcf : (0 : E) ≤ c • f := smul_nonneg hc hf
  refine rkSup_le L hcf ?_
  intro g hg0 hgf
  set h := c⁻¹ • g with hh
  have hh0 : 0 ≤ h := smul_nonneg (le_of_lt (inv_pos.mpr hcpos)) hg0
  have hhf : h ≤ f := by
    have := smul_le_smul_of_nonneg_left hgf (le_of_lt (inv_pos.mpr hcpos))
    rwa [smul_smul, inv_mul_cancel₀ hcne, one_smul] at this
  have hgch : g = c • h := by rw [hh, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  rw [hgch, map_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (le_rkSup L hL hf hh0 hhf) hc

omit [IsOrderedAddMonoid E] in
private lemma rkSup_smul_ge (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hcpos : 0 < c)
    {f : E} (hf : 0 ≤ f) : c * rkSup L f ≤ rkSup L (c • f) := by
  have hc : 0 ≤ c := le_of_lt hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcf : (0 : E) ≤ c • f := smul_nonneg hc hf
  have key : rkSup L f ≤ c⁻¹ * rkSup L (c • f) := by
    refine rkSup_le L hf ?_
    intro g hg0 hgf
    have hcg0 : (0 : E) ≤ c • g := smul_nonneg hc hg0
    have hcgf : c • g ≤ c • f := smul_le_smul_of_nonneg_left hgf hc
    have h1 : L (c • g) ≤ rkSup L (c • f) := le_rkSup L hL hcf hcg0 hcgf
    rw [map_smul, smul_eq_mul, ← le_div_iff₀' hcpos, div_eq_inv_mul] at h1
    exact h1
  have := mul_le_mul_of_nonneg_left key hc
  rwa [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at this

omit [IsOrderedAddMonoid E] in
/-- `rkSup L` is positively homogeneous on the positive cone. -/
theorem rkSup_smul (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hc : 0 ≤ c)
    {f : E} (hf : 0 ≤ f) : rkSup L (c • f) = c * rkSup L f := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- `c = 0`: both sides are `0`.
    subst hc0
    rw [zero_smul, zero_mul, rkSup_zero L hL]
  · -- `c > 0`: bijection `g ↦ c • g` between order intervals `[0, f]` and `[0, c • f]`.
    exact le_antisymm (rkSup_smul_le L hL hcpos hf) (rkSup_smul_ge L hL hcpos hf)

omit [IsOrderedAddMonoid E] in
/-- For a nonnegative scalar, `•` distributes over the lattice join. -/
theorem smul_sup_of_nonneg {c : ℝ} (hc : 0 ≤ c) (a b : E) :
    c • (a ⊔ b) = (c • a) ⊔ (c • b) := by
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0; simp
  · apply le_antisymm
    · have ha : a ≤ c⁻¹ • ((c • a) ⊔ (c • b)) := by
        have h2 := smul_le_smul_of_nonneg_left (le_sup_left (a := c • a) (b := c • b))
          (le_of_lt (inv_pos.mpr hpos))
        rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at h2
      have hb : b ≤ c⁻¹ • ((c • a) ⊔ (c • b)) := by
        have h2 := smul_le_smul_of_nonneg_left (le_sup_right (a := c • a) (b := c • b))
          (le_of_lt (inv_pos.mpr hpos))
        rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] at h2
      have := smul_le_smul_of_nonneg_left (sup_le ha hb) (le_of_lt hpos)
      rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul] at this
    · exact sup_le (smul_le_smul_of_nonneg_left le_sup_left hc)
        (smul_le_smul_of_nonneg_left le_sup_right hc)

omit [IsOrderedAddMonoid E] in
/-- For a nonnegative scalar, `•` commutes with the positive part. -/
theorem smul_posPart_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁺ = c • x⁺ := by
  rw [posPart_def, posPart_def, smul_sup_of_nonneg hc, smul_zero]

omit [IsOrderedAddMonoid E] in
/-- For a nonnegative scalar, `•` commutes with the negative part. -/
theorem smul_negPart_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁻ = c • x⁻ := by
  rw [negPart_def, negPart_def, ← smul_neg, smul_sup_of_nonneg hc, smul_zero]

-- `Lpos` helpers --------------------------------------------------------------

omit [Module ℝ E] [PosSMulMono ℝ E] in
private lemma Lpos_add_id (x y : E) :
    (x + y)⁺ + x⁻ + y⁻ = (x + y)⁻ + x⁺ + y⁺ := by
  have hsub : (x + y)⁺ - (x + y)⁻ = (x⁺ - x⁻) + (y⁺ - y⁻) := by
    rw [posPart_sub_negPart, posPart_sub_negPart, posPart_sub_negPart]
  linear_combination (norm := abel) hsub

omit [PosSMulMono ℝ E] in
private lemma Lpos_rkSup_add_left (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) (x y : E) :
    rkSup L ((x + y)⁺ + x⁻ + y⁻) =
      rkSup L (x + y)⁺ + rkSup L x⁻ + rkSup L y⁻ := by
  rw [rkSup_add L hL (add_nonneg (posPart_nonneg _) (negPart_nonneg _)) (negPart_nonneg _),
    rkSup_add L hL (posPart_nonneg _) (negPart_nonneg _)]

omit [PosSMulMono ℝ E] in
private lemma Lpos_rkSup_add_right (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) (x y : E) :
    rkSup L ((x + y)⁻ + x⁺ + y⁺) =
      rkSup L (x + y)⁻ + rkSup L x⁺ + rkSup L y⁺ := by
  rw [rkSup_add L hL (add_nonneg (negPart_nonneg _) (posPart_nonneg _)) (posPart_nonneg _),
    rkSup_add L hL (negPart_nonneg _) (posPart_nonneg _)]

omit [PosSMulMono ℝ E] in
private lemma Lpos_map_add (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) (x y : E) :
    rkSup L (x + y)⁺ - rkSup L (x + y)⁻ =
      (rkSup L x⁺ - rkSup L x⁻) + (rkSup L y⁺ - rkSup L y⁻) := by
  have hL1 := Lpos_rkSup_add_left L hL x y
  have hR1 := Lpos_rkSup_add_right L hL x y
  rw [Lpos_add_id x y] at hL1
  rw [hL1] at hR1
  linarith [hR1]

omit [IsOrderedAddMonoid E] in
private lemma Lpos_map_smul_neg (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hc : c < 0)
    (x : E) :
    rkSup L (c • x)⁺ - rkSup L (c • x)⁻ = c * (rkSup L x⁺ - rkSup L x⁻) := by
  have hnc : 0 ≤ -c := by linarith
  have hp : (c • x)⁺ = (-c) • x⁻ := by
    rw [show c • x = -((-c) • x) by rw [neg_smul, neg_neg], posPart_neg,
      smul_negPart_of_nonneg hnc]
  have hn : (c • x)⁻ = (-c) • x⁺ := by
    rw [show c • x = -((-c) • x) by rw [neg_smul, neg_neg], negPart_neg,
      smul_posPart_of_nonneg hnc]
  rw [hp, hn, rkSup_smul L hL hnc (negPart_nonneg _), rkSup_smul L hL hnc (posPart_nonneg _)]
  ring

/-- The Riesz–Kantorovich positive part of an order-bounded functional `L`: the linear functional
`x ↦ rkSup L x⁺ - rkSup L x⁻`. It dominates both `L` and `0` on the positive cone. -/
noncomputable def Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : E →ₗ[ℝ] ℝ where
  toFun x := rkSup L x⁺ - rkSup L x⁻
  map_add' x y := Lpos_map_add L hL x y
  map_smul' c x := by
    change rkSup L (c • x)⁺ - rkSup L (c • x)⁻ = (RingHom.id ℝ) c * (rkSup L x⁺ - rkSup L x⁻)
    rw [RingHom.id_apply]
    rcases le_or_gt 0 c with hc | hc
    · -- `c ≥ 0`: positive and negative parts scale directly.
      rw [smul_posPart_of_nonneg hc, smul_negPart_of_nonneg hc,
        rkSup_smul L hL hc (posPart_nonneg _), rkSup_smul L hL hc (negPart_nonneg _)]
      ring
    · -- `c < 0`: scaling swaps the positive and negative parts.
      exact Lpos_map_smul_neg L hL hc x

/-- On the positive cone, `Lpos L hL` agrees with `rkSup L`. -/
theorem Lpos_apply_of_nonneg (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    Lpos L hL f = rkSup L f := by
  change rkSup L f⁺ - rkSup L f⁻ = rkSup L f
  rw [posPart_eq_self.mpr hf, negPart_eq_zero.mpr hf, rkSup_zero L hL, sub_zero]

/-- `Lpos L hL` is nonnegative on the positive cone. -/
theorem Lpos_nonneg (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    0 ≤ Lpos L hL f := by
  rw [Lpos_apply_of_nonneg L hL hf]
  exact rkSup_nonneg L hL hf

/-- On the positive cone, `Lpos L hL` dominates `L`. -/
theorem le_Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    L f ≤ Lpos L hL f := by
  rw [Lpos_apply_of_nonneg L hL hf]
  exact le_rkSup L hL hf hf (le_refl f)

/-- **Riesz–Kantorovich decomposition.** Every order-bounded linear functional on a vector lattice
is the difference of two functionals that are nonnegative on the positive cone. -/
theorem exists_positive_decomposition (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) :
    ∃ Lp Lm : E →ₗ[ℝ] ℝ,
      (∀ f, 0 ≤ f → 0 ≤ Lp f) ∧ (∀ f, 0 ≤ f → 0 ≤ Lm f) ∧ ∀ x, L x = Lp x - Lm x := by
  refine ⟨Lpos L hL, Lpos L hL - L, fun f hf => Lpos_nonneg L hL hf, fun f hf => ?_, fun x => ?_⟩
  · rw [LinearMap.sub_apply]
    exact sub_nonneg.mpr (le_Lpos L hL hf)
  · rw [LinearMap.sub_apply, sub_sub_cancel]

/-! ### Closure of `IsOrderBounded` under the module operations -/

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- The zero functional is order bounded. -/
theorem IsOrderBounded.zero : IsOrderBounded (0 : E →ₗ[ℝ] ℝ) := by
  intro f _
  exact ⟨0, by rintro y ⟨g, _, _, rfl⟩; simp⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- A sum of order-bounded functionals is order bounded. -/
theorem IsOrderBounded.add {L M : E →ₗ[ℝ] ℝ} (hL : IsOrderBounded L) (hM : IsOrderBounded M) :
    IsOrderBounded (L + M) := by
  intro f hf
  obtain ⟨a, ha⟩ := hL f hf
  obtain ⟨b, hb⟩ := hM f hf
  refine ⟨a + b, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  rw [LinearMap.add_apply]
  exact add_le_add (ha ⟨g, hg0, hgf, rfl⟩) (hb ⟨g, hg0, hgf, rfl⟩)

omit [PosSMulMono ℝ E] in
/-- The negation of an order-bounded functional is order bounded. -/
theorem IsOrderBounded.neg {L : E →ₗ[ℝ] ℝ} (hL : IsOrderBounded L) : IsOrderBounded (-L) := by
  intro f hf
  obtain ⟨a, ha⟩ := hL f hf
  refine ⟨a - L f, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  rw [LinearMap.neg_apply]
  have hmem : L (f - g) ≤ a := ha ⟨f - g, sub_nonneg.mpr hgf, sub_le_self f hg0, rfl⟩
  rw [map_sub] at hmem
  linarith

omit [PosSMulMono ℝ E] in
/-- A difference of order-bounded functionals is order bounded. -/
theorem IsOrderBounded.sub {L M : E →ₗ[ℝ] ℝ} (hL : IsOrderBounded L) (hM : IsOrderBounded M) :
    IsOrderBounded (L - M) := by
  rw [sub_eq_add_neg]; exact hL.add hM.neg

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- A nonnegative scalar multiple of an order-bounded functional is order bounded. -/
theorem IsOrderBounded.smul_nonneg {c : ℝ} (hc : 0 ≤ c) {L : E →ₗ[ℝ] ℝ}
    (hL : IsOrderBounded L) : IsOrderBounded (c • L) := by
  intro f hf
  obtain ⟨a, ha⟩ := hL f hf
  refine ⟨c * a, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  rw [LinearMap.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (ha ⟨g, hg0, hgf, rfl⟩) hc

omit [PosSMulMono ℝ E] in
/-- Any scalar multiple of an order-bounded functional is order bounded. -/
theorem IsOrderBounded.smul (c : ℝ) {L : E →ₗ[ℝ] ℝ} (hL : IsOrderBounded L) :
    IsOrderBounded (c • L) := by
  rcases le_or_gt 0 c with hc | hc
  · exact hL.smul_nonneg hc
  · rw [show c • L = -((-c) • L) by rw [neg_smul, neg_neg]]
    exact (hL.smul_nonneg (by linarith)).neg

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- `rkSup L` is monotone on the positive cone. -/
theorem rkSup_mono (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₁₂ : f₁ ≤ f₂) : rkSup L f₁ ≤ rkSup L f₂ := by
  apply csSup_le_csSup (hL f₂ (le_trans hf₁ hf₁₂)) (rkSup_set_nonempty L hf₁)
  rintro y ⟨g, hg0, hgf, rfl⟩
  exact ⟨g, hg0, le_trans hgf hf₁₂, rfl⟩

/-- `Lpos L hL` is itself order bounded. -/
theorem Lpos_isOrderBounded (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) :
    IsOrderBounded (Lpos L hL) := by
  intro f hf
  refine ⟨rkSup L f, ?_⟩
  rintro y ⟨g, hg0, hgf, rfl⟩
  rw [Lpos_apply_of_nonneg L hL hg0]
  exact rkSup_mono L hL hg0 hgf

/-! ### The order-bounded dual as a vector lattice -/

/-- The order-bounded linear functionals form a submodule of the algebraic dual. -/
def orderBoundedDualSubmodule : Submodule ℝ (E →ₗ[ℝ] ℝ) where
  carrier := {L | IsOrderBounded L}
  add_mem' := IsOrderBounded.add
  zero_mem' := IsOrderBounded.zero
  smul_mem' := fun c _ hL => IsOrderBounded.smul c hL

/-- The **order-bounded dual** of `E`: the order-bounded linear functionals `E →ₗ[ℝ] ℝ`,
equipped with their natural vector-lattice structure. -/
abbrev OrderBoundedDual (E : Type*) [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [Module ℝ E] [PosSMulMono ℝ E] : Type _ :=
  ↥(orderBoundedDualSubmodule (E := E))

namespace OrderBoundedDual

/-- The pointwise-on-the-cone order: `L ≤ M` iff `L f ≤ M f` for every positive `f`. -/
instance instPartialOrder : PartialOrder (OrderBoundedDual E) where
  le L M := ∀ f : E, 0 ≤ f → L.1 f ≤ M.1 f
  le_refl _ _ _ := le_refl _
  le_trans _ _ _ hLM hMN f hf := le_trans (hLM f hf) (hMN f hf)
  le_antisymm L M hLM hML := by
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    rw [show x = x⁺ - x⁻ from (posPart_sub_negPart x).symm, map_sub, map_sub,
      le_antisymm (hLM x⁺ (posPart_nonneg x)) (hML x⁺ (posPart_nonneg x)),
      le_antisymm (hLM x⁻ (negPart_nonneg x)) (hML x⁻ (negPart_nonneg x))]

theorem le_def {L M : OrderBoundedDual E} : L ≤ M ↔ ∀ f : E, 0 ≤ f → L.1 f ≤ M.1 f := Iff.rfl

/-- The Riesz–Kantorovich join `L ⊔ M = L + Lpos (M - L)`. -/
noncomputable instance instSup : Max (OrderBoundedDual E) where
  max L M := ⟨L.1 + Lpos (M.1 - L.1) (M.2.sub L.2),
    L.2.add (Lpos_isOrderBounded _ _)⟩

theorem sup_apply (L M : OrderBoundedDual E) (f : E) :
    (L ⊔ M).1 f = L.1 f + Lpos (M.1 - L.1) (M.2.sub L.2) f := rfl

-- `instSemilatticeSup` helpers ------------------------------------------------

private lemma rk_le_sup_left (L M : OrderBoundedDual E) (f : E) (hf : 0 ≤ f) :
    L.1 f ≤ (L ⊔ M).1 f := by
  rw [sup_apply]
  have := Lpos_nonneg (M.1 - L.1) (M.2.sub L.2) hf
  linarith

private lemma rk_le_sup_right (L M : OrderBoundedDual E) (f : E) (hf : 0 ≤ f) :
    M.1 f ≤ (L ⊔ M).1 f := by
  rw [sup_apply]
  have h := le_Lpos (M.1 - L.1) (M.2.sub L.2) hf
  rw [LinearMap.sub_apply] at h
  linarith

private lemma rk_sup_le (L M N : OrderBoundedDual E) (hLN : L ≤ N) (hMN : M ≤ N)
    (f : E) (hf : 0 ≤ f) : (L ⊔ M).1 f ≤ N.1 f := by
  rw [sup_apply, ← le_sub_iff_add_le']
  rw [Lpos_apply_of_nonneg (M.1 - L.1) (M.2.sub L.2) hf]
  refine rkSup_le (M.1 - L.1) hf (fun g hg0 hgf => ?_)
  rw [LinearMap.sub_apply]
  have h1 : M.1 g - L.1 g ≤ N.1 g - L.1 g := by linarith [hMN g hg0]
  have h2 : N.1 g - L.1 g ≤ N.1 f - L.1 f := by
    have hpos : 0 ≤ N.1 (f - g) - L.1 (f - g) := by
      have := hLN (f - g) (sub_nonneg.mpr hgf)
      linarith
    rw [map_sub, map_sub] at hpos
    linarith
  linarith

noncomputable instance instSemilatticeSup : SemilatticeSup (OrderBoundedDual E) where
  sup := max
  le_sup_left L M f hf := rk_le_sup_left L M f hf
  le_sup_right L M f hf := rk_le_sup_right L M f hf
  sup_le L M N hLN hMN f hf := rk_sup_le L M N hLN hMN f hf

/-- Negation reverses the order. -/
theorem neg_le_neg_iff {L M : OrderBoundedDual E} : (-L) ≤ (-M) ↔ M ≤ L := by
  constructor
  · intro h f hf
    have h := h f hf
    change M.1 f ≤ L.1 f
    have e : ((-L) : OrderBoundedDual E).1 f = -(L.1 f) := rfl
    have e' : ((-M) : OrderBoundedDual E).1 f = -(M.1 f) := rfl
    rw [e, e'] at h
    linarith
  · intro h f hf
    have h := h f hf
    change ((-L) : OrderBoundedDual E).1 f ≤ ((-M) : OrderBoundedDual E).1 f
    have e : ((-L) : OrderBoundedDual E).1 f = -(L.1 f) := rfl
    have e' : ((-M) : OrderBoundedDual E).1 f = -(M.1 f) := rfl
    rw [e, e']
    linarith

/-- The Riesz–Kantorovich meet, obtained by duality from the join:
`L ⊓ M = -((-L) ⊔ (-M))`. -/
noncomputable instance instLattice : Lattice (OrderBoundedDual E) where
  __ := instSemilatticeSup
  inf L M := -((-L) ⊔ (-M))
  inf_le_left L M := by
    -- goal: -((-L) ⊔ (-M)) ≤ L
    rw [show L = -(-L) from (neg_neg L).symm, neg_le_neg_iff, neg_neg (-L)]
    exact le_sup_left
  inf_le_right L M := by
    rw [show M = -(-M) from (neg_neg M).symm, neg_le_neg_iff, neg_neg (-M)]
    exact le_sup_right
  le_inf L M N hLM hLN := by
    -- L ≤ -((-M) ⊔ (-N))  ↔  (-M) ⊔ (-N) ≤ -L
    rw [show L = -(-L) from (neg_neg L).symm, neg_le_neg_iff]
    refine sup_le ?_ ?_
    · rw [neg_le_neg_iff]; exact hLM
    · rw [neg_le_neg_iff]; exact hLN

end OrderBoundedDual
end RieszKantorovich
