import Mathlib

/-!
# Riesz–Kantorovich decomposition (order-bounded dual of a vector lattice)
Intended Mathlib home: `Mathlib/Analysis/Order/` (confirm with maintainers).
-/

namespace RieszKantorovich

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

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

/-- The defining set of `rkSup L f` is always nonempty (witnessed by `g = 0`). -/
theorem rkSup_set_nonempty (L : E →ₗ[ℝ] ℝ) {f : E} (hf : 0 ≤ f) :
    {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}.Nonempty :=
  ⟨L 0, 0, le_refl 0, hf, rfl⟩

/-- Every value of `L` on the order interval `[0, f]` is below `rkSup L f`. -/
theorem le_rkSup (L : E →ₗ[ℝ] ℝ) {f g : E} (hL : IsOrderBounded L)
    (hf : 0 ≤ f) (hg0 : 0 ≤ g) (hgf : g ≤ f) : L g ≤ rkSup L f :=
  le_csSup (hL f hf) ⟨g, hg0, hgf, rfl⟩

/-- `rkSup L f` is nonnegative for positive `f`. -/
theorem rkSup_nonneg (L : E →ₗ[ℝ] ℝ) {f : E} (hL : IsOrderBounded L) (hf : 0 ≤ f) :
    0 ≤ rkSup L f := by
  have h := le_rkSup L hL hf (le_refl (0 : E)) hf
  rwa [map_zero] at h

/-- Universal property: `rkSup L f` is below any upper bound for `L` on `[0, f]`. -/
theorem rkSup_le (L : E →ₗ[ℝ] ℝ) {f : E} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ g, 0 ≤ g → g ≤ f → L g ≤ c) : rkSup L f ≤ c :=
  csSup_le (rkSup_set_nonempty L hf) (fun _ ⟨g, hg0, hgf, hgy⟩ => hgy ▸ h g hg0 hgf)

/-- `rkSup L` is additive on the positive cone. -/
theorem rkSup_add (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    rkSup L (f₁ + f₂) = rkSup L f₁ + rkSup L f₂ := by
  apply le_antisymm
  · -- (≤): split a positive `g ≤ f₁ + f₂` via Riesz decomposition
    refine rkSup_le L (add_nonneg hf₁ hf₂) ?_
    intro g hg0 hgf
    obtain ⟨a, b, hgab, ha0, haf, hb0, hbf⟩ := riesz_decomp hg0 hgf hf₁ hf₂
    rw [hgab, map_add]
    exact add_le_add (le_rkSup L hL hf₁ ha0 haf) (le_rkSup L hL hf₂ hb0 hbf)
  · -- (≥): combine the two sups
    rw [← le_sub_iff_add_le]
    refine rkSup_le L hf₁ ?_
    intro g₁ hg₁0 hg₁f
    rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
    refine rkSup_le L hf₂ ?_
    intro g₂ hg₂0 hg₂f
    rw [le_sub_iff_add_le, add_comm, ← map_add]
    exact le_rkSup L hL (add_nonneg hf₁ hf₂) (add_nonneg hg₁0 hg₂0)
      (add_le_add hg₁f hg₂f)

/-- `rkSup L` vanishes at `0`. -/
theorem rkSup_zero (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : rkSup L (0 : E) = 0 := by
  apply le_antisymm
  · refine rkSup_le L (le_refl 0) ?_
    intro g hg0 hgf
    rw [le_antisymm hgf hg0, map_zero]
  · exact rkSup_nonneg L hL (le_refl 0)

/-- `rkSup L` is positively homogeneous on the positive cone. -/
theorem rkSup_smul (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hc : 0 ≤ c)
    {f : E} (hf : 0 ≤ f) : rkSup L (c • f) = c * rkSup L f := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- `c = 0`: both sides are `0`.
    subst hc0
    rw [zero_smul, zero_mul, rkSup_zero L hL]
  · -- `c > 0`: bijection `g ↦ c • g` between the order intervals `[0, f]` and `[0, c • f]`.
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hcf : (0 : E) ≤ c • f := smul_nonneg hc hf
    apply le_antisymm
    · -- `rkSup L (c • f) ≤ c * rkSup L f`
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
    · -- `c * rkSup L f ≤ rkSup L (c • f)`
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

/-- For a nonnegative scalar, `•` commutes with the positive part. -/
theorem smul_posPart_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁺ = c • x⁺ := by
  rw [posPart_def, posPart_def, smul_sup_of_nonneg hc, smul_zero]

/-- For a nonnegative scalar, `•` commutes with the negative part. -/
theorem smul_negPart_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁻ = c • x⁻ := by
  rw [negPart_def, negPart_def, ← smul_neg, smul_sup_of_nonneg hc, smul_zero]

/-- The Riesz–Kantorovich positive part of an order-bounded functional `L`: the linear functional
`x ↦ rkSup L x⁺ - rkSup L x⁻`. It dominates both `L` and `0` on the positive cone. -/
noncomputable def Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : E →ₗ[ℝ] ℝ where
  toFun x := rkSup L x⁺ - rkSup L x⁻
  map_add' x y := by
    -- The lattice identity `(x + y)⁺ + x⁻ + y⁻ = (x + y)⁻ + x⁺ + y⁺` reduces additivity of
    -- `Lpos` to additivity of `rkSup` on the positive cone.
    have hid : (x + y)⁺ + x⁻ + y⁻ = (x + y)⁻ + x⁺ + y⁺ := by
      have hsub : (x + y)⁺ - (x + y)⁻ = (x⁺ - x⁻) + (y⁺ - y⁻) := by
        rw [posPart_sub_negPart, posPart_sub_negPart, posPart_sub_negPart]
      linear_combination (norm := abel) hsub
    have hL1 : rkSup L ((x + y)⁺ + x⁻ + y⁻) = rkSup L (x + y)⁺ + rkSup L x⁻ + rkSup L y⁻ := by
      rw [rkSup_add L hL (add_nonneg (posPart_nonneg _) (negPart_nonneg _)) (negPart_nonneg _),
        rkSup_add L hL (posPart_nonneg _) (negPart_nonneg _)]
    have hR1 : rkSup L ((x + y)⁻ + x⁺ + y⁺) = rkSup L (x + y)⁻ + rkSup L x⁺ + rkSup L y⁺ := by
      rw [rkSup_add L hL (add_nonneg (negPart_nonneg _) (posPart_nonneg _)) (posPart_nonneg _),
        rkSup_add L hL (negPart_nonneg _) (posPart_nonneg _)]
    rw [hid] at hL1
    rw [hL1] at hR1
    change rkSup L (x + y)⁺ - rkSup L (x + y)⁻
        = (rkSup L x⁺ - rkSup L x⁻) + (rkSup L y⁺ - rkSup L y⁻)
    linarith [hR1]
  map_smul' c x := by
    change rkSup L (c • x)⁺ - rkSup L (c • x)⁻ = (RingHom.id ℝ) c * (rkSup L x⁺ - rkSup L x⁻)
    rw [RingHom.id_apply]
    rcases le_or_gt 0 c with hc | hc
    · -- `c ≥ 0`: positive and negative parts scale directly.
      rw [smul_posPart_of_nonneg hc, smul_negPart_of_nonneg hc,
        rkSup_smul L hL hc (posPart_nonneg _), rkSup_smul L hL hc (negPart_nonneg _)]
      ring
    · -- `c < 0`: scaling swaps the positive and negative parts.
      have hnc : 0 ≤ -c := by linarith
      have hp : (c • x)⁺ = (-c) • x⁻ := by
        rw [show c • x = -((-c) • x) by rw [neg_smul, neg_neg], posPart_neg,
          smul_negPart_of_nonneg hnc]
      have hn : (c • x)⁻ = (-c) • x⁺ := by
        rw [show c • x = -((-c) • x) by rw [neg_smul, neg_neg], negPart_neg,
          smul_posPart_of_nonneg hnc]
      rw [hp, hn, rkSup_smul L hL hnc (negPart_nonneg _), rkSup_smul L hL hnc (posPart_nonneg _)]
      ring

/-- On the positive cone, `Lpos L hL` agrees with `rkSup L`. -/
theorem Lpos_apply_of_nonneg (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    Lpos L hL f = rkSup L f := by
  change rkSup L f⁺ - rkSup L f⁻ = rkSup L f
  rw [posPart_eq_self.mpr hf, negPart_eq_zero.mpr hf, rkSup_zero L hL, sub_zero]

end RieszKantorovich
