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

end RieszKantorovich
