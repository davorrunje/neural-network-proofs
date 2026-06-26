import Mathlib

/-!
# Riesz–Kantorovich decomposition (order-bounded dual of a vector lattice)
Intended Mathlib home: `Mathlib/Analysis/Order/` (confirm with maintainers).
-/

namespace RieszKantorovich

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

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

end RieszKantorovich
