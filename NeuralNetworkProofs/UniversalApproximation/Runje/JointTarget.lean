/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Constructions
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Joint monotone target for partial-monotone UAP (Runje et al.)

Part of the partial-monotone construction, a secondary result of the Deep Constrained Monotonic
Neural Networks development. `jointTarget g C w = (∑ i, (z-block of w) i * g i (x-block of w)) −
C`. When each `g i` is nonnegative and monotone in `x`, this is jointly coordinatewise monotone
and continuous on the unit cube — the target approximated by the monotone network in the UAP
proof.
-/

namespace UniversalApproximation.Runje

/-- The first `N`-coordinate block of a `Fin (N + dm)`-vector. -/
def zpart {N dm : ℕ} (w : Fin (N + dm) → ℝ) : Fin N → ℝ := fun i => w (Fin.castAdd dm i)

/-- The last `dm`-coordinate block of a `Fin (N + dm)`-vector. -/
def xpart {N dm : ℕ} (w : Fin (N + dm) → ℝ) : Fin dm → ℝ := fun j => w (Fin.natAdd N j)

@[simp] lemma zpart_append {N dm} (z : Fin N → ℝ) (x : Fin dm → ℝ) :
    zpart (Fin.append z x) = z := by
  funext i; simp [zpart, Fin.append_left]

@[simp] lemma xpart_append {N dm} (z : Fin N → ℝ) (x : Fin dm → ℝ) :
    xpart (Fin.append z x) = x := by
  funext j; simp [xpart, Fin.append_right]

/-- The `z`-block of a cube point lies in the `N`-cube. -/
private lemma zpart_mem_Icc {N dm : ℕ} {w : Fin (N + dm) → ℝ}
    (hw : w ∈ Set.Icc (0 : Fin (N + dm) → ℝ) 1) :
    zpart w ∈ Set.Icc (0 : Fin N → ℝ) 1 :=
  ⟨fun i => hw.1 (Fin.castAdd dm i), fun i => hw.2 (Fin.castAdd dm i)⟩

/-- The `x`-block of a cube point lies in the `dm`-cube. -/
private lemma xpart_mem_Icc {N dm : ℕ} {w : Fin (N + dm) → ℝ}
    (hw : w ∈ Set.Icc (0 : Fin (N + dm) → ℝ) 1) :
    xpart w ∈ Set.Icc (0 : Fin dm → ℝ) 1 :=
  ⟨fun j => hw.1 (Fin.natAdd N j), fun j => hw.2 (Fin.natAdd N j)⟩

private lemma continuous_xpart {N dm : ℕ} : Continuous (xpart (N := N) (dm := dm)) :=
  continuous_pi fun _ => continuous_apply _

/-- The jointly monotone target: a `z`-weighted sum of the `g i` evaluated at the `x`-block,
shifted by a constant `C`. -/
noncomputable def jointTarget {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (w : Fin (N + dm) → ℝ) : ℝ :=
  (∑ i, zpart w i * g i (xpart w)) - C

/-- **Joint monotonicity.** If each `g i` is nonnegative and monotone in `x` on the cube, then
`jointTarget g C` is coordinatewise monotone on the cube. -/
lemma jointTarget_mono {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (hg_nonneg : ∀ i, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1, 0 ≤ g i x)
    (hg_mono : ∀ i, ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
      y ∈ Set.Icc (0 : Fin dm → ℝ) 1 → x ≤ y → g i x ≤ g i y) :
    ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin (N+dm) → ℝ) 1 → b ∈ Set.Icc (0 : Fin (N+dm) → ℝ) 1 →
      a ≤ b → jointTarget g C a ≤ jointTarget g C b := by
  intro a b ha hb hab
  unfold jointTarget
  apply sub_le_sub_right
  apply Finset.sum_le_sum
  intro i _
  have hxa := xpart_mem_Icc ha
  have hxb := xpart_mem_Icc hb
  refine mul_le_mul (hab (Fin.castAdd dm i))
    (hg_mono i hxa hxb fun j => hab (Fin.natAdd N j))
    (hg_nonneg i (xpart a) hxa) (hb.1 (Fin.castAdd dm i))

/-- **Joint continuity.** If each `g i` is continuous on the `x`-cube, then `jointTarget g C`
is continuous on the cube. -/
lemma jointTarget_continuousOn {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (hg : ∀ i, ContinuousOn (g i) (Set.Icc (0 : Fin dm → ℝ) 1)) :
    ContinuousOn (jointTarget g C) (Set.Icc (0 : Fin (N+dm) → ℝ) 1) := by
  unfold jointTarget
  refine ContinuousOn.sub ?_ continuousOn_const
  apply continuousOn_finsetSum
  intro i _
  refine ContinuousOn.mul ?_ ?_
  · exact (continuous_apply (Fin.castAdd dm i)).continuousOn
  · exact (hg i).comp continuous_xpart.continuousOn fun w hw => xpart_mem_Icc hw

/-- **Per-coordinate difference bound.** Changing only the `z`-block moves `jointTarget` by at
most the weighted `ℓ¹` change of the `z`-coordinates. -/
lemma jointTarget_diff_bound {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (z z' : Fin N → ℝ) (x : Fin dm → ℝ) :
    |jointTarget g C (Fin.append z x) - jointTarget g C (Fin.append z' x)|
      ≤ ∑ i, |z i - z' i| * |g i x| := by
  simp only [jointTarget, zpart_append, xpart_append]
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [← sub_mul, abs_mul]

end UniversalApproximation.Runje
