/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UnitInterval

/-!
# Unit-interval clamp (Runje et al.)

The fixed bounded output activation `clamp01`, used by the partial-monotone construction — a
secondary result of the Deep Constrained Monotonic Neural Networks development of Runje et al. It
clamps a real into `[0,1]`; baked into `PartMonoNet.toFun` (and its deep-core counterpart
`DeepPartMonoNet.toFun`) so the embedding value fed to the monotone network always lies in the
unit cube.
-/

namespace UniversalApproximation.Runje

/-- Clamp a real into the unit interval `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- `clamp01` is nonnegative. -/
lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

/-- `clamp01` is at most `1`. -/
lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

/-- `clamp01` takes values in `[0,1]`. -/
lemma clamp01_mem_Icc (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clamp01_nonneg t, clamp01_le_one t⟩

/-- `clamp01` is the identity on `[0,1]`. -/
lemma clamp01_eq_self {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right h.2, max_eq_right h.1]

/-- `clamp01` is continuous. -/
lemma clamp01_continuous : Continuous clamp01 := by
  unfold clamp01; fun_prop

/-- `clamp01` is `1`-Lipschitz: it does not increase distances. -/
lemma abs_clamp01_sub_le (a b : ℝ) : |clamp01 a - clamp01 b| ≤ |a - b| := by
  -- `clamp01 = ↑(Set.projIcc 0 1 _)` definitionally, so this is `Set.abs_projIcc_sub_projIcc`.
  simp only [clamp01]
  exact Set.abs_projIcc_sub_projIcc (by norm_num)

end UniversalApproximation.Runje
