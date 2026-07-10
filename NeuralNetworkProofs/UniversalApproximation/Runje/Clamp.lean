/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Unit-interval clamp (Runje et al.)

The fixed bounded output activation `clamp01` used by the partial-monotone architecture of
Runje et al. It clamps a real into `[0,1]`; baked into `PartMonoNet.toFun` so the embedding
value fed to the monotone network always lies in the unit cube.
-/

namespace UniversalApproximation.Runje

/-- Clamp a real into the unit interval `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma clamp01_mem_Icc (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clamp01_nonneg t, clamp01_le_one t⟩

lemma clamp01_eq_self {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right h.2, max_eq_right h.1]

lemma clamp01_continuous : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma abs_clamp01_sub_le (a b : ℝ) : |clamp01 a - clamp01 b| ≤ |a - b| := by
  unfold clamp01
  simp only [max_comm 0 (min 1 a), max_comm 0 (min 1 b)]
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  rw [min_comm 1 a, min_comm 1 b]
  exact abs_inf_sub_inf_le_abs a b 1

end UniversalApproximation.Runje
