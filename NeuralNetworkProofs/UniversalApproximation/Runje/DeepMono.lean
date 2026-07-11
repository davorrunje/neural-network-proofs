/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.Residual
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Approximation

/-!
# Deep monotone networks + UAP by subsumption (Runje et al.)

A `DeepMonoNet` is a `ResNet` (deep residual body) plus a nonnegative-weight scalar read-out. It is
monotone (soundness). A shallow `MonoNet` embeds as a single-block `DeepMonoNet` preserving the
denotation exactly, so the depth-4 monotone UAP lifts verbatim: deep-residual monotone nets retain
universality, and no depth beyond 4 is required.

* `DeepMonoNet`, `DeepMonoNet.toFun`, `DeepMonoNet.IsMonotone`, `DeepMonoNet.monotone_toFun` — the
  deep-residual monotone network and its soundness.
* `MonoNet.toDeep`, `MonoNet.toDeep_toFun`, `MonoNet.toDeep_isMonotone`,
  `MonoNet.toDeep_single_block` — the single-block embedding, its exact denotation, monotonicity,
  and the witness that only one residual block over the depth-4 core is used.
* `deep_monotone_approximation` — **deep monotone UAP by exact subsumption of the shallow net.**
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.MikulincerReichman

/-- A deep monotone network: a residual body of any depth plus a nonnegative-weight scalar
read-out. -/
structure DeepMonoNet (d : ℕ) where
  /-- The width of the residual body's output. -/
  width : ℕ
  /-- The residual body. -/
  net : ResNet d width
  /-- The read-out weights. -/
  readW : Fin width → ℝ
  /-- The read-out bias. -/
  readBias : ℝ

/-- Network denotation: `∑ i, readW i * (residual body output)_i + readBias`. -/
noncomputable def DeepMonoNet.toFun {d} (D : DeepMonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, D.readW i * D.net.toFun x i) + D.readBias

/-- Monotone deep network: the residual body is monotone and the read-out weights are
nonnegative. -/
def DeepMonoNet.IsMonotone {d} (D : DeepMonoNet d) : Prop :=
  D.net.IsMonotone ∧ ∀ i, 0 ≤ D.readW i

/-- A monotone deep network denotes a monotone function: the residual body is monotone and the
read-out is a nonnegatively weighted sum plus a constant. -/
theorem DeepMonoNet.monotone_toFun {d} (D : DeepMonoNet d) (h : D.IsMonotone) :
    Monotone D.toFun := by
  intro x y hxy
  have hnet : Monotone D.net.toFun := D.net.monotone_toFun h.1
  simp only [DeepMonoNet.toFun]
  gcongr with i _
  · exact h.2 i
  · exact hnet hxy i

end UniversalApproximation.Runje

namespace UniversalApproximation.Monotone

open UniversalApproximation.Runje

/-- Embed a `MonoNet` as a single-block `DeepMonoNet`: one block with `gα = 0, gβ = 1`,
`skip = 0`, `F = the stack's monotone map`; the block computes the stack exactly. -/
noncomputable def MonoNet.toDeep {d} (N : MonoNet d) : DeepMonoNet d where
  width := N.width
  net := ResNet.cons { gα := 0, gβ := 1, skip := fun _ => 0, F := N.stack.toFun } ResNet.nil
  readW := N.readW
  readBias := N.readBias

/-- The embedding preserves the denotation exactly: the single residual block collapses to the
stack, so the deep read-out equals the shallow one. -/
theorem MonoNet.toDeep_toFun {d} (N : MonoNet d) : N.toDeep.toFun = N.toFun := by
  funext x
  simp only [MonoNet.toDeep, DeepMonoNet.toFun, MonoNet.toFun, ResNet.toFun, ResBlock.toFun,
    Runje.residual, zero_mul, zero_add, one_mul]
  rfl

/-- The embedding uses exactly one residual block over the depth-4 core. -/
theorem MonoNet.toDeep_single_block {d} (N : MonoNet d) :
    ∃ B : ResBlock d N.width, N.toDeep.net = ResNet.cons B ResNet.nil :=
  ⟨_, rfl⟩

/-- A monotone `MonoNet` embeds to a monotone `DeepMonoNet`: the single block has nonnegative
gates and monotone skip/sublayer, and the read-out weights are unchanged. -/
theorem MonoNet.toDeep_isMonotone {d} (N : MonoNet d) (h : N.IsMonotone) :
    N.toDeep.IsMonotone :=
  ⟨⟨⟨le_rfl, zero_le_one, monotone_const, N.stack.monotone_toFun h.1⟩, trivial⟩, h.2⟩

end UniversalApproximation.Monotone

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.MikulincerReichman

/-- **Deep UAP (retains UAP).** Every continuous, coordinatewise-monotone `f` on the unit cube is
uniformly `ε`-approximated by a monotone `DeepMonoNet`. The witness is a single residual block over
the existing depth-4 core (`MonoNet.toDeep_single_block`), so no depth beyond 4 is required. -/
theorem deep_monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : DeepMonoNet d, D.IsMonotone ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |D.toFun x - f x| ≤ ε := by
  obtain ⟨N, hNmono, _hdepth, hNapprox⟩ := monotone_approximation f hf hmono hε
  refine ⟨N.toDeep, N.toDeep_isMonotone hNmono, ?_⟩
  intro x hx
  rw [MonoNet.toDeep_toFun]
  exact hNapprox x hx

end UniversalApproximation.Runje
