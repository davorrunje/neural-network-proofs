/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.NeuralNetwork.Network

/-!
# Monotone threshold networks: model and monotonicity

This file defines the monotone threshold-network model used in the formalization of the
Mikulincer–Reichman universal approximation result for monotone neural networks
(arXiv:2207.05275, Result 1), and proves that a network with non-negative weights denotes a
monotone function.

* `θ` — the threshold (Heaviside) gate.
* `ThreshStack` — a stack of threshold layers, with denotation `toFun`, `depth`, `IsMonotone`.
* `MonoNet` — a monotone threshold network (threshold stack + non-negative linear read-out).
* `MonoNet.monotone_toFun` — a monotone network denotes a monotone function.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- Threshold (Heaviside) gate: `1` if `0 ≤ z`, else `0`. -/
noncomputable def θ (z : ℝ) : ℝ := if 0 ≤ z then 1 else 0

/-- The threshold gate is monotone. -/
theorem θ_monotone : Monotone θ := by
  intro a b h
  unfold θ
  split_ifs with ha hb hb
  · rfl
  · exact absurd (le_trans ha h) hb
  · norm_num
  · rfl

/-- The threshold gate is non-negative. -/
theorem θ_nonneg (z : ℝ) : 0 ≤ θ z := by
  unfold θ; split_ifs <;> norm_num

/-- The threshold gate is at most `1`. -/
theorem θ_le_one (z : ℝ) : θ z ≤ 1 := by
  unfold θ; split_ifs <;> norm_num

/-- A stack of threshold layers `Fin a → ℝ ⟶ Fin b → ℝ`; each `cons` layer applies the affine
map `W.mulVec x + c` then `θ` pointwise (`NeuralNetwork.Layer.toFun θ`). -/
inductive ThreshStack : ℕ → ℕ → Type
  | nil (n : ℕ) : ThreshStack n n
  | cons {a b c : ℕ} (L : NeuralNetwork.Layer a b) (rest : ThreshStack b c) : ThreshStack a c

/-- Denotation of a threshold stack. -/
noncomputable def ThreshStack.toFun : {a b : ℕ} → ThreshStack a b → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil _, x => x
  | _, _, .cons L rest, x => rest.toFun (L.toFun θ x)

/-- Number of threshold layers. -/
def ThreshStack.depth : {a b : ℕ} → ThreshStack a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.depth + 1

/-- All layer weights are non-negative. -/
def ThreshStack.IsMonotone : {a b : ℕ} → ThreshStack a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons L rest => (∀ i j, 0 ≤ L.W i j) ∧ rest.IsMonotone

/-- A single threshold layer with non-negative weights denotes a monotone function. -/
theorem Layer.toFun_monotone {a b : ℕ} (L : NeuralNetwork.Layer a b)
    (hW : ∀ i j, 0 ≤ L.W i j) : Monotone (L.toFun θ) := by
  intro x y hxy i
  apply θ_monotone
  simp only [Matrix.mulVec, dotProduct]
  gcongr with j _
  · exact hW i j
  · exact hxy j

/-- A monotone threshold stack denotes a monotone function. -/
theorem ThreshStack.monotone_toFun : {a b : ℕ} → (S : ThreshStack a b) →
    S.IsMonotone → Monotone S.toFun
  | _, _, .nil _, _ => monotone_id
  | _, _, .cons L rest, h => by
    have hrest : Monotone rest.toFun := rest.monotone_toFun h.2
    have hL : Monotone (L.toFun θ) := Layer.toFun_monotone L h.1
    exact fun x y hxy => hrest (hL hxy)

/-- A monotone threshold network: a threshold hidden stack + a non-negative linear read-out. -/
structure MonoNet (d : ℕ) where
  /-- The width of the threshold stack's output. -/
  width : ℕ
  /-- The threshold hidden stack. -/
  stack : ThreshStack d width
  /-- The read-out weights. -/
  readW : Fin width → ℝ
  /-- The read-out bias. -/
  readBias : ℝ

/-- Network denotation: `∑ i, readW i * (stack output)_i + readBias`. -/
noncomputable def MonoNet.toFun {d} (N : MonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, N.readW i * N.stack.toFun x i) + N.readBias

/-- Total depth: threshold layers plus the read-out layer. -/
def MonoNet.depth {d} (N : MonoNet d) : ℕ := N.stack.depth + 1

/-- Monotone network: non-negative hidden weights and non-negative read-out weights. -/
def MonoNet.IsMonotone {d} (N : MonoNet d) : Prop :=
  N.stack.IsMonotone ∧ ∀ i, 0 ≤ N.readW i

/-- A monotone network denotes a monotone function. -/
theorem MonoNet.monotone_toFun {d} (N : MonoNet d) (h : N.IsMonotone) : Monotone N.toFun := by
  intro x y hxy
  have hstack : Monotone N.stack.toFun := N.stack.monotone_toFun h.1
  unfold MonoNet.toFun
  gcongr with i _
  · exact h.2 i
  · exact hstack hxy i

end UniversalApproximation.Monotone
