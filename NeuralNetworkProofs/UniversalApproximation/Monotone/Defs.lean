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

* `heaviside` — the threshold (Heaviside) gate.
* `ThreshStack` — a stack of threshold layers, with denotation `toFun`, `depth`, `IsMonotone`.
* `ThreshStack.toOrderHom` — a monotone stack bundled as an order homomorphism.
* `MonoNet` — a monotone threshold network (threshold stack + non-negative linear read-out).
* `MonoNet.monotone_toFun` — a monotone network denotes a monotone function.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- Threshold (Heaviside) gate: `1` if `0 ≤ z`, else `0`. -/
noncomputable def heaviside (z : ℝ) : ℝ := if 0 ≤ z then 1 else 0

/-- The threshold gate is monotone. -/
theorem heaviside_monotone : Monotone heaviside := by
  intro a b h
  unfold heaviside
  split_ifs with ha hb hb
  · rfl
  · exact absurd (le_trans ha h) hb
  · exact zero_le_one
  · rfl

/-- The threshold gate is non-negative. -/
theorem heaviside_nonneg (z : ℝ) : 0 ≤ heaviside z := by
  unfold heaviside; split_ifs <;> norm_num

/-- The threshold gate is at most `1`. -/
theorem heaviside_le_one (z : ℝ) : heaviside z ≤ 1 := by
  unfold heaviside; split_ifs <;> norm_num

/-- A single threshold layer with non-negative weights denotes a monotone function. The affine
map `x ↦ W.mulVec x + c` is monotone in `x` because each output coordinate is a dot product of a
non-negative weight row with `x`, and the pointwise `heaviside` gate is monotone. -/
theorem layer_toFun_monotone {a b : ℕ} (L : NeuralNetwork.Layer a b)
    (hW : ∀ i j, 0 ≤ L.W i j) : Monotone (L.toFun heaviside) := by
  intro x y hxy i
  apply heaviside_monotone
  gcongr
  exact dotProduct_le_dotProduct_of_nonneg_left hxy (fun j => hW i j)

/-- A stack of threshold layers `Fin a → ℝ ⟶ Fin b → ℝ`; each `cons` layer applies the affine
map `W.mulVec x + c` then `heaviside` pointwise (`NeuralNetwork.Layer.toFun heaviside`). -/
inductive ThreshStack : ℕ → ℕ → Type
  | nil (n : ℕ) : ThreshStack n n
  | cons {a b c : ℕ} (L : NeuralNetwork.Layer a b) (rest : ThreshStack b c) : ThreshStack a c

/-- Denotation of a threshold stack. -/
noncomputable def ThreshStack.toFun : {a b : ℕ} → ThreshStack a b → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil _, x => x
  | _, _, .cons L rest, x => rest.toFun (L.toFun heaviside x)

/-- Number of threshold layers. -/
def ThreshStack.depth : {a b : ℕ} → ThreshStack a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.depth + 1

/-- All layer weights are non-negative. -/
def ThreshStack.IsMonotone : {a b : ℕ} → ThreshStack a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons L rest => (∀ i j, 0 ≤ L.W i j) ∧ rest.IsMonotone

/-- A monotone threshold stack bundled as an order homomorphism, built by induction over the
stack with `OrderHom.comp`: `nil` is the identity and `cons L rest` is `rest`'s order
homomorphism composed after the monotone single-layer map `L.toFun heaviside`. -/
noncomputable def ThreshStack.toOrderHom : {a b : ℕ} → (S : ThreshStack a b) →
    S.IsMonotone → ((Fin a → ℝ) →o (Fin b → ℝ))
  | _, _, .nil _, _ => OrderHom.id
  | _, _, .cons L rest, h =>
      (rest.toOrderHom h.2).comp ⟨L.toFun heaviside, layer_toFun_monotone L h.1⟩

/-- The bundled order homomorphism of a monotone stack has the stack denotation `toFun` as its
underlying function. -/
theorem ThreshStack.coe_toOrderHom : {a b : ℕ} → (S : ThreshStack a b) → (h : S.IsMonotone) →
    ⇑(S.toOrderHom h) = S.toFun
  | _, _, .nil _, _ => rfl
  | _, _, .cons L rest, h => by
    ext x
    simp only [ThreshStack.toOrderHom, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
      ThreshStack.toFun]
    rw [rest.coe_toOrderHom h.2]

/-- A monotone threshold stack denotes a monotone function. -/
theorem ThreshStack.monotone_toFun {a b : ℕ} (S : ThreshStack a b)
    (h : S.IsMonotone) : Monotone S.toFun :=
  S.coe_toOrderHom h ▸ (S.toOrderHom h).monotone'

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

/-- A monotone network denotes a monotone function: the hidden stack is monotone (as an order
homomorphism) and the read-out is a non-negatively weighted sum plus a constant. -/
theorem MonoNet.monotone_toFun {d} (N : MonoNet d) (h : N.IsMonotone) : Monotone N.toFun := by
  intro x y hxy
  have hstack : Monotone N.stack.toFun := N.stack.monotone_toFun h.1
  unfold MonoNet.toFun
  gcongr with i _
  · exact h.2 i
  · exact hstack hxy i

end UniversalApproximation.Monotone
