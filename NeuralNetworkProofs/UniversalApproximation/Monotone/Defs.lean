/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic
import NeuralNetworkProofs.NeuralNetwork.Network

/-!
# Monotone activation networks: model and monotonicity

This file defines the monotone neural-network model used in the formalization of the
Mikulincer–Reichman universal approximation result for monotone neural networks
(arXiv:2207.05275, Result 1), and proves that a network with non-negative weights and monotone
activations denotes a monotone function.

The hidden stack is generalized so that each layer carries its own activation `σ : ℝ → ℝ`.
The threshold (Heaviside) construction of the Mikulincer–Reichman model is recovered as the
special case where every layer uses `heaviside` (see `ActStack.threshold`).

* `heaviside` — the threshold (Heaviside) gate.
* `ActStack` — a stack of activation layers, with denotation `toFun`, `depth`, `IsMonotone`.
* `ActStack.threshold` — the threshold specialization: a stack using `heaviside` at every layer.
* `ActStack.toOrderHom` — a monotone stack bundled as an order homomorphism.
* `MonoNet` — a monotone network (a monotone-activation stack + non-negative linear read-out).
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

/-- A single layer with non-negative weights and a monotone activation `σ` denotes a monotone
function. The affine map `x ↦ W.mulVec x + c` is monotone in `x` because each output coordinate
is a dot product of a non-negative weight row with `x`, and the pointwise `σ` gate is monotone. -/
theorem layer_toFun_monotone {a b : ℕ} (L : NeuralNetwork.Layer a b) {σ : ℝ → ℝ}
    (hσ : Monotone σ) (hW : ∀ i j, 0 ≤ L.W i j) : Monotone (L.toFun σ) := by
  intro x y hxy i
  apply hσ
  gcongr
  exact dotProduct_le_dotProduct_of_nonneg_left hxy (fun j => hW i j)

/-- A stack of activation layers `Fin a → ℝ ⟶ Fin b → ℝ`; each `cons` layer carries an activation
`σ : ℝ → ℝ` and applies the affine map `W.mulVec x + c` then `σ` pointwise
(`NeuralNetwork.Layer.toFun σ`). -/
inductive ActStack : ℕ → ℕ → Type
  | nil (n : ℕ) : ActStack n n
  | cons {a b c : ℕ} (L : NeuralNetwork.Layer a b) (σ : ℝ → ℝ) (rest : ActStack b c) :
      ActStack a c

/-- Denotation of an activation stack: each `cons` layer applies its own activation `σ`. -/
noncomputable def ActStack.toFun : {a b : ℕ} → ActStack a b → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil _, x => x
  | _, _, .cons L σ rest, x => rest.toFun (L.toFun σ x)

/-- Number of activation layers. -/
def ActStack.depth : {a b : ℕ} → ActStack a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => rest.depth + 1

/-- Every layer has non-negative weights and a monotone activation. -/
def ActStack.IsMonotone : {a b : ℕ} → ActStack a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons L σ rest => (Monotone σ ∧ ∀ i j, 0 ≤ L.W i j) ∧ rest.IsMonotone

/-- Every layer has non-negative weights (independent of the activations). This is the residual
obligation for a threshold-specialized stack, whose activations are uniformly `heaviside` and
hence automatically monotone. -/
def ActStack.WeightsNonneg : {a b : ℕ} → ActStack a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons L _ rest => (∀ i j, 0 ≤ L.W i j) ∧ rest.WeightsNonneg

/-- The threshold specialization: rebuild a stack using `heaviside` as the activation at every
layer, preserving the weights and biases. This recovers the Mikulincer–Reichman threshold model
as a `cons`-chain whose per-layer activation is uniformly `heaviside`. -/
noncomputable def ActStack.threshold : {a b : ℕ} → ActStack a b → ActStack a b
  | _, _, .nil n => .nil n
  | _, _, .cons L _ rest => .cons L heaviside rest.threshold

/-- The threshold specialization has the same per-layer weights as the original stack, so it
inherits the `WeightsNonneg` predicate. -/
theorem ActStack.threshold_weightsNonneg : {a b : ℕ} → (S : ActStack a b) →
    S.WeightsNonneg → S.threshold.WeightsNonneg
  | _, _, .nil _, _ => trivial
  | _, _, .cons _ _ rest, hW => ⟨hW.1, rest.threshold_weightsNonneg hW.2⟩

/-- A threshold-specialized stack is `IsMonotone` as soon as its weights are non-negative: each
layer's activation is `heaviside`, which discharges the per-layer `Monotone` obligation via
`heaviside_monotone`. -/
theorem ActStack.threshold_isMonotone : {a b : ℕ} → (S : ActStack a b) →
    S.WeightsNonneg → S.threshold.IsMonotone
  | _, _, .nil _, _ => trivial
  | _, _, .cons _ _ rest, hW =>
      ⟨⟨heaviside_monotone, hW.1⟩, rest.threshold_isMonotone hW.2⟩

/-- A monotone activation stack bundled as an order homomorphism, built by induction over the
stack with `OrderHom.comp`: `nil` is the identity and `cons L σ rest` is `rest`'s order
homomorphism composed after the monotone single-layer map `L.toFun σ`. -/
noncomputable def ActStack.toOrderHom : {a b : ℕ} → (S : ActStack a b) →
    S.IsMonotone → ((Fin a → ℝ) →o (Fin b → ℝ))
  | _, _, .nil _, _ => OrderHom.id
  | _, _, .cons L σ rest, h =>
      (rest.toOrderHom h.2).comp ⟨L.toFun σ, layer_toFun_monotone L h.1.1 h.1.2⟩

/-- The bundled order homomorphism of a monotone stack has the stack denotation `toFun` as its
underlying function. -/
theorem ActStack.coe_toOrderHom : {a b : ℕ} → (S : ActStack a b) → (h : S.IsMonotone) →
    ⇑(S.toOrderHom h) = S.toFun
  | _, _, .nil _, _ => rfl
  | _, _, .cons L σ rest, h => by
    ext x
    simp only [ActStack.toOrderHom, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
      ActStack.toFun]
    rw [rest.coe_toOrderHom h.2]

/-- A monotone activation stack denotes a monotone function. -/
theorem ActStack.monotone_toFun {a b : ℕ} (S : ActStack a b)
    (h : S.IsMonotone) : Monotone S.toFun :=
  S.coe_toOrderHom h ▸ (S.toOrderHom h).monotone'

/-- A monotone network: a monotone-activation hidden stack + a non-negative linear read-out. -/
structure MonoNet (d : ℕ) where
  /-- The width of the stack's output. -/
  width : ℕ
  /-- The hidden activation stack. -/
  stack : ActStack d width
  /-- The read-out weights. -/
  readW : Fin width → ℝ
  /-- The read-out bias. -/
  readBias : ℝ

/-- Network denotation: `∑ i, readW i * (stack output)_i + readBias`. -/
noncomputable def MonoNet.toFun {d} (N : MonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, N.readW i * N.stack.toFun x i) + N.readBias

/-- Total depth: hidden layers plus the read-out layer. -/
def MonoNet.depth {d} (N : MonoNet d) : ℕ := N.stack.depth + 1

/-- Monotone network: the hidden stack is monotone (non-negative weights and monotone
activations) and the read-out weights are non-negative. -/
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
