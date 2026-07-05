/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.NeuralNetwork.Network
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Saturating

/-!
# Weight-sign ↔ saturation-side equivalence (Proposition 3.10)

This file formalizes the algebraic equivalence at the heart of Proposition 3.10 of the Sartor
et al. saturating-activation universal approximation development: a two consecutive layers with
**non-positive** weights and activation `σ` denote the same map as two consecutive layers with
**non-negative** weights and activation `reflect σ` (`reflect σ x = −σ(−x)`, see `Saturating`).

The driving fact is a single-layer identity. Flipping the sign of a layer's weights *and* bias
and swapping the activation from `σ` to `reflect σ` negates the layer's output:

  `(reflect σ)((−W).mulVec x + (−c)) i = −σ((W.mulVec x) i + c i) = −(L.toFun σ x) i`,

using `(reflect σ) z = −σ(−z)` and `−(−(W·x) + (−c)) = (W·x) + c`.

A single sign flip on the output of layer 1 is then absorbed by flipping the sign of layer 2's
weight matrix, so the composite of two `σ`-layers with negated data equals the composite of two
`reflect σ`-layers on the original data. Since the transformation sends non-positive weights to
non-negative weights (and back), this is exactly the weight-sign ↔ saturation-side trade of
Proposition 3.10, stated at the `Layer.toFun` denotation level for downstream reuse.

* `reflect_negLayer_toFun` — the single-layer identity (Proposition 3.10 core).
* `Layer.neg` — the sign-flip `(W, c) ↦ (−W, −c)` on a layer.
* `reflect_negLayer_eq_neg` — `Layer.neg` phrased over `Layer.neg` (packaged form).
* `prop_3_10_two_layer` — the two-layer composite equivalence (Proposition 3.10).
-/

namespace UniversalApproximation.Monotone

open NeuralNetwork

/-- The sign-flip of a layer: negate both the weight matrix and the bias, `(W, c) ↦ (−W, −c)`.
This is the transformation trading a non-positive-weight layer for a non-negative-weight one (and
back), used in Proposition 3.10 to swap the saturation side of the activation. -/
def Layer.neg {a b : ℕ} (L : Layer a b) : Layer a b where
  W := -L.W
  c := -L.c

@[simp] theorem Layer.neg_W {a b : ℕ} (L : Layer a b) : (Layer.neg L).W = -L.W := rfl

@[simp] theorem Layer.neg_c {a b : ℕ} (L : Layer a b) : (Layer.neg L).c = -L.c := rfl

/-- `Layer.neg` is an involution: negating the weights and bias twice restores the layer. -/
@[simp] theorem Layer.neg_neg {a b : ℕ} (L : Layer a b) : Layer.neg (Layer.neg L) = L := by
  cases L with
  | mk W c => simp only [Layer.neg, _root_.neg_neg]

/-- **Single-layer identity (Proposition 3.10 core).** Applying `reflect σ` to the sign-flipped
layer `(−W, −c)` negates the output of the original `σ`-layer:
`(reflect σ).toFun (Layer.neg L) x = −(σ.toFun L x)` pointwise. This is where the sign flip
`W ↦ −W`, `c ↦ −c` is absorbed by the reflected activation `reflect σ z = −σ(−z)`. -/
theorem reflect_negLayer_toFun {a b : ℕ} (L : Layer a b) (σ : ℝ → ℝ) (x : Fin a → ℝ) :
    (Layer.neg L).toFun (reflect σ) x = fun i => -(L.toFun σ x i) := by
  funext i
  simp only [Layer.toFun, Layer.neg_W, Layer.neg_c, reflect, Matrix.neg_mulVec,
    Pi.neg_apply, neg_add, _root_.neg_neg]

/-- Packaged form of `reflect_negLayer_toFun`: `(reflect σ)` on `Layer.neg L` is the pointwise
negation of `σ` on `L`. -/
theorem reflect_negLayer_eq_neg {a b : ℕ} (L : Layer a b) (σ : ℝ → ℝ) :
    (Layer.neg L).toFun (reflect σ) = fun x i => -(L.toFun σ x i) := by
  funext x
  exact reflect_negLayer_toFun L σ x

/-- Absorption law: applying a layer to a pointwise-negated input equals applying the
weight-negated layer to the original input. This cancels the sign flip emitted by layer 1 under
`reflect σ` (`reflect_negLayer_toFun`): for the second layer `M` and activation `τ`,
`M.toFun τ (fun i => −(y i)) = ({ W := −M.W, c := M.c }).toFun τ y`. Only `M`'s weights are
negated (its bias is unchanged), matching the composite in `prop_3_10_two_layer`. -/
theorem negWeights_toFun {b c : ℕ} (M : Layer b c) (τ : ℝ → ℝ) (y : Fin b → ℝ) :
    M.toFun τ (fun i => -(y i))
      = ({ W := -M.W, c := M.c } : Layer b c).toFun τ y := by
  funext i
  simp only [Layer.toFun, Matrix.neg_mulVec, Pi.neg_apply]
  have hmul : M.W.mulVec (fun i => -(y i)) = -(M.W.mulVec y) := by
    rw [← Matrix.mulVec_neg]
    congr 1
  simp only [hmul, Pi.neg_apply]

/-- **Proposition 3.10 (two-layer equivalence).** A two-layer segment with activation `σ`, whose
first layer is the sign-flipped `Layer.neg L₁` (weights `−W₁`, so *non-positive* when `W₁ ≥ 0`)
and whose second layer has weights `−M.W`, denotes the same map as the two-layer segment with
activation `reflect σ`, first layer `Layer.neg L₁` and second layer the *original* `M` (weights
`M.W`, so *non-negative* when `M.W ≥ 0`). The sign flip emitted by layer 1 under `reflect σ`
(`reflect_negLayer_toFun`) is absorbed by negating layer 2's weight matrix (`negWeights_toFun`).

Concretely, with `L₁ : Layer a b`, `M : Layer b c` and input `x`:

  `M.toFun (reflect σ) ((Layer.neg L₁).toFun (reflect σ) x)`
    `= ({ W := -M.W, c := M.c }).toFun (reflect σ) (L₁.toFun σ x)`.

The right-hand side is a genuine two-layer composite; both sides are the second layer applied to
the first, so this is the composite denotation equivalence Task 6 can chain into an `ActStack`. -/
theorem prop_3_10_two_layer {a b c : ℕ} (L₁ : Layer a b) (M : Layer b c) (σ : ℝ → ℝ)
    (x : Fin a → ℝ) :
    M.toFun (reflect σ) ((Layer.neg L₁).toFun (reflect σ) x)
      = ({ W := -M.W, c := M.c } : Layer b c).toFun (reflect σ) (L₁.toFun σ x) := by
  rw [reflect_negLayer_toFun L₁ σ x, negWeights_toFun M (reflect σ) (L₁.toFun σ x)]

end UniversalApproximation.Monotone
