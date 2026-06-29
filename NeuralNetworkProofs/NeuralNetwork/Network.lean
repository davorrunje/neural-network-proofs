/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib

/-!
# General feedforward neural networks

This file defines a general feedforward neural network as a chain of affine layers
followed by a pointwise activation, together with its denotation `toFun`, and proves
that the denotation is continuous whenever the activation is continuous.

* `Layer a b` — a single layer: a weight matrix and a bias vector.
* `Layer.toFun σ` — the layer's map: affine map `x ↦ W x + c` followed by pointwise `σ`.
* `Network` — a network with input/output arities and a denotation `toFun`.
* `Layer.continuous_toFun` — the layer denotation is continuous when `σ` is.

The continuity of `x ↦ W.mulVec x` (a finite-dimensional linear map) is obtained from
`Continuous.matrix_mulVec`.
-/

namespace NeuralNetwork

/-- A single feedforward layer from `Fin a` inputs to `Fin b` outputs:
a weight matrix `W` and a bias vector `c`. -/
structure Layer (a b : ℕ) where
  /-- The weight matrix. -/
  W : Matrix (Fin b) (Fin a) ℝ
  /-- The bias vector. -/
  c : Fin b → ℝ

/-- The denotation of a layer under activation `σ`: the affine map `x ↦ W.mulVec x + c`
followed by the pointwise application of `σ`. -/
def Layer.toFun (σ : ℝ → ℝ) {a b} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => σ ((L.W.mulVec x) i + L.c i)

/-- A feedforward neural network: input/output arities together with a denotation
`toFun : (Fin nIn → ℝ) → (Fin nOut → ℝ)`. -/
structure Network where
  /-- The input arity. -/
  nIn : ℕ
  /-- The output arity. -/
  nOut : ℕ
  /-- The denotation of the network. -/
  toFun : (Fin nIn → ℝ) → (Fin nOut → ℝ)

/-- If the activation `σ` is continuous, the layer denotation `L.toFun σ` is continuous. -/
theorem Layer.continuous_toFun (σ : ℝ → ℝ) (hσ : Continuous σ) {a b}
    (L : Layer a b) : Continuous (L.toFun σ) := by
  unfold Layer.toFun
  apply continuous_pi
  intro i
  apply hσ.comp
  apply Continuous.add
  · have hmul : Continuous (fun x : Fin a → ℝ => L.W.mulVec x) :=
      continuous_const.matrix_mulVec continuous_id
    exact (continuous_apply i).comp hmul
  · exact continuous_const

end NeuralNetwork
