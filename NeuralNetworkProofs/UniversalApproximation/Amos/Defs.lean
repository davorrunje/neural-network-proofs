/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Fully input-convex neural networks — definitions (Amos et al.)

The fully-input-convex network (FICNN) of Amos–Xu–Kolter (2017): each layer propagates a hidden
vector `z` with nonnegative weights and re-injects the original input `y` through an unconstrained
skip, `z ↦ act (Wz z + Wy y + b)`. With `Wz ≥ 0` and a convex, nondecreasing activation the
denotation is convex in `y` (proved in `Amos/Convex.lean`). The convex sibling of the constrained-
monotone developments.
-/

namespace UniversalApproximation.Amos

/-- One FICNN layer, input dim `d`, hidden `a → b`: `z ↦ act (Wz z + Wy y + b)` componentwise. -/
structure ICNNLayer (d a b : ℕ) where
  /-- Propagation weights (nonnegative for convexity). -/
  Wz : Matrix (Fin b) (Fin a) ℝ
  /-- Input-skip weights (unconstrained). -/
  Wy : Matrix (Fin b) (Fin d) ℝ
  /-- Layer bias. -/
  bias : Fin b → ℝ
  /-- Activation (convex + nondecreasing for convexity). -/
  act : ℝ → ℝ

/-- Layer denotation on hidden `z` and original input `y`. -/
noncomputable def ICNNLayer.toFun {d a b} (L : ICNNLayer d a b)
    (z : Fin a → ℝ) (y : Fin d → ℝ) : Fin b → ℝ :=
  fun j => L.act ((L.Wz.mulVec z) j + (L.Wy.mulVec y) j + L.bias j)

/-- The convexity-inducing constraints: `Wz` nonnegative, `act` convex and nondecreasing. -/
def ICNNLayer.IsConvex {d a b} (L : ICNNLayer d a b) : Prop :=
  (∀ i j, 0 ≤ L.Wz i j) ∧ Monotone L.act ∧ ConvexOn ℝ Set.univ L.act

/-- A FICNN: a chain of layers threading the original input `y`. -/
inductive ICNN (d : ℕ) : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ICNN d a a
  | cons : {a b c : ℕ} → ICNNLayer d a b → ICNN d b c → ICNN d a c

/-- Evaluate the chain: `y` fed to every layer, `z` threaded. -/
noncomputable def ICNN.eval {d} :
    {a b : ℕ} → ICNN d a b → (Fin d → ℝ) → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil, _, z => z
  | _, _, .cons L rest, y, z => rest.eval y (L.toFun z y)

/-- Every layer satisfies the convexity constraints. -/
def ICNN.IsConvex {d} : {a b : ℕ} → ICNN d a b → Prop
  | _, _, .nil => True
  | _, _, .cons L rest => L.IsConvex ∧ rest.IsConvex

/-- Scalar FICNN denotation: start from a width-0 hidden vector (so the first layer is the
input-affine `act (Wy y + b)`), end at width 1. -/
noncomputable def ICNN.toFun {d} (N : ICNN d 0 1) (y : Fin d → ℝ) : ℝ :=
  N.eval y (0 : Fin 0 → ℝ) 0

end UniversalApproximation.Amos
