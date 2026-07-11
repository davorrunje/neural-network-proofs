/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Residual monotone blocks and deep stacks (Runje et al.)

The residual/deep-monotone core of the deep-constrained-monotonic development. A residual block
`x ↦ g_α · skip(x) + g_β · F(x)` with nonnegative scalar gates and monotone `skip`, `F` is
monotone; a `ResNet` (a composition of such blocks, of *any* depth) is monotone. The concrete
`mononet` gates (`shiftedElu`, `scaledElu`) are strictly positive and the `exp`-projected skip
(`expSkip`) is monotone, so the concrete residual block satisfies these hypotheses.

* `residual`, `residual_monotone` — the abstract combinator and its monotonicity.
* `shiftedElu`/`scaledElu` (`…_pos`), `expSkip` (`expSkip_monotone`) — concrete gate/skip instances.
* `ResBlock`, `ResBlock.monotone_toFun` — a single residual block and its soundness.
* `ResNet`, `ResNet.monotone_toFun` — **soundness: a residual stack of any depth is monotone.**
-/

namespace UniversalApproximation.Runje

/-- Residual block map: positive-gated sum of a skip and a sublayer `F`. -/
def residual {a b : ℕ} (gα gβ : ℝ) (skip F : (Fin a → ℝ) → (Fin b → ℝ)) :
    (Fin a → ℝ) → (Fin b → ℝ) := fun x i => gα * skip x i + gβ * F x i

/-- A residual block with nonnegative gates over monotone `skip` and `F` is monotone. -/
theorem residual_monotone {a b : ℕ} {gα gβ : ℝ} {skip F : (Fin a → ℝ) → (Fin b → ℝ)}
    (hgα : 0 ≤ gα) (hgβ : 0 ≤ gβ) (hskip : Monotone skip) (hF : Monotone F) :
    Monotone (residual gα gβ skip F) := by
  intro x y hxy i
  have h1 := hskip hxy i
  have h2 := hF hxy i
  simp only [residual]
  gcongr

/-- Shifted ELU gate `mononet` uses: strictly positive, so usable as a nonnegative gate. -/
noncomputable def shiftedElu (r : ℝ) : ℝ := (if 0 < r then r else Real.exp r - 1) + 1

/-- Scaled ELU gate `mononet` uses: strictly positive for `0 < ε`. -/
noncomputable def scaledElu (ε r : ℝ) : ℝ := max r 0 + ε * Real.exp (min r 0 / ε)

/-- The `exp`-projected skip connection: `x ↦ (exp ∘ W).mulVec x`. -/
noncomputable def expSkip {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) := fun x => (W.map Real.exp).mulVec x

/-- The shifted ELU gate is strictly positive. -/
theorem shiftedElu_pos (r : ℝ) : 0 < shiftedElu r := by
  unfold shiftedElu
  split_ifs with h
  · linarith
  · have := Real.exp_pos r
    linarith

/-- The scaled ELU gate is strictly positive for a positive scale `ε`. -/
theorem scaledElu_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 < scaledElu ε r := by
  unfold scaledElu
  exact add_pos_of_nonneg_of_pos (le_max_right _ _) (mul_pos hε (Real.exp_pos _))

/-- The `exp`-projected skip connection is monotone: every entry `exp (W i j)` is nonnegative. -/
theorem expSkip_monotone {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) :
    Monotone (expSkip W) := by
  intro x y hxy i
  exact dotProduct_le_dotProduct_of_nonneg_left hxy (fun j => (Real.exp_pos _).le)

/-- A residual block: gates and the skip/sublayer maps. -/
structure ResBlock (a b : ℕ) where
  /-- The skip gate. -/
  gα : ℝ
  /-- The sublayer gate. -/
  gβ : ℝ
  /-- The skip connection. -/
  skip : (Fin a → ℝ) → (Fin b → ℝ)
  /-- The sublayer map. -/
  F : (Fin a → ℝ) → (Fin b → ℝ)

/-- A residual block is *monotone* when its gates are nonnegative and both maps are monotone. -/
def ResBlock.IsMonotone {a b} (B : ResBlock a b) : Prop :=
  0 ≤ B.gα ∧ 0 ≤ B.gβ ∧ Monotone B.skip ∧ Monotone B.F

/-- Denotation of a residual block via the `residual` combinator. -/
def ResBlock.toFun {a b} (B : ResBlock a b) : (Fin a → ℝ) → (Fin b → ℝ) :=
  residual B.gα B.gβ B.skip B.F

/-- A monotone residual block denotes a monotone map. -/
theorem ResBlock.monotone_toFun {a b} (B : ResBlock a b) (h : B.IsMonotone) :
    Monotone B.toFun :=
  residual_monotone h.1 h.2.1 h.2.2.1 h.2.2.2

/-- A deep residual network: a chain of residual blocks from arity `a` to `c`. -/
inductive ResNet : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ResNet a a
  | cons : {a b c : ℕ} → ResBlock a b → ResNet b c → ResNet a c

/-- Denotation of a residual stack: compose the blocks front to back. -/
def ResNet.toFun : {a c : ℕ} → ResNet a c → (Fin a → ℝ) → (Fin c → ℝ)
  | _, _, .nil, x => x
  | _, _, .cons B rest, x => rest.toFun (B.toFun x)

/-- A residual stack is *monotone* when every block is. -/
def ResNet.IsMonotone : {a c : ℕ} → ResNet a c → Prop
  | _, _, .nil => True
  | _, _, .cons B rest => B.IsMonotone ∧ rest.IsMonotone

/-- **Soundness: a residual stack of any depth is monotone.** -/
theorem ResNet.monotone_toFun : {a c : ℕ} → (N : ResNet a c) → N.IsMonotone → Monotone N.toFun
  | _, _, .nil, _ => monotone_id
  | _, _, .cons B rest, h => (rest.monotone_toFun h.2).comp (B.monotone_toFun h.1)

end UniversalApproximation.Runje
