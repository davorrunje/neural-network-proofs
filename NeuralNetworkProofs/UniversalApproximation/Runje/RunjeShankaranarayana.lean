/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.NeuralNetwork.Network
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Runje–Shankaranarayana dense layer is monotone (Runje et al.)

Part of the deep constrained monotonic networks development. The `mononet` "absolute-mode" dense
layer (Runje–Shankaranarayana 2023) builds nonnegative effective weights `|W|`, feeds a first block
of *convex* neurons through a base activation `ρ`, and a second block of *concave* neurons through
its point reflection `Sartor.reflect ρ`. Modeled here as the `Fin.append` of two single-activation
sublayers, it is a monotone map — an instance of the shared monotone abstraction
(`Monotone.layer_toFun_monotone`). Its base activations (`elu`, `softplus`) are monotone and
one-sided (left-)saturating, so their reflections meet the Sartor universal-approximation
hypotheses.

* `rsDense` — the R–S absolute-mode dense map (convex/concave sublayer split).
* `rsDense_monotone` — the R–S dense map is monotone.
* `elu`, `softplus` — the base activations.
* `elu_monotone`, `softplus_monotone` — the base activations are monotone.
* `elu_leftSaturating`, `softplus_leftSaturating` — the base activations are left-saturating.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.Sartor

/-- R–S absolute-mode dense map: convex block (`ρ`, weights `|Wc|`) on the first `c` outputs,
concave block (`reflect ρ`, weights `|Wk|`) on the rest, appended. -/
noncomputable def rsDense {a c k : ℕ} (ρ : ℝ → ℝ)
    (Wc : Matrix (Fin c) (Fin a) ℝ) (bc : Fin c → ℝ)
    (Wk : Matrix (Fin k) (Fin a) ℝ) (bk : Fin k → ℝ) : (Fin a → ℝ) → (Fin (c + k) → ℝ) :=
  fun x => Fin.append
    (({ W := Wc.map (fun t => |t|), c := bc } : NeuralNetwork.Layer a c).toFun ρ x)
    (({ W := Wk.map (fun t => |t|), c := bk } : NeuralNetwork.Layer a k).toFun (reflect ρ) x)

/-- The R–S absolute-mode dense map is monotone: it is the `Fin.append` of a convex block with
monotone activation `ρ` and non-negative weights `|Wc|`, and a concave block with monotone
activation `reflect ρ` and non-negative weights `|Wk|`. Both blocks are monotone by
`layer_toFun_monotone`, and `Fin.append` is monotone coordinatewise. -/
theorem rsDense_monotone {a c k : ℕ} {ρ : ℝ → ℝ} (hρ : Monotone ρ)
    (Wc : Matrix (Fin c) (Fin a) ℝ) (bc : Fin c → ℝ)
    (Wk : Matrix (Fin k) (Fin a) ℝ) (bk : Fin k → ℝ) :
    Monotone (rsDense ρ Wc bc Wk bk) := by
  have hconv : Monotone (({ W := Wc.map (fun t => |t|), c := bc } :
      NeuralNetwork.Layer a c).toFun ρ) :=
    layer_toFun_monotone _ hρ (fun i j => abs_nonneg _)
  have hconc : Monotone (({ W := Wk.map (fun t => |t|), c := bk } :
      NeuralNetwork.Layer a k).toFun (reflect ρ)) :=
    layer_toFun_monotone _ (reflect_monotone hρ) (fun i j => abs_nonneg _)
  intro x y hxy i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa only [rsDense, Fin.append_left] using hconv hxy i
  · simpa only [rsDense, Fin.append_right] using hconc hxy j

/-- Exponential linear unit (ELU): the identity on the positive axis, `exp x - 1` elsewhere. -/
noncomputable def elu (x : ℝ) : ℝ := if 0 < x then x else Real.exp x - 1

/-- Softplus: the smooth `log (1 + exp x)` approximation of the ReLU. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- ELU is monotone. -/
theorem elu_monotone : Monotone elu := by
  intro x y hxy
  simp only [elu]
  split_ifs with hx hy hy
  · exact hxy
  · exact absurd (lt_of_lt_of_le hx hxy) hy
  · have hle : Real.exp x ≤ Real.exp 0 := Real.exp_le_exp.mpr (not_lt.mp hx)
    rw [Real.exp_zero] at hle
    linarith
  · linarith [Real.exp_le_exp.mpr hxy]

/-- ELU is left-saturating: `elu x → -1` as `x → -∞`, since on the negative axis it equals
`exp x - 1` and `exp x → 0`. -/
theorem elu_leftSaturating : LeftSaturating elu := by
  refine ⟨-1, ?_⟩
  have hb : Filter.Tendsto (fun x : ℝ => Real.exp x - 1) Filter.atBot (nhds (0 - 1)) :=
    Real.tendsto_exp_atBot.sub_const 1
  rw [zero_sub] at hb
  refine Filter.Tendsto.congr' ?_ hb
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
  rw [elu, if_neg (not_lt.mpr hx)]

/-- Softplus is monotone: `log` is monotone on `(0, ∞)` and `1 + exp x > 0` increases with `x`. -/
theorem softplus_monotone : Monotone softplus := by
  intro x y hxy
  simp only [softplus]
  have hpos : (0 : ℝ) < 1 + Real.exp x := by positivity
  exact Real.log_le_log hpos (by linarith [Real.exp_le_exp.mpr hxy])

/-- Softplus is left-saturating: `softplus x → 0` as `x → -∞`, since `1 + exp x → 1` and
`log 1 = 0`. -/
theorem softplus_leftSaturating : LeftSaturating softplus := by
  refine ⟨0, ?_⟩
  have h1 : Filter.Tendsto (fun x : ℝ => 1 + Real.exp x) Filter.atBot (nhds (1 + 0)) :=
    Real.tendsto_exp_atBot.const_add 1
  rw [add_zero] at h1
  have h2 : Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num)).tendsto
  rw [Real.log_one] at h2
  exact h2.comp h1

end UniversalApproximation.Runje
