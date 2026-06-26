import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.UniversalApproximation.Discriminatory
import LeanPlayground.UniversalApproximation.Network
import LeanPlayground.UniversalApproximation.Family
import LeanPlayground.UniversalApproximation.Riesz
import LeanPlayground.UniversalApproximation.Theorem

/-!
# Universal Approximation Theorem (Cybenko) — scaffold root

This is the root module of a Lean 4 + Mathlib scaffold for Cybenko's
**Universal Approximation Theorem** (UAT): the single-hidden-layer neural
network family built from a continuous *sigmoidal* activation is dense in the
space `C(K, ℝ)` of continuous real-valued functions on a compact set
`K ⊆ EuclideanSpace ℝ (Fin n)`.

It re-exports the five component modules:

* `Activation` — `Sigmoidal`, `signedIntegral`, and `Discriminatory`.
* `Discriminatory` — the proved `sigmoidal_discriminatory` (Cybenko's
  Fourier/measure argument).
* `Network` — `Layer`, `Network`, and `Layer.continuous_toFun`.
* `Family` — `generator`, the spanned submodule `S`, and `generator_mem_S`.
* `Riesz` — the admitted dual/signed Riesz representation `riesz_repr`.
* `Theorem` — the Hahn–Banach reduction
  `dense_iff_forall_functional_eq_zero`, the main theorem
  `universal_approximation`, and the ε-form corollary
  `universal_approximation_eps`.

## Admit inventory (roadmap)

The scaffold is complete except for one deep analytic fact, left as a named
`sorry` with a full docstring pointing at its intended proof:

1. `UniversalApproximation.riesz_repr` — the signed / dual Riesz representation:
   every continuous linear functional on `C(K, ℝ)` is integration against a
   signed measure on `K`.

`UniversalApproximation.sigmoidal_discriminatory` — a continuous sigmoidal
activation is discriminatory (Cybenko's Fourier/measure half-space argument) —
is now **fully proved** in `Discriminatory.lean`.

**Everything else is proved**, with no `sorry`:

* continuity of layers / networks (`Layer.continuous_toFun`);
* the spanned subspace and its generators (`S`, `generator`,
  `generator_mem_S`);
* the Hahn–Banach reduction of density to functional vanishing
  (`dense_iff_forall_functional_eq_zero`);
* the headline theorem `universal_approximation`;
* the ε-corollary `universal_approximation_eps`.

The sanity lemma `logistic_sigmoidal` below — that the standard logistic
function `t ↦ 1 / (1 + exp (-t))` is sigmoidal — is **fully proved** (it is
*not* a third admit), exhibiting a concrete activation satisfying the
`Sigmoidal` hypothesis of the main theorem.
-/

namespace UniversalApproximation

open Real

/-- **PROVED (sanity check).** The standard logistic function
`t ↦ 1 / (1 + exp (-t))` is `Sigmoidal`: it is continuous (the denominator
`1 + exp (-t) ≥ 1 > 0` never vanishes), tends to `0` as `t → -∞` (then
`exp (-t) → +∞`, so the reciprocal `→ 0`), and tends to `1` as `t → +∞` (then
`exp (-t) → 0`, so `1 / (1 + exp (-t)) → 1 / 1 = 1`).

This provides a concrete witness for the `Sigmoidal` hypothesis of
`universal_approximation`. -/
theorem logistic_sigmoidal : Sigmoidal (fun t => 1 / (1 + Real.exp (-t))) where
  continuous := by
    have hne : ∀ t : ℝ, (1 + Real.exp (-t)) ≠ 0 := fun t => by positivity
    fun_prop (disch := assumption)
  atBot := by
    have h1 : Filter.Tendsto (fun t : ℝ => 1 + Real.exp (-t)) Filter.atBot Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_left
      exact Real.tendsto_exp_atTop.comp Filter.tendsto_neg_atBot_atTop
    have h2 := h1.inv_tendsto_atTop
    simp only [one_div]
    exact h2
  atTop := by
    have h1 : Filter.Tendsto (fun t : ℝ => 1 + Real.exp (-t)) Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
      simpa using h0.const_add 1
    have h2 : Filter.Tendsto (fun t : ℝ => 1 / (1 + Real.exp (-t))) Filter.atTop (nhds (1 / 1)) :=
      Filter.Tendsto.div tendsto_const_nhds h1 (by norm_num)
    simpa using h2

end UniversalApproximation
