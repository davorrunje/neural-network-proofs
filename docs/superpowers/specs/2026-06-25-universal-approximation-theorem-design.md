# Universal Approximation Theorem — Design Spec

**Date:** 2026-06-25
**Status:** Approved (design) — pending spec review
**Target:** A compiling Lean 4 / Mathlib *scaffold* of the Universal Approximation
Theorem (Cybenko, general n-dimensional form), with the two deep analytic lemmas
admitted behind named declarations and a documented roadmap to discharge them.

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

## Context

`lean-playground` is a learning project (Lean 4 + Mathlib `v4.32.0-rc1`). After a
first worked example (`LeanPlayground/Intro.lean`), the goal is a substantially more
ambitious target: define what a neural network is and state + prove the Universal
Approximation Theorem (UAT).

A *fully* `sorry`-free proof of the general UAT is a research-scale formalization: the
classic proof depends on the Riesz representation of the dual of `C(K)` as signed
measures, which a feasibility probe suggests is **not** readily available in this
Mathlib version (Mathlib has Riesz–Markov–Kakutani for *positive* functionals; the
signed/dual form likely needs building). We therefore target a **compiling scaffold +
roadmap**: correct definitions, the precise theorem statement, genuine proofs of all
the structural/glue steps, and exactly two clearly-marked admitted lemmas that map onto
the known-hard analytic facts.

### Confirmed Mathlib support (feasibility probe)

- ✅ Stone–Weierstrass: `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`
- ✅ Hahn–Banach extension: `exists_extension_norm_eq`
- ✅ Hahn–Banach geometric separation: `geometric_hahn_banach_point_closed`
- ⚠️ Riesz representation of `(C(K,ℝ))*` as signed measures: **unconfirmed / likely absent** → admitted.

### Reference

Cybenko, G. (1989). *Approximation by superpositions of a sigmoidal function.*
Mathematics of Control, Signals, and Systems, 2(4): 303–314. DOI 10.1007/BF02551274.
The online proof confirms the strategy used here: Hahn–Banach + Riesz, with the
*discriminatory* condition on the activation as the property that drives the
contradiction. Stone–Weierstrass does **not** apply (the network family is not a
subalgebra — not closed under multiplication); recorded and set aside.

## Scope & definition of done

**In scope.** A directory of Lean files under the existing `LeanPlayground` library that
builds via `lake build`, defining a general feedforward neural network, the
single-hidden-layer family, the activation predicates, and the UAT statement, with a
proof that is complete except for two named admitted lemmas.

**Out of scope.** Discharging the admitted lemmas (Riesz dual representation;
sigmoidal ⇒ discriminatory); multi-output approximation; `Lᵖ` versions; training,
optimization, or any algorithmic/numeric content; depth-vs-width results.

**Done =** `lake build` succeeds with *only* `declaration uses 'sorry'` warnings, and
those occur *only* on the admitted lemmas; `#check @universal_approximation` shows the
intended type; the module docstring lists the admit inventory (the roadmap).

## Definitions

Ambient spaces:
- Input: `EuclideanSpace ℝ (Fin n)` (provides `⟪w, x⟫` and finite-dim normed/inner-product structure).
- Domain: `K : Set (EuclideanSpace ℝ (Fin n))`, `hK : IsCompact K`. Approximation happens
  in `C(K, ℝ) = ContinuousMap ↥K ℝ` with the sup-norm (`↥K` is a `CompactSpace` from `hK`).

Activation predicates (`σ : ℝ → ℝ`):
- `Sigmoidal σ := Continuous σ ∧ Tendsto σ atBot (𝓝 0) ∧ Tendsto σ atTop (𝓝 1)`.
- `Discriminatory K σ :=` for every signed regular Borel measure `μ` on `↥K`,
  `(∀ w b, ∫ x, σ (⟪w, x⟫ + b) ∂μ = 0) → μ = 0`.

General feedforward network ("what a neural network is"):
- `Layer a b`: weight matrix `Matrix (Fin b) (Fin a) ℝ` + bias `Fin b → ℝ`; its map is the
  affine map followed by pointwise `σ`.
- `Network`: a chain of layers; denotation `Network.toFun : (Fin nᵢₙ → ℝ) → (Fin nₒᵤₜ → ℝ)`.
- Lemma (proved): `Continuous σ → Continuous net.toFun`.

The theorem's family `S`:
- Generators `g_{w,b}(x) = σ (⟪w, x⟫ + b)` restricted to `↥K`, as elements of `C(K, ℝ)`.
- `S σ K : Submodule ℝ C(K, ℝ) := Submodule.span ℝ {g_{w,b} | w, b}`. Elements are the
  finite sums `Σⱼ αⱼ · σ (⟪wⱼ, ·⟫ + bⱼ)`.
- Bridge lemma (proved): each element of `S` is the denotation of a single-hidden-layer
  `Network` (hidden activation `σ`, linear output), linking `S` to the general definition.

Making `S` a `Submodule` of `C(K,ℝ)` is the key modeling decision: it turns
"approximation" into `S.topologicalClosure = ⊤` and makes the Hahn–Banach machinery
directly applicable.

## Main statement

```lean
theorem universal_approximation
    {n : ℕ} (σ : ℝ → ℝ) (hσ : Sigmoidal σ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    (S σ K).topologicalClosure = ⊤
```

Corollary (ε-form): `∀ (f : C(K,ℝ)) (ε : ℝ), 0 < ε → ∃ g ∈ S σ K, ‖f - g‖ < ε`.

## Proof architecture (🟢 prove / 🔴 admit)

1. 🟢 `S σ K` is a submodule; each generator is continuous (from `hσ.continuous` and
   continuity of `x ↦ ⟪w,x⟫ + b`).
2. 🟢 **Hahn–Banach reduction**: `S.topologicalClosure = ⊤ ↔
   (∀ L : (C(K,ℝ))*, (∀ g ∈ S, L g = 0) → L = 0)`, proved from `exists_extension_norm_eq`
   / geometric separation. (Intent: genuinely prove. If the generic wiring proves
   disproportionately painful, this is the one fallback admit — flagged, not planned.)
3. 🔴 **Riesz representation** (`riesz_repr`): every `L : (C(K,ℝ))*` is
   `L g = ∫ x, g x ∂μ` for a signed regular Borel measure `μ`, with `L = 0 ↔ μ = 0`.
   **Admit.** Roadmap: build the signed/dual Riesz representation, or extract it from
   Mathlib's Riesz–Markov–Kakutani for positive functionals via Jordan decomposition.
4. 🟢 **Generators into the measure**: `(∀ g ∈ S, L g = 0)` ⇒
   `∀ w b, ∫ x, σ (⟪w,x⟫+b) ∂μ = 0` (unfold span + linearity of the integral).
5. 🔴 **`sigmoidal_discriminatory`**: `Sigmoidal σ → Discriminatory K σ`. **Admit.**
   Roadmap: the Fourier/measure argument of Cybenko §3.
6. 🟢 **Close**: step 4 + discriminatory ⇒ `μ = 0` ⇒ (Riesz) `L = 0`; with step 2, `S`
   is dense.

Net: structural steps (1, 2, 4, 6) are really proved; exactly **two** named lemmas
(steps 3, 5) are admitted, each with a docstring stating the missing math + the Cybenko
reference.

## File layout

```
LeanPlayground/UniversalApproximation/
  Activation.lean   -- σ, Sigmoidal, Discriminatory; 🔴 sigmoidal_discriminatory; basic facts
  Network.lean      -- Layer, Network, Network.toFun, continuity lemma
  Family.lean       -- generators g_{w,b}, S : Submodule ℝ C(K,ℝ), bridge lemma to Network
  Riesz.lean        -- 🔴 riesz_repr: signed-measure representation interface for (C(K,ℝ))*
  Theorem.lean      -- Hahn–Banach reduction (proved) + universal_approximation + ε-corollary
LeanPlayground/UniversalApproximation.lean  -- imports the five (single build entry point)
```

Each 🔴 admit is a named lemma with a docstring (missing math + reference) and a single
`sorry`; no bare `sorry` scattered inside proofs.

## Verification

- `lake build` succeeds with **only** `declaration uses 'sorry'` warnings, and only on the
  admitted lemmas.
- MCP `lean_diagnostic_messages` per file → no `error`-severity items.
- `#check @universal_approximation` confirms hypotheses + `topologicalClosure = ⊤` conclusion.
- Sanity instantiation: `Sigmoidal (fun t => 1 / (1 + Real.exp (-t)))` for the logistic
  function (proved if quick; otherwise a clearly-marked third admit) — guards against
  vacuous definitions.
- Module docstring carries the **admit inventory** (= the roadmap), so remaining work is
  greppable and honest.

## Roadmap (admitted lemmas, in priority order)

1. `riesz_repr` — signed/dual Riesz representation for `(C(K,ℝ))*`. The substantive gap;
   either formalize directly or derive from Riesz–Markov–Kakutani + Jordan decomposition.
2. `sigmoidal_discriminatory` — continuous sigmoidal ⇒ discriminatory (Cybenko §3, Fourier/
   measure argument).
3. (If needed) logistic-function-is-sigmoidal sanity lemma.
