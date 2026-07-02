# Monotone Neural Network Approximation — Design

**Date:** 2026-07-02
**Status:** approved (design); implementation plan to follow
**Paper:** Dan Mikulincer, Daniel Reichman, *"Size and depth of monotone neural networks:
interpolation and approximation"*, arXiv:2207.05275. **This project formalizes Result 1 only**
(depth-4 monotone approximation via monotone interpolation). Result 2 (the exponential size
separation) is a possible separate later project.

## Goal

Formalize, `sorry`-free in Lean 4 + Mathlib, the two positive results of the paper's Result 1:

- **Interpolation** — every *monotone dataset* is interpolated exactly by a depth-4 monotone
  threshold network.
- **Approximation** — every *continuous monotone* function on `[0,1]^d` is approximated to
  arbitrary `ℓ∞` accuracy by a depth-4 monotone threshold network.

This is the monotone-NN work reserved in `CLAUDE.md`. It lands under
`NeuralNetworkProofs/UniversalApproximation/Monotone/` (namespace `UniversalApproximation.Monotone`).

## Scope

**In scope:** Result 1, **depth-4 + existence** only. Depth is proven exactly (4 weight layers);
neuron counts are NOT tracked.

**Out of scope** (each a candidate later project, noted so no task silently pulls them in):
- Result 2 — monotone functions requiring exponential-size monotone networks (separation/lower bound).
- All quantitative **size / neuron-count** bounds (`O(nd)`, `O(d(Ld/ε)^d)`).
- The **totally-ordered → depth-3** refinement.
- The **Lemma-3** first-layer `≥ n` lower bound.

## The two public headlines

Target statements (final Lean signatures may adjust names/binders, but the mathematical content
is fixed):

- `monotone_interpolation` — For a monotone dataset `{(xᵢ, yᵢ)}_{i ∈ Fin n}` in `(Fin d → ℝ) × ℝ`
  (i.e. `xᵢ ≤ xⱼ → yᵢ ≤ yⱼ`, and distinct inputs), there exists a monotone threshold network `N`
  of depth 4 with `N xᵢ = yᵢ` for every `i`.
- `monotone_approximation` — For continuous monotone `f : (Fin d → ℝ) → ℝ` and `ε > 0`, there
  exists a monotone threshold network `N` of depth 4 with `|N x − f x| ≤ ε` for all `x ∈ [0,1]^d`
  (the unit cube `Set.Icc 0 1` in the coordinatewise order).

Both must have axiom profile `[propext, Classical.choice, Quot.sound]`.

## Network model

A fresh model, reusing `NeuralNetwork.Layer` (weight matrix + bias) as the per-layer primitive.

- **Threshold gate:** `θ (z : ℝ) : ℝ := if 0 ≤ z then 1 else 0`.
- **Layered network:** an explicit chain of layers so that **depth is structural** (not an opaque
  `toFun`). Hidden layers apply `θ` pointwise; the **top layer is a non-negative linear read-out**
  (Theorem 2's output is a real interpolated value, not a 0/1 threshold). "Depth 4" = four weight
  layers, matching the paper.
- **Monotonicity predicate `IsMonotone`:** every weight-matrix entry is `≥ 0` (biases
  unconstrained). Threshold `θ` is monotone nondecreasing and non-negative weights preserve the
  coordinatewise order, so:
- **Denotation + monotonicity lemma:** `toFun N : (Fin d → ℝ) → ℝ`, and for `IsMonotone N`,
  `x ≤ y → toFun N x ≤ toFun N y`. This monotonicity lemma is the workhorse of the Theorem-2
  sandwich.

Depth counting: `depth` = number of weight layers; the model records its layers explicitly (e.g. a
structure carrying the hidden `Layer`s + the non-negative read-out), and `depth N = 4` is a
provable fact about the constructed networks, not an axiom.

## Decomposition (files, one responsibility each)

1. **`Monotone/Defs.lean`** — `θ`; the monotone threshold network model; `depth`; `IsMonotone`;
   denotation `toFun`; the lemma `IsMonotone N → Monotone (toFun N)`. Foundational; every later
   file depends on it.
2. **`Monotone/Domination.lean`** — the **Lemma-4 gadget**. A 2-threshold-layer sub-network
   computing the domination indicator `𝟙(x ≥ p)` for a fixed point `p : Fin d → ℝ`, realized as
   `θ (∑ⱼ θ (xⱼ − pⱼ) − d)`, with non-negative weights. Proves it equals `1` iff `x ≥ p` and `0`
   otherwise, and that it is monotone. The reusable building block for interpolation.
3. **`Monotone/Interpolation.lean`** — **Theorem 1**. Assemble the domination indicators over the
   dataset points and a **non-negative combination that reconstructs the `yᵢ`** via telescoping
   increments (differences of sorted values arranged so all read-out weights are `≥ 0`). Establish
   depth = 4 and exact interpolation. Public `monotone_interpolation`. *(Crux — see risk.)*
4. **`Monotone/Grid.lean`** — the grid `G_δ = (δ_d · ℤ)^d ∩ [0,1]^d` with `δ_d = δ/√d`; the fact
   that grid samples `{(g, f g) : g ∈ G_δ}` of a monotone `f` form a monotone dataset; and the
   neighbor-sandwich lemma: every `x ∈ [0,1]^d` has grid neighbors `x₋ ≤ x ≤ x₊` in `G_δ` with
   `‖x₊ − x₋‖ ≤ δ`.
5. **`Monotone/Approximation.lean`** — **Theorem 2**. Uniform continuity of `f` on the compact cube
   → `δ`; build the grid dataset; apply Theorem 1 to get `N` with `N g = f g` on the grid; then for
   arbitrary `x`, sandwich `f x₋ ≤ N x ≤ f x₊` and `f x₋ ≤ f x ≤ f x₊` (monotonicity of both `N`
   and `f`) and close with `|f x₊ − f x₋| ≤ ε`. Public `monotone_approximation`.
6. **`Monotone.lean`** (root) — re-export both headlines; docstring; included from
   `NeuralNetworkProofs.lean` so `lake build` checks them.

## Proof structure

**Theorem 1 (Interpolation).** Inputs: monotone dataset. (a) For each dataset point `xᵢ`, the
Domination gadget gives a depth-2 monotone sub-network `dᵢ(x) = 𝟙(x ≥ xᵢ)`. (b) A non-negative
read-out combines the `dᵢ` so the value at `xⱼ` telescopes to `yⱼ`: because the dataset is
monotone, the increments assigned to points can be chosen `≥ 0`, keeping the network monotone.
(c) Stack to depth 4 and prove `N xᵢ = yᵢ`.

**Theorem 2 (Approximation).** (a) `f` continuous on compact `[0,1]^d` ⇒ uniformly continuous ⇒
`∃ δ>0, ‖x−y‖ ≤ δ → |f x − f y| ≤ ε`. (b) Build `G_δ` and the monotone dataset of grid samples
(Grid.lean). (c) Theorem 1 ⇒ depth-4 monotone `N` with `N g = f g` on `G_δ`. (d) For `x ∈ [0,1]^d`
with neighbors `x₋ ≤ x ≤ x₊`: monotonicity of `N` gives `f x₋ = N x₋ ≤ N x ≤ N x₊ = f x₊`;
monotonicity of `f` gives `f x₋ ≤ f x ≤ f x₊`; both `N x` and `f x` lie in `[f x₋, f x₊]`, an
interval of length `|f x₊ − f x₋| ≤ ε`. Hence `|N x − f x| ≤ ε`.

## Risk

The analysis half (uniform continuity, grid, sandwich) is Mathlib-friendly and low risk. The
**crux and main research risk is the value-reconstruction step in Theorem 1**: producing the exact
`yᵢ` from the domination pattern using only non-negative read-out weights. The plan sequences
`Defs → Domination → Interpolation` **first**, so this risk surfaces before the analysis wrapper is
built. If a construction detail proves intractable, it is reported as `NEEDS_CONTEXT`, never hidden
behind `sorry` or a weakened statement.

## Conventions & verification bar

- `sorry`/`admit`-free; the real gate is `#print axioms` on both headlines =
  `[propext, Classical.choice, Quot.sound]` (via `lake env lean`, fresh oleans), plus
  `scripts/check_sorry_free.lean` clean and `lake build` green.
- Line length ≤ 100 codepoints; docstrings on public declarations.
- **Deferred signing:** the user is often unavailable during execution and SSH signing needs their
  live confirmation. Execution commits are made **unsigned**; the branch is **batch-signed in one
  step immediately before the PR** (`git rebase --exec 'git commit --amend --no-edit -S' <base>`),
  signing ONLY the unpushed commits once anything has been pushed (avoid the repo's no-force-push
  rule). PR opened only after every commit shows `G`.
- New definitions are project-local (not `ForMathlib/`); if a genuinely general lemma emerges,
  promotion to `ForMathlib/` is a separate decision, not part of this pass.
