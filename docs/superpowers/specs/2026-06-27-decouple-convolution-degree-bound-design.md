# Decouple `ForMathlib/TestFunctionDegreeBound.lean` from the Leshno development

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

**Date:** 2026-06-27
**Status:** Approved (design); proceeding to plan.
**Branch:** `refactor/decouple-formathlib` (from `origin/main` @ `ce2a197`).

## Goal

Make the uniform-degree-bound result genuinely upstream-ready by removing every dependency on the
Leshno development. Today `Contrib/TestFunctionDegreeBound.lean` imports
`UniversalApproximation.Leshno.MollifyDef` and is stated in terms of the Leshno-specific `mollify`,
`ClassM`, and `IsPolynomialFun`. After this change it depends only on `Mathlib` and the sibling
`ForMathlib`/`Contrib` convolution-polynomial lemmas, and is renamed to reflect its now-general
content.

## Background: the exact coupling

`Contrib/TestFunctionDegreeBound.lean` couples to Leshno in three ways, each sugar over a general
concept:

1. **`mollify σ φ`** (from `Leshno.MollifyDef`) — definitionally
   `convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume` (`mollify_eq_convolution`).
2. **hypothesis `ClassM σ`** — used *only* to derive `LocallyIntegrable σ volume` and
   `AEStronglyMeasurable σ volume` (the two `private classM_locallyIntegrable` /
   `classM_aestronglyMeasurable` copies in the file).
3. **`IsPolynomialFun (mollify σ φ)`** — unfolds to `∃ p : Polynomial ℝ, mollify σ φ = fun t => p.eval t`.

Confirmed facts:
- Mathlib has `LocallyIntegrable.aestronglyMeasurable` (instances hold for `ℝ → ℝ`), so a single
  hypothesis `LocallyIntegrable σ volume` yields both needed measurability/integrability facts and
  makes the two `private classM_*` copies unnecessary.
- `IsPolynomialFun σ` is defined as `∃ p : Polynomial ℝ, σ = fun t => p.eval t` — inlinable.
- The Leshno side already exposes **public** `ClassM.locallyIntegrable` and
  `ClassM.aestronglyMeasurable` (in `Leshno/Mollify.lean`), so the consumer has its adapter ready.
- The only consumer of `exists_uniform_degree_bound` is `Leshno.Mollify.exists_nonpoly_mollify`.

## Approach

Chosen: **restate the lemmas purely over `convolution` / `LocallyIntegrable` / an inline polynomial
predicate, and adapt the single Leshno call site.**

Rejected alternatives: moving `mollify` into `ForMathlib` (it is a Leshno alias; Mathlib uses
`convolution`, so it would pollute the upstream folder); introducing a general `IsPolynomialFun`
predicate in `ForMathlib` (inlining `∃ p, f = p.eval` is simpler and idiomatic).

### Substitutions

| Leshno-coupled (before) | General (after) |
|---|---|
| `mollify σ φ` | `convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume` |
| hypothesis `ClassM σ` | `LocallyIntegrable σ volume` |
| `AEStronglyMeasurable σ` (via `classM_aestronglyMeasurable`) | `hσ.aestronglyMeasurable` (`LocallyIntegrable.aestronglyMeasurable`) |
| `IsPolynomialFun (mollify σ φ)` | `∃ p : Polynomial ℝ, convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => p.eval t` |

### File changes

`Contrib/TestFunctionDegreeBound.lean` (renamed to `Contrib/ConvolutionDegreeBound.lean`):
- Remove `import LeanPlayground.UniversalApproximation.Leshno.MollifyDef` (and the
  `open UniversalApproximation.Leshno`).
- Delete the two `private` lemmas `classM_aestronglyMeasurable` and `classM_locallyIntegrable`.
- Rename the namespace `TestFunctionDegreeBound` → `ConvolutionDegreeBound`.
- `mollify_conv_assoc` → restated as a pure convolution-associativity lemma over
  `convolution … (ContinuousLinearMap.mul ℝ ℝ) volume` with hypothesis `LocallyIntegrable σ volume`
  (measurability via `hσ.aestronglyMeasurable`; local integrability of `‖σ‖` as before). Its proof
  body already operates in the convolution orientation (it opens with
  `rw [mollify_eq_convolution, mollify_eq_convolution]`), so the interior is essentially unchanged —
  only the statement and the two derived measurability facts change source.
- `exists_uniform_degree_bound` → restated with hypothesis `LocallyIntegrable σ volume`, the inline
  polynomial predicate in `H`, and the conclusion
  `iteratedDeriv (d + 1) (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) = 0`. The proof body
  is the same argument (it already used the convolution bridge `hbridge` internally); the references
  to `mollify`/`H`-as-`IsPolynomialFun` become references to the general forms.
- Update the file's header: drop "research leaf — no general Mathlib home yet"; describe the
  general statement (a uniform iterated-derivative/degree bound for convolutions against
  test functions whose mollifications are all polynomials) and propose a plausible Mathlib home
  (e.g. alongside `Mathlib/Analysis/Convolution`).

`Leshno/Mollify.lean` (consumer):
- Update the import `Contrib.TestFunctionDegreeBound` → `Contrib.ConvolutionDegreeBound`.
- In `exists_nonpoly_mollify`, adapt the single call: pass `hσ.locallyIntegrable` (= `ClassM.locallyIntegrable hσ`)
  for the hypothesis; bridge `IsPolynomialFun (mollify σ φ)` ↔ the inline predicate and the
  `iteratedDeriv … (convolution …)` conclusion ↔ `iteratedDeriv … (mollify …)` via
  `mollify_eq_convolution`. No new wrapper lemma; the *statement* of `exists_nonpoly_mollify` is
  unchanged.

`UniversalApproximation/Leshno.lean` (admit-inventory docstring):
- Update the references `TestFunctionDegreeBound.exists_uniform_degree_bound` →
  `ConvolutionDegreeBound.exists_uniform_degree_bound` and the supporting-lemma names.

## Verification / done-criteria

- `lake build` green.
- `ConvolutionDegreeBound.lean` contains **no** `import …UniversalApproximation…` and no reference to
  `mollify`, `ClassM`, or `IsPolynomialFun`.
- `#print axioms` (on freshly-built oleans) for `Leshno.Mollify.exists_nonpoly_mollify` and
  `UniversalApproximation.Leshno.leshno_dense_iff` remain `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`); likewise `ConvolutionDegreeBound.exists_uniform_degree_bound` and
  `…mollify_conv_assoc`.
- `git mv` used for the file rename (history preserved).
- No other file references the old `TestFunctionDegreeBound` namespace/module.
- Line length ≤ 100 codepoints.

## Sequencing

Independent of the headline work and the reorg. Branches from `origin/main` (which already contains
the D-work). Should land **before** the `NeuralNetworkProofs` reorg so that the `ForMathlib/` folder
is genuinely Leshno-free when the reorg renames `Contrib/` → `ForMathlib/`. The reorg branch
(`refactor/neural-network-proofs`) will rebase onto the post-merge `main` and pick up the renamed
`ConvolutionDegreeBound.lean`.

## Global constraints

- Do not change the *statement* of `exists_nonpoly_mollify` or any headline theorem; the visible
  contract is unchanged. Only `exists_uniform_degree_bound` / `mollify_conv_assoc` are restated
  (their content/strength is preserved — `ClassM σ → LocallyIntegrable σ` is a *generalization*, so
  the consumer still type-checks).
- No new Mathlib upstream dependency.
- Commits SSH-signed.
- Preserve git history via `git mv`.
