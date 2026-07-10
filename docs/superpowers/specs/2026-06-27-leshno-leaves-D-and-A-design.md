# Leshno UAT — filling the two remaining analytic leaves (D and A) — Design Spec

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

**Date:** 2026-06-27
**Status:** Approved (design) — pending spec review
**Goal:** Discharge the two remaining documented `sorry` leaves of the Leshno M-class UAT scaffold —
`exists_nonpoly_mollify` (D) and `mollify_ridge_mem_T` (A) — by building the missing general
analytic lemmas as reusable, Mathlib-upstream-ready `Contrib` contributions and then assembling them
in `Mollify.lean`. On completion the entire `leshno_dense_iff` development is `sorry`-free.

## Context

The Leshno scaffold (`LeanPlayground/UniversalApproximation/Leshno/`, PR #6) proves the headline

```lean
theorem leshno_dense_iff {σ : ℝ → ℝ} (hσ : ClassM σ) :
    DenselyApproximates σ ↔ ¬ IsAEPolynomial σ
```

as glue over six analytic leaves. **Four are already proved** (`iteratedDeriv_eq_zero_imp_poly`,
`ridgePow_span` — both in `Contrib/`; `contDiff_mollify`; `deriv_pow_mem` — so `smooth_engine` is
fully `sorryAx`-free). **Two remain**, both in `Mollify.lean`:

```lean
-- D
theorem exists_nonpoly_mollify {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ¬ IsPolynomialFun (mollify σ φ)

-- A
theorem mollify_ridge_mem_T {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩ : C(↥K, ℝ)) ∈ T σ K
```

where `mollify σ φ := fun x => ∫ y, σ (x - y) * φ y` (already proved equal to
`convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume`), `ClassM σ` = locally bounded +
discontinuity-closure null, and smoothness is `ContDiff ℝ ∞` (C^∞).

**Reference.** Pinkus, *Approximation theory of the MLP model*, Acta Numerica 8 (1999), Thm 3.1.

## Decisions locked during brainstorming

1. **Upstream-helpers-first.** The hard analytic content of both leaves is factored into general,
   dependency-light lemmas placed in `LeanPlayground/Contrib/` (each its own per-contribution
   namespace + inline `Intended Mathlib home:` header, matching the established convention). The
   project-specific assembly stays in `Mollify.lean`.
2. **D — full Baire route** for the uniform degree bound (the faithful classical argument; produces
   genuinely upstreamable test-function-space infrastructure).
3. **A — staged via continuous σ first**: prove the uniform Riemann-sum convergence and the full
   `genFun`-assembly for *continuous* `σ` (easy, validates the machinery), then generalize the
   convergence lemma to the M-class (bounded a.e.-continuous) case.

## Available proved helpers (reuse)

`IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly` (vanishing `n`-th derivative ⇒ polynomial
of `degree < n`), `RidgePowersSpan.ridgePow_span`, `contDiff_mollify`, `deriv_pow_mem`,
`exists_antideriv` (polynomial antiderivative), `ClassM.aestronglyMeasurable`,
`ClassM.locallyIntegrable`, `genFun_reparam_mem`, `T_isClosed`. From Mathlib:
`HasCompactSupport.hasDerivAt_convolution_left`, `ae_eq_of_integral_contDiff_smul_eq`
(degree-0 distributional recovery), `ContDiffBump.convolution_tendsto_right`, `BaireSpace`.

## D — `exists_nonpoly_mollify` (contrapositive)

Assume `H : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → IsPolynomialFun (mollify σ φ)`; derive
`IsAEPolynomial σ`, contradicting `hnp`. Sub-lemmas:

- **D-B1 — iterated convolution derivative** *(Contrib: `ConvolutionIteratedDeriv.lean`)*.
  `iteratedDeriv n (mollify σ φ) = mollify σ (iteratedDeriv n φ)` (equivalently for the bundled
  `convolution`), by induction on `HasCompactSupport.hasDerivAt_convolution_left`. ~40–80 lines.
  *Intended Mathlib home:* `Mathlib/Analysis/Calculus/ContDiff/Convolution`.

- **D-B2 — uniform degree bound (the crux, Baire)** *(Contrib: `TestFunctionDegreeBound.lean`)*.
  Under `H`, there is a single `d` with `(mollify σ φ).natDegree ≤ d` (as a polynomial) for all test
  `φ`. Classical proof: the sets `Fₙ := {φ : the polynomial mollify σ φ has degree ≤ n}` are closed
  in the test-function topology and cover it; by Baire one has nonempty interior, yielding a uniform
  bound. Requires building enough of the test-function-space topology / closedness scaffolding to
  apply `BaireSpace`. ~150+ lines; research-grade. *Intended Mathlib home:* distribution theory
  (new area; flag for maintainers).

- **D-B3 — smooth ⇒ polynomial recovery: ALREADY PROVED.** This is exactly
  `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly` (a C^∞ function with `iteratedDeriv (d+1)`
  vanishing is a polynomial of `degree < d+1`). No new work.

- **D-B4 — moment-vanishing antiderivative** *(Contrib: `SmoothCompactAntideriv.lean`)*.
  A smooth compactly-supported `g` with `∫ g(y) yʲ dy = 0` for `j = 0..d` equals `iteratedDeriv (d+1) φ`
  for some smooth compactly-supported `φ`. Built from the iterated indefinite integral `∫_{-∞}^x`,
  proving compact support is preserved exactly when the moments vanish. ~100–150 lines.
  *Intended Mathlib home:* `Mathlib/Analysis/Calculus/...` (bump/antiderivative).

- **D-B5 — degree-`d` distributional polynomial recovery** *(Contrib: `PolynomialDistribution.lean`)*.
  A locally integrable `f` with `∫ f·g = 0` for every smooth compactly-supported `g` whose moments
  up to order `d` vanish is a.e. a polynomial of degree ≤ `d`. Bootstraps Mathlib's degree-0
  `ae_eq_of_integral_contDiff_smul_eq` plus D-B3/D-B4. The actual crux assembly.
  *Intended Mathlib home:* distribution theory.

- **D-assembly** *(in `Mollify.lean`)*. From `H` + D-B1: for the uniform degree `d` (D-B2),
  `mollify σ (iteratedDeriv (d+1) φ) = iteratedDeriv (d+1) (mollify σ φ) = 0` (a degree-≤d
  polynomial's `(d+1)`-th derivative vanishes). Every moment-vanishing `g` is such an
  `iteratedDeriv (d+1) φ` (D-B4), so `σ` annihilates all moment-vanishing test functions; D-B5 gives
  `IsAEPolynomial σ`. Contradiction with `hnp`.

## A — `mollify_ridge_mem_T`

- **A-core-cont — uniform Riemann-sum convolution, continuous integrand**
  *(Contrib: `UniformRiemannConvolution.lean`)*. For **continuous** `f : ℝ → ℝ`, `φ ∈ C_c`, and a
  compact `S ⊆ ℝ`: the point-sampling Riemann sums `∑ᵢ f(s - yᵢ) φ(yᵢ) Δ` converge to
  `∫ f(s - y) φ(y) dy` **uniformly for `s ∈ S`** (uniform continuity of `f` on the compact
  `S - tsupport φ`). *Intended Mathlib home:* `Mathlib/Analysis/Convolution` / Riemann-sum approx.

- **A-assembly-cont — continuous-σ instance** *(in `Mollify.lean`)*. Each Riemann sum, as a function
  of `x`, is `∑ᵢ (φ yᵢ Δ) · genFun σ (lam•w) (lam*b + c - yᵢ)` ∈ `genSpan σ K` via
  `genFun_reparam_mem`; the uniform-on-`S` limit (A-core-cont, with `S` the compact image of `K`)
  composed with the ridge gives `ApproxByGen σ K`, hence membership in `T σ K` (using the closedness
  already available). This validates the entire assembly path for continuous `σ`.

- **A-core-Mclass — uniform Riemann-sum convolution, bounded a.e.-continuous integrand**
  *(Contrib: same file)*. Generalize A-core-cont to `f` **locally bounded and a.e. continuous**
  (`discNull`-style hypothesis): the Riemann sums still converge uniformly in `s ∈ S`. This is the
  M-class analytic core — uniform Riemann integrability of a bounded a.e.-continuous integrand,
  uniform in the translation parameter `s` (Lebesgue's criterion + the null discontinuity set
  controlling the cells that straddle discontinuities). The hard piece.

- **A-assembly-Mclass — close the leaf** *(in `Mollify.lean`)*. Swap A-core-Mclass into the
  assembly (now `σ` need only be `ClassM`, using `ClassM.locBdd` + `ClassM.discNull`) to obtain
  `mollify_ridge_mem_T` in full.

## New files

Under `LeanPlayground/Contrib/` (each its own namespace + `Intended Mathlib home:` header):
`ConvolutionIteratedDeriv.lean` (D-B1), `TestFunctionDegreeBound.lean` (D-B2),
`SmoothCompactAntideriv.lean` (D-B4), `PolynomialDistribution.lean` (D-B5),
`UniformRiemannConvolution.lean` (A-core, both versions).
Edited: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean` (assemblies; remove the two
`sorry`s) and `Leshno.lean` (admit inventory → 0 leaves).

## Sequencing (dependency-ordered; each unit independently verified, no `sorry` introduced beyond the two existing leaves until its assembly lands)

1. **D-B1** — self-contained, easy win.
2. **A-core-cont → A-assembly-cont** — de-risks A's assembly machinery on the easy case.
3. **D-B4**, then **D-B5** (uses D-B1, D-B3, D-B4).
4. **A-core-Mclass → A-assembly-Mclass** — **closes A**.
5. **D-B2** (Baire) — the hardest single piece, done last when everything else is in place.
6. **D-assembly** — **closes D**. Then update `Leshno.lean` inventory and confirm a `sorry`-free `lake build`.

## Effort estimate

D ≈ 400–600 lines across four new Contrib lemmas (B2 Baire and B5 recovery are research-grade).
A ≈ 150–250 lines (A-core-Mclass is the hard part). Multi-session; each Contrib lemma is a discrete,
reviewable, upstreamable unit. Per-lemma discipline: write the statement (elaborates, single `sorry`),
prove it (`lean_verify` axioms `[propext, Classical.choice, Quot.sound]` + any legitimate transitive
leaf), commit (signed). Verification via lean-lsp MCP diagnostics; `lake build` green at each step.

## Non-goals

- No change to the headline statement, `mollify`, `ClassM`, or any already-proved lemma.
- No modification of existing Cybenko files.
- No new approximation topology — everything stays everywhere-sup / C^∞ as established.
- The two leaves' statements are unchanged (only their proofs are filled).
