# Monotone Saturating-Activation Universal Approximation — Design

**Date:** 2026-07-05
**Status:** approved (design); implementation plan to follow
**Paper:** Sartor, Sinigaglia, Susto, *"Advancing Constrained Monotonic Neural Networks: Achieving
Universal Approximation Beyond Bounded Activations"*, arXiv:2505.02537.
**Relationship:** builds directly on the merged Mikulincer–Reichman development
(`UniversalApproximation/Monotone/`). This project introduces a **shared core** that unifies both:
M-R becomes the exact/threshold special case of a general saturating-activation construction.

## Goal

Formalize, `sorry`-free, the three theoretical results of Sartor et al.:
- **Theorem 3.5 (Result 1):** a non-negative-weight MLP with 3 hidden layers (4 total) and monotone
  activations that **alternate saturation sides** interpolates any monotone non-decreasing function
  on any finite point set.
- **Proposition 3.10 (equivalence):** two consecutive non-positive-weight layers with activation `σ`
  equal a non-negative-weight pair with the point-reflected activation `σ'(x) = −σ(−x)`
  (weight-sign ↔ saturation-side).
- **Proposition 3.11 (Result 2/3):** a 4-layer MLP with non-positive weights and a one-side-saturating
  activation `σ ∈ 𝒮⁻ ∪ 𝒮⁺` is a universal approximator for monotone functions (incl. the convex/ReLU
  case, contrasting Prop 3.2's non-negative-weight convexity limitation).

…done via a factorization that also **re-derives the M-R theorems** as the exact special case.

## Frozen invariants

- The two merged M-R headlines keep **byte-identical statements** and axiom profile
  `[propext, Classical.choice, Quot.sound]`:
  `UniversalApproximation.Monotone.monotone_interpolation`, `monotone_approximation`. Their *proofs*
  are refactored to route through the shared core (M-R = the ε=0 / threshold instance). The public
  interface symbols the headlines name — `MonoNet`, `MonoNet.toFun`, `MonoNet.depth`,
  `MonoNet.IsMonotone` — keep their signatures and faithful meanings.
- New Sartor headlines are added (statements per the paper — see the faithfulness gate below).
- No `sorry`/`admit`; no `set_option maxHeartbeats` in committed code; lines ≤ 100 codepoints;
  docstrings on public declarations. A research-grade blocker is reported `NEEDS_CONTEXT`, never
  hidden as `sorry` or worked around by weakening a statement.

## The factorization (shared core)

1. **Generalized model (`Defs`).** Lift the threshold-only `ThreshStack` to a **monotone-activation
   MLP**: a layered non-negative-weight network where each layer carries an activation `σ` with
   `Monotone σ`; `heaviside` is one instance. Preserve `MonoNet`'s public interface so the M-R
   headline still elaborates (the generalization is in how a layer's activation is supplied; the
   threshold stack is recovered by using `heaviside` at every layer).
2. **Indicator-gadget abstraction (`Indicator`).** `IsEpsIndicator G p ε` — a monotone,
   non-negative-weight sub-network `G` with `∀ x, |G x − 𝟙[p ≤ x]| ≤ ε` (coordinatewise domination).
   Threshold gives `ε = 0`; a monotone alternating-saturation activation with internal gain `λ` gives
   `ε = ε(λ) → 0`.
3. **One interpolation engine (`Interpolation`).** Over any gadget family: reindex the monotone
   dataset (`Basic.sort_key_linear_extension`) → level-sets → telescoping non-negative read-out ⇒
   interpolation with error controlled by ε and the read-out spread. `ε = 0` collapses to exact
   `N xᵢ = yᵢ`.
4. **Instances.** Threshold gadget (`ε = 0`) ⇒ M-R `monotone_interpolation` (exact). Alternating-
   saturation gadget (half-space indicator from monotone `𝒮⁺`/`𝒮⁻` activations) ⇒ Sartor Thm 3.5.
5. **Corollaries.** `Equivalence` (Prop 3.10): the point-reflection `σ'(x) = −σ(−x)` and the
   non-positive ↔ non-negative-weight layer-pair transformation (Prop 3.8 gives `σ'` monotone with
   opposite saturation). `NonPositive` (Prop 3.11 + Result 3): non-positive-weight / one-side-
   saturating / convex-monotone instances of the universal-approximation statement.

## Faithful statements

M-R headlines: unchanged (frozen).

Sartor headlines (namespace `UniversalApproximation.Monotone`, names provisional):
- `saturating_interpolation` — Theorem 3.5.
- `nonpos_weight_universal` — Proposition 3.11.
- an equivalence lemma for Proposition 3.10.

Activation predicates: `RightSaturating σ := ∃ L, Tendsto σ atTop (𝓝 L)`, `LeftSaturating` dually
(Definition 3.3); `AlternatingSaturation` for the 3-hidden-layer side pattern (𝒮⁻,𝒮⁺,𝒮⁻ or the
reverse). The shared engine's ε-approximate interpolation statement is
`∀ ε > 0, ∃ N, N.IsMonotone ∧ N.depth = 4 ∧ ∀ i, |N.toFun (x i) − y i| ≤ ε`, with the exact form
(`= y i`) as the `ε = 0` gadget corollary (M-R).

### ⚠ Faithfulness gate (resolve from the PRIMARY source before Phase 2 — do NOT guess)

Two summarizer reads of the paper conflict on whether **Theorem 3.5 is EXACT interpolation
(`gθ(xᵢ) = f(xᵢ)`) or ε-APPROXIMATE** (Lemmas 3.6/3.7 state "≈"; the theorem allegedly states exact,
with `λ→∞` only in the proof). This is mathematically load-bearing: strictly-monotone saturating
activations never *attain* their limits, so an *exact* finite-net statement would require either
activations that attain saturation, or an exact read-out solve against sharp-but-approximate level-set
indicators. **Before implementing Phase 2**, read the actual Theorem 3.5 statement + the Lemma
3.6/3.7 proofs from the paper PDF/source and finalize (a) the exact vs `∀ε` form of
`saturating_interpolation`, and (b) whether the ε-gadget engine captures the paper's mechanism or the
engine needs an exact-solve variant. The shared core is designed to prove the `∀ε` form with exact as
`ε = 0`; if the paper's Thm 3.5 is genuinely exact via a different mechanism, adjust the Sartor
headline + the gadget→interpolation lemma accordingly (report `NEEDS_CONTEXT` if the mechanism cannot
be reconstructed faithfully). Working assumption until then: `∀ε` approximate interpolation.

## File structure (under `NeuralNetworkProofs/UniversalApproximation/Monotone/`)

- `Defs.lean` — **generalize** the model to activation-parametric monotone MLP (`heaviside` an
  instance); preserve the frozen `MonoNet` interface.
- `Basic.lean` — reuse (`sort_key_linear_extension`, `sum_le_one_card_le_iff`, `dist_le_of_coord`);
  add any general saturation/limit lemmas here.
- `Indicator.lean` — new: `IsEpsIndicator` abstraction + the threshold instance (generalizing the
  current `Domination.lean`) + the saturating-activation instance.
- `Interpolation.lean` — **refactor** to the gadget-based engine; M-R exact interpolation becomes the
  `ε = 0` corollary (behavior-preserving at the frozen headline).
- `Saturating.lean` — new: `RightSaturating`/`LeftSaturating`/alternation predicates + Theorem 3.5.
- `Equivalence.lean` — new: Prop 3.8 (`σ'` monotone, opposite saturation) + Prop 3.10.
- `NonPositive.lean` — new: Prop 3.11 + Result 3 (non-positive weights, convex/ReLU).
- `Grid.lean`, `Approximation.lean` — reuse (grid, monotone-dataset, approximation-from-interpolation).
- `Monotone.lean` — re-export the new headlines.

**Historical notes.** Record the M-R proof generalization: a short note in this repo's docs and a line
in the affected module docstrings ("proof refactored through the shared ε-indicator engine;
originally the standalone threshold construction of PR #16"). Git history + PRs also track it.

## Execution & verification

- **Subagent-driven** (one implementer + reviewer per file; controller commits + runs gates).
- **Phased** (likely one PR each):
  - **Phase 1** — generalized `Defs` model + `Indicator` abstraction + refactor `Interpolation` to the
    engine + **re-derive M-R** (both frozen headlines byte-identical + axiom-clean). Behavior-preserving.
  - **Phase 2** — `Saturating` + Theorem 3.5 (after the faithfulness gate is resolved).
  - **Phase 3** — `Equivalence` (Prop 3.10) + `NonPositive` (Prop 3.11 / Result 3).
- **Gate per phase:** full `lake build` green; every headline (M-R + new) `[propext, Classical.choice,
  Quot.sound]` on fresh oleans; `scripts/check_sorry_free.lean` extended to the new headlines and
  clean; no `maxHeartbeats`; ≤ 100 codepoints.
- **Deferred signing:** execution commits unsigned; batch-sign only the unpushed commits before each
  PR (repo blocks force-push); PR opened only after every commit shows `G`.

## Out of scope

The empirical/architectural contribution (sign-adjusted activations, training-stability experiments);
any change to the frozen M-R headline statements; upstreaming to `ForMathlib/`.
