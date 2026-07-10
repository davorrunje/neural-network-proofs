# Closing `sigmoidal_discriminatory` — Design Spec

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

**Date:** 2026-06-26
**Status:** Approved (design) — pending spec review
**Goal:** Fully discharge the admitted lemma `UniversalApproximation.sigmoidal_discriminatory` (continuous sigmoidal ⇒ discriminatory) with a complete, `sorry`-free Lean 4 / Mathlib proof, following Cybenko (1989) via the characteristic-function uniqueness theorem now available in Mathlib.

## Context

The merged UAT scaffold (`LeanPlayground/UniversalApproximation/`) leaves exactly two admitted lemmas: `riesz_repr` and `sigmoidal_discriminatory`. This effort closes **`sigmoidal_discriminatory`** (the more tractable of the two: all required Mathlib tools already exist, with no missing foundational theorem). `riesz_repr` is out of scope for this cycle.

Current statement (in `Activation.lean`):

```lean
def Discriminatory (K : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ → ℝ) : Prop :=
  ∀ μ : SignedMeasure ↥K,
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0) → μ = 0

theorem sigmoidal_discriminatory {n} {K} {σ} (hσ : Sigmoidal σ) : Discriminatory K σ := by sorry
```

where `signedIntegral μ g = ∫ g ∂μ.toJordanDecomposition.posPart − ∫ g ∂μ.toJordanDecomposition.negPart` and `Sigmoidal σ` packages `Continuous σ`, `Tendsto σ atBot (𝓝 0)`, `Tendsto σ atTop (𝓝 1)`.

## Proof strategy (Cybenko via characteristic functions)

Given a signed measure `μ` on `↥K` with `∫ σ(⟪w,x⟫+b) dμ = 0` for all `w, b`:

1. Because the hypothesis quantifies over **all** `w, b`, it already covers `σ(λ(⟪w,x⟫+b)+φ)` (take `w' = λw`, `b' = λb+φ`). As `λ → ∞`, `σ(λt+φ) →` `1` (`t>0`) / `0` (`t<0`) / `σ φ` (`t=0`).
2. **Bounded convergence** (σ bounded, μ finite) ⇒ `σ(φ)·μ(H_{w,b}) + μ(P_{w,b}) = 0` for hyperplane `H` and open half-space `P`. Letting `φ→±∞`: `μ(P)=0` and `μ(H)=0` for every half-space.
3. For each `w`, the real pushforward `(⟪w,·⟫)_*μ` has all tails `(s,∞)` zero ⇒ it is the zero signed measure.
4. Hence `∫ e^{i⟪w,x⟫} dμ = 0` for all `w`.
5. Push `μ` forward to the ambient `E = EuclideanSpace ℝ (Fin n)`, Jordan-split `μ = μ⁺ − μ⁻`; step 4 gives `charFun (push μ⁺) = charFun (push μ⁻)`, so **`Measure.ext_of_charFun`** ⇒ `push μ⁺ = push μ⁻`; injectivity of the embedding pushforward ⇒ `μ⁺ = μ⁻` ⇒ `μ = 0`.

Rejected alternatives: `FiniteMeasure.ext_of_forall_integral_eq` (reaching its hypothesis is circular with UAT); pure Cramér–Wold (realized in Mathlib *through* `charFun` anyway).

## File layout

- **`Activation.lean`** — keep the definitions (`Sigmoidal`, `Discriminatory`, `signedIntegral`); **remove** the admitted `sigmoidal_discriminatory`.
- **`LeanPlayground/UniversalApproximation/Discriminatory.lean`** (new) — imports `Activation`; contains the 6 lemmas below and the proved `sigmoidal_discriminatory`.
- **`Theorem.lean`** and **`UniversalApproximation.lean`** (root) — add `import LeanPlayground.UniversalApproximation.Discriminatory` (they already use the theorem via the namespace).

## Lemma decomposition (`Discriminatory.lean`, namespace `UniversalApproximation`)

1. `Sigmoidal.bounded : Sigmoidal σ → ∃ C, ∀ t, |σ t| ≤ C` — continuous with finite limits at ±∞ ⇒ bounded (compact-away-from-ends + bounded tails).
2. `sigmoidal_tendsto_step` — pointwise limit of `n ↦ σ(n·t+φ)` as `n → ∞` (ℕ-indexed): `1` if `t>0`, `0` if `t<0`, `σ φ` if `t=0`.
3. `signed_halfspace_eq_zero` — from the hypothesis + `tendsto_integral_of_dominated_convergence` (bound `C` from lemma 1, integrable on finite `μ⁺/μ⁻`): for all `w,b`, signed `μ(P_{w,b}) = 0` and `μ(H_{w,b}) = 0`.
4. `pushforward_dir_eq_zero` — for each `w`, `(⟪w,·⟫)_*μ` (real signed measure) has all tails zero ⇒ is `0`.
5. `charFun_eq_zero` — hence `∫ cos⟪w,x⟫ dμ = ∫ sin⟪w,x⟫ dμ = 0`, i.e. `charFun (push μ⁺) = charFun (push μ⁻)`.
6. `sigmoidal_discriminatory` — assemble via Jordan + `Measure.map Subtype.val` to `E` + `Measure.ext_of_charFun` + embedding-pushforward injectivity.

## Confirmed Mathlib dependencies

- `MeasureTheory.charFun : Measure E → E → ℂ` (`charFun μ t = ∫ e^{i⟪t,x⟫} dμ`).
- `MeasureTheory.Measure.ext_of_charFun` — finite measures on `E` with `[InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]`; `EuclideanSpace ℝ (Fin n)` satisfies all.
- `MeasureTheory.tendsto_integral_of_dominated_convergence` (ℕ-indexed).
- `MeasureTheory.SignedMeasure.toJordanDecomposition` (→ finite `posPart`, `negPart`); `MeasureTheory.Measure.map`.

## Risks / fiddly points

1. **Subtype → ambient.** `μ` is on `↥K`; `charFun`/`ext_of_charFun` need a measure on `E`. Jordan-split on `↥K`, push `μ⁺,μ⁻` to `E` via `Measure.map Subtype.val` (measurable embedding: `K` compact ⇒ measurable), apply `ext_of_charFun` there, then embedding-pushforward injectivity returns `μ⁺=μ⁻` on `↥K`. Avoids `VectorMeasure.map`.
2. **Signed ⇒ positive.** `charFun` is for positive measures; only ever apply to `μ⁺,μ⁻`. Step 5 = "`charFun (push μ⁺) = charFun (push μ⁻)`".
3. **ℕ-indexed DCT.** Use `λ = n → ∞`; bound `|σ(n·t+φ)| ≤ C` (constant, integrable on finite measure); continuity ⇒ `AEStronglyMeasurable`.
4. **Hyperplane boundary.** The step limit on `H` is `σ(φ)`; kill it by deriving `μ(H)=0` separately (the `φ→±∞` subtraction) so the boundary value never enters the final integrals. Fiddliest step.
5. **charFun convention.** Only equality of the two charFuns is used (their difference is `0`), so the exact sign/normalization convention is immaterial as long as it is consistent.

## Verification

- Each of the 6 lemmas builds clean via `lean_diagnostic_messages` (no `error`-severity items).
- `sigmoidal_discriminatory` ends with **no `sorry`**.
- Full `lake build` succeeds; afterward the **only** remaining `sorry` in the entire project is `riesz_repr` (`Riesz.lean`).
- `#check @UniversalApproximation.sigmoidal_discriminatory` shows the unchanged statement type (proof closed, signature intact, so `Theorem.lean`/`universal_approximation` are unaffected).

## Out of scope

`riesz_repr` (a separate cycle); any change to the UAT statement, the network definitions, or `Discriminatory`'s definition; upstreaming reusable lemmas to Mathlib (a possible follow-up).

## Reference

Cybenko, G. (1989). *Approximation by superpositions of a sigmoidal function.* Mathematics of Control, Signals, and Systems, 2(4): 303–314, §3 (discriminatory property). [doi:10.1007/BF02551274](https://link.springer.com/article/10.1007/BF02551274)
