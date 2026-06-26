# Riesz–Kantorovich (Mathlib-bound) + completing the UAT — Design Spec

**Date:** 2026-06-26
**Status:** Approved (design) — pending spec review
**Goal:** (Part 1) Formalize the Riesz–Kantorovich decomposition for order-bounded linear functionals on a real vector lattice — a fully `sorry`-free, general, Mathlib-upstream-ready result. (Part 2) Use it to discharge the last admitted lemma `UniversalApproximation.riesz_repr`, making the entire UAT development `sorry`-free.

## Context

The UAT scaffold has one remaining admit: `riesz_repr` (signed/dual Riesz representation of `(C(K,ℝ))*`). A feasibility probe showed Mathlib has the *positive* Riesz–Markov–Kakutani theorem (`RealRMK`) and its injectivity, plus function-level positive parts (`nnrealPart`), but **not** the decomposition of a bounded *functional* into positive parts — the **Riesz–Kantorovich** theorem (the order-bounded dual of a vector lattice is a lattice). That single classical theorem is the whole gap.

The user wants to contribute this missing theorem to Mathlib. So this cycle has two parts: a general, upstream-ready RK formalization (Part 1), and its application to finish the UAT (Part 2).

### Mathlib state (researched)

- ❌ Riesz–Kantorovich / order-bounded-dual-is-a-lattice: **absent** (only unrelated lattice instances exist; web search found the classical literature but no Lean formalization — **to be reconfirmed on the Mathlib Zulip before upstreaming**).
- ❌ Riesz decomposition (interpolation) property as a named lemma: absent, but elementary (`a := z ⊓ x`).
- ✅ Vector-lattice infrastructure: `Lattice`, `IsOrderedAddMonoid`, `Module ℝ`, ordered `smul`, `PosPart`/`NegPart` (`⁺`/`⁻`); `ℝ` conditionally complete.
- ✅ Positive RMK: `RealRMK.rieszMeasure`, `RealRMK.integral_rieszMeasure`, `RealRMK.integralPositiveLinearMap_inj`; `CompactlySupportedContinuousMap.integralPositiveLinearMap`.

## Part 1 — Riesz–Kantorovich (general, Mathlib-bound)

**Setting.** `E` a real vector lattice: `[Lattice E] [AddCommGroup E] [IsOrderedAddMonoid E] [Module ℝ E]` + ordered scalar multiplication (`PosSMulMono`/`OrderedSMul ℝ E`). Codomain `ℝ` (conditionally complete). Exact instance bundle to be pinned against Mathlib during planning.

**Order-bounded functional.** `L : E →ₗ[ℝ] ℝ` is order-bounded if `{L g | 0 ≤ g ≤ f}` is bounded above in `ℝ` for every `f ≥ 0`.

**Construction.** For order-bounded `L`, on the positive cone
`Lpos f := sSup { L g | 0 ≤ g ∧ g ≤ f }` (`f ≥ 0`), extended to all `E` by `Lpos x := Lpos x⁺ − Lpos x⁻`.

**Lemma chain (each named):**
1. `riesz_decomp` — `0 ≤ z ≤ x+y ⇒ ∃ a b, z = a+b ∧ 0≤a≤x ∧ 0≤b≤y` (take `a := z ⊓ x`).
2. `Lpos` well-defined — the `sSup` exists (order-boundedness + `ℝ` conditionally complete; `g=0` gives nonempty).
3. `Lpos` additive on the positive cone — the crux, via `riesz_decomp`.
4. `Lpos` positively homogeneous ⇒ extends to a linear `E →ₗ[ℝ] ℝ`.
5. `Lpos` positive (`0≤f ⇒ 0≤Lpos f`) and dominates `L` (`L f ≤ Lpos f` for `f≥0`).

**Deliverables (in order of robustness):**
1. The lemma chain above (verified core).
2. `exists_positive_decomposition : ∃ Lp Lm : E →ₗ[ℝ] ℝ, (∀ f, 0≤f → 0≤Lp f) ∧ (∀ f, 0≤f → 0≤Lm f) ∧ ∀ x, L x = Lp x − Lm x` — the robust headline; exactly what Part 2 consumes.
3. The **`Lattice` instance** on the order-bounded dual with the RK formula for `⊔`/`⊓` — the idiomatic Mathlib capstone. If proving every lattice axiom proves disproportionately heavy, #2 is the guaranteed deliverable and #3 is the capstone (the aim is #3).

**File (staging).** `LeanPlayground/Contrib/RieszKantorovich.lean` — self-contained, **no playground deps**, written in Mathlib style with a header comment naming the intended Mathlib home (likely `Mathlib/Analysis/Order/` or `Mathlib/Order/`, to be confirmed with maintainers) and flagging it as an upstream-staging copy.

**Mathlib-readiness conventions:** module + per-declaration docstrings; `UpperCamelCase` types / `lowerCamelCase` terms / Mathlib theorem naming; ≤100-char lines; general typeclass hypotheses only; developed against `import Mathlib` (imports trimmed to specific modules at PR time); **fully `sorry`-free**.

## Part 2 — Close `riesz_repr` (UAT, in-repo)

Edits in `LeanPlayground/UniversalApproximation/Riesz.lean` (the `riesz_repr` statement/signature is unchanged):

1. **Instances** — `C(↥K,ℝ)` is a real vector lattice; pull in Mathlib's `ContinuousMap` lattice + ordered-module instances (verify all present for compact domain).
2. **Order-bounded bridge** — a continuous `L : C(↥K,ℝ) →L[ℝ] ℝ` is order-bounded: on compact `K`, `0≤g≤f ⇒ ‖g‖ ≤ ‖f‖`, so `|L g| ≤ ‖L‖·‖f‖`.
3. Apply Part 1's `exists_positive_decomposition` ⇒ `L = L⁺ − L⁻`, both positive.
4. **RealRMK assembly** — bridge each positive functional to `CompactlySupportedContinuousMap ↥K ℝ →ₚ[ℝ] ℝ` (compact ⇒ all continuous maps compactly supported); `RealRMK.rieszMeasure` ⇒ regular `μ⁺, μ⁻`; set `μ := μ⁺.toSignedMeasure − μ⁻.toSignedMeasure`.
5. Show `signedIntegral μ g = ∫ g ∂μ⁺ − ∫ g ∂μ⁻ = L g` (independence of the signed-measure integral from the chosen finite-measure difference) and `L = 0 ↔ μ = 0` (`integralPositiveLinearMap_inj` / measure-from-integrals uniqueness) ⇒ **remove the `sorry`**.

**End state:** the entire UAT development is `sorry`-free, and `Contrib/RieszKantorovich.lean` is a general, upstream-ready file.

## Risks / fiddly points

- **Typeclass bundle** for "real vector lattice" — pin the exact Mathlib instances (`OrderedSMul` vs `PosSMulMono`, etc.) early.
- **`Lpos` additivity** (Part 1 step 3) is the analytic crux; depends on `riesz_decomp` and careful `sSup` manipulation.
- **Full `Lattice` instance** (Part 1 #3) may be heavy; `exists_positive_decomposition` is the fallback-robust deliverable.
- **`signedIntegral`-of-difference identity** (Part 2 step 5): `signedIntegral` is defined via the Jordan decomposition, which need not equal `(μ⁺, μ⁻)`; prove the integral is independent of the chosen finite-measure difference.
- **C(K) ↔ CompactlySupportedContinuousMap** bridge for compact `K` — confirm the cleanest Mathlib path (equiv/coercion).

## Verification

- `lake build` clean — **no `sorry`, no errors** in `Contrib/RieszKantorovich.lean` and across the UAT files.
- `#print axioms` on `exists_positive_decomposition` and on `UniversalApproximation.riesz_repr` ⇒ only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- Project-wide `sorry` inventory is **empty** (UAT fully closed).
- `riesz_repr` signature unchanged ⇒ `universal_approximation` and the rest of the UAT still build.
- Keep `Contrib/RieszKantorovich.lean` lint-clean locally; real Mathlib `lake exe runLinter` is a pre-PR step on the fork (user-driven).

## Out of scope

General-operator RK (codomain a Dedekind-complete vector lattice); signed/complex RMK as a standalone Mathlib contribution; the actual Mathlib fork/PR/Zulip submission (user-driven; we produce the upstream-ready file).

## References

- Riesz–Kantorovich: the order-bounded dual of a vector lattice is a lattice (classical; see e.g. Aliprantis–Burkinshaw, *Positive Operators*).
- Cybenko, G. (1989). *Approximation by superpositions of a sigmoidal function.* Math. Control Signals Systems 2:303–314 (the UAT this completes).
