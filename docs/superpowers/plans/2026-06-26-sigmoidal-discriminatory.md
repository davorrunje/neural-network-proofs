# Closing `sigmoidal_discriminatory` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fully discharge `UniversalApproximation.sigmoidal_discriminatory` with a `sorry`-free proof.

**Architecture:** Build six bottom-up lemmas in a new `Discriminatory.lean`, following Cybenko via Mathlib's `Measure.ext_of_charFun`: sigmoidal→step (dominated convergence) ⇒ signed `μ` vanishes on half-spaces ⇒ per-direction real pushforward is `0` ⇒ characteristic function `0` ⇒ `μ = 0`.

**Tech Stack:** Lean 4, Mathlib v4.32.0-rc1, lake, lean-lsp MCP tools.

## Global Constraints

- Branch: `feat/discriminatory-proof`. Spec: `docs/superpowers/specs/2026-06-26-sigmoidal-discriminatory-design.md`.
- New code in `LeanPlayground/UniversalApproximation/Discriminatory.lean`, `namespace UniversalApproximation`, after `import Mathlib` and `import LeanPlayground.UniversalApproximation.Activation`.
- Header opens: `open MeasureTheory Filter Topology` and `open scoped RealInnerProductSpace`; `variable {n : ℕ}`.
- Inner product is written `⟪w, x⟫` (the `_ℝ` suffix does NOT parse — established in the scaffold).
- Reuse definitions from `Activation.lean`: `Sigmoidal` (fields `.continuous`, `.atBot : Tendsto σ atBot (𝓝 0)`, `.atTop : Tendsto σ atTop (𝓝 1)`), `signedIntegral μ g = ∫ x, g x ∂μ.toJordanDecomposition.posPart − ∫ x, g x ∂μ.toJordanDecomposition.negPart`, and `Discriminatory`.
- **Definition of done:** `lake build` succeeds; `sigmoidal_discriminatory` has **no `sorry`**; the ONLY remaining `sorry` in the whole project is `riesz_repr` (`Riesz.lean`). No change to any statement signature.
- **Lean iteration is expected.** Statements below are exact; proofs are given as strategy + named Mathlib lemmas. For every proof: write it, run `mcp__lean-lsp__lean_diagnostic_messages` (or `lean_goal` at a tactic position), and when stuck on a name use `lean_leansearch` / `lean_loogle` / `lean_hover_info`. A lemma is done when diagnostics show no `error` and no `sorry` for it.
- **Per-lemma discipline (TDD analogue):** (a) write the lemma with `:= by sorry`, confirm the *statement* elaborates (only a `sorry` warning); (b) replace `sorry` with the real proof, confirm no `sorry`; (c) commit. Never accumulate sorries across commits — each committed lemma is fully proved.
- **Contingency:** the goal is full closure. If a single sub-lemma proves intractable after sustained effort, leave *that lemma* as a clearly-docstringed `sorry`, prove everything downstream on top of it, and report it prominently — this still shrinks the gap. Do not silently sorry.
- Commit after each task. If a commit hangs on SSH signing, retry once with `-c commit.gpgsign=false` and continue.

---

### Task 1: Scaffold + `Sigmoidal.bounded`

**Files:** Create `LeanPlayground/UniversalApproximation/Discriminatory.lean`

**Interfaces — Produces:** `UniversalApproximation.Sigmoidal.bounded : Sigmoidal σ → ∃ C, ∀ t, |σ t| ≤ C`

- [ ] **Step 1: Write the file scaffold + lemma statement (with `sorry`)**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Activation

/-! # Discriminatory property of sigmoidal activations (Cybenko 1989, §3). -/

namespace UniversalApproximation

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A sigmoidal function is bounded: continuity plus finite limits at ±∞. -/
theorem Sigmoidal.bounded {σ : ℝ → ℝ} (hσ : Sigmoidal σ) : ∃ C, ∀ t, |σ t| ≤ C := by
  sorry

end UniversalApproximation
```

- [ ] **Step 2: Confirm the statement elaborates** — `lean_diagnostic_messages` on the file: only a `sorry` warning, no errors.

- [ ] **Step 3: Prove it.** Strategy: from `hσ.atTop` get `A` with `∀ t ≥ A, |σ t - 1| < 1` (so `|σ t| ≤ 2`); from `hσ.atBot` get `B` with `∀ t ≤ B, |σ t| < 1`. On the compact interval `Set.Icc (min A B) (max A B)`, `hσ.continuous` is bounded via `IsCompact.exists_bound_of_continuousOn` (or `IsCompact.bddAbove_image` on `|σ|`). Take `C` = max of the three bounds. Use `Metric.tendsto_atTop`/`Tendsto` ε-characterizations (`eventually` with ε=1) to extract `A`, `B`. Search: `lean_leansearch "continuous function on compact interval is bounded"`, `lean_loogle "IsCompact.exists_bound"`.

- [ ] **Step 4: Verify** — `lean_diagnostic_messages`: no errors, no `sorry`.

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Discriminatory.lean
git commit -m "feat(uat): Discriminatory.lean scaffold + Sigmoidal.bounded"
```

---

### Task 2: `sigmoidal_tendsto_pos` / `sigmoidal_tendsto_neg`

**Interfaces — Consumes:** `Sigmoidal` (`.atTop`, `.atBot`). **Produces:**
- `sigmoidal_tendsto_pos : Sigmoidal σ → 0 < t → Tendsto (fun m : ℕ => σ (m * t + φ)) atTop (𝓝 1)`
- `sigmoidal_tendsto_neg : Sigmoidal σ → t < 0 → Tendsto (fun m : ℕ => σ (m * t + φ)) atTop (𝓝 0)`

- [ ] **Step 1: Statements (with `sorry`)**
```lean
theorem sigmoidal_tendsto_pos {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) atTop (𝓝 1) := by
  sorry

theorem sigmoidal_tendsto_neg {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : t < 0) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) atTop (𝓝 0) := by
  sorry
```

- [ ] **Step 2: Confirm statements elaborate.**

- [ ] **Step 3: Prove.** Both are `Tendsto.comp` of `hσ.atTop` / `hσ.atBot` with the inner `fun m : ℕ => (m : ℝ) * t + φ` tending to `atTop` (pos) / `atBot` (neg). Inner limit: `(m : ℝ) → atTop` via `tendsto_natCast_atTop_atTop`; multiply by `t > 0` via `Tendsto.atTop_mul_const ht` (and `Tendsto.atTop_mul_neg_const` / `Tendsto.atBot` for `t < 0`); add `φ` via `tendsto_atTop_add_const_right` / `tendsto_atBot_add_const_right`. Search exact names with `lean_loogle "Tendsto _ atTop atTop"`, `lean_leansearch "natCast tendsto atTop"`.

- [ ] **Step 4: Verify** — no errors, no `sorry`.

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Discriminatory.lean
git commit -m "feat(uat): sigmoidal scaled-shift step limits"
```

---

### Task 3: `signed_halfspace_eq_zero` (the analytic crux)

**Interfaces — Consumes:** `Sigmoidal.bounded`, `sigmoidal_tendsto_pos/neg`, `signedIntegral`. **Produces:**
`signed_halfspace_eq_zero : Sigmoidal σ → (∀ w b, signedIntegral μ (fun x => σ (⟪w, (x:EuclideanSpace ℝ (Fin n))⟫ + b)) = 0) → ∀ w b, (μ {x | 0 < ⟪w, (x:EuclideanSpace ℝ (Fin n))⟫ + b} = 0 ∧ μ {x | ⟪w, (x:EuclideanSpace ℝ (Fin n))⟫ + b = 0} = 0)`

- [ ] **Step 1: Statement (with `sorry`)**
```lean
variable {σ : ℝ → ℝ} {K : Set (EuclideanSpace ℝ (Fin n))}

theorem signed_halfspace_eq_zero (hσ : Sigmoidal σ) {μ : SignedMeasure ↥K}
    (H0 : ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0)
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    μ {x : ↥K | 0 < ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b} = 0 ∧
    μ {x : ↥K | ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b = 0} = 0 := by
  sorry
```
(`μ s` is the signed measure of a set; `SignedMeasure α = VectorMeasure α ℝ` coerces to a set-function. Confirm the coercion spelling via `lean_hover_info` on `SignedMeasure`; it may be `μ s` directly.)

- [ ] **Step 2: Confirm the statement elaborates** (measurability of the half-space/hyperplane sets is not needed to *state* it; it will be needed in the proof — the map `x ↦ ⟪w,x⟫ + b` is continuous, sets are preimages of `Ioi`/`{0}`).

- [ ] **Step 3: Prove.** Decompose into sub-goals (heavy MCP iteration expected here):
  1. **Per-`m` instances.** For every `m : ℕ` and `φ`, `signedIntegral μ (fun x => σ (m * (⟪w,x⟫+b) + φ)) = 0` by `H0 (m • w) (m * b + φ)`, rewriting `⟪(m:ℝ)•w, x⟫ = m * ⟪w,x⟫` (`real_inner_smul_left`) and `ring_nf`.
  2. **DCT on each Jordan part.** Let `μ⁺ := μ.toJordanDecomposition.posPart`, `μ⁻ := negPart` (finite measures; `IsFiniteMeasure` instances exist). Apply `MeasureTheory.tendsto_integral_of_dominated_convergence` with `bound := fun _ => C` (from `Sigmoidal.bounded`; constant is `Integrable` on a finite measure via `integrable_const`), `AEStronglyMeasurable` from `hσ.continuous.comp (...)`, and pointwise limit from Task 2 (split on `0 < ⟪w,x⟫+b`, `=0`, `<0`; the `m*(s)+φ` form matches Task 2 with `t = ⟪w,x⟫+b`). The limit integrand is `fun x => Set.indicator P 1 x + σ φ • Set.indicator Hy 1 x` where `P = {0 < ⟪w,x⟫+b}`, `Hy = {⟪w,x⟫+b = 0}`.
  3. **Evaluate the limit integral.** `∫ (indicator P 1 + σφ • indicator Hy 1) ∂μ± = μ±(P) + σφ • μ±(Hy)` via `integral_indicator_const` / `integral_indicator` (sets measurable). Subtracting the two parts: `signedIntegral`-limit `= μ(P) + σφ • μ(Hy)` (signed). Since every term in the sequence is `0`, the limit is `0`: `μ(P) + σφ • μ(Hy) = 0` for all `φ`.
  4. **Two values of `φ`.** `σ` is sigmoidal so `∃ φ₁ φ₂, σ φ₁ ≠ σ φ₂` (e.g. from `.atBot`/`.atTop`, values near `0` and `1`). The two equations `μ(P)+σφᵢ•μ(Hy)=0` give `(σφ₁ - σφ₂)•μ(Hy)=0 ⇒ μ(Hy)=0`, then `μ(P)=0`.
  Search as needed: `lean_leansearch "integral of indicator"`, `lean_loogle "tendsto_integral_of_dominated_convergence"`, `lean_hover_info` on `SignedMeasure.toJordanDecomposition`.

- [ ] **Step 4: Verify** — no errors, no `sorry`.

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Discriminatory.lean
git commit -m "feat(uat): signed measure vanishes on half-spaces (dominated convergence)"
```

---

### Task 4: `charFun_eq_zero` (Fourier transform of `μ` vanishes)

**Interfaces — Consumes:** `signed_halfspace_eq_zero`. **Produces:**
`charFun_eq_zero : Sigmoidal σ → (H0 …) → ∀ w, signedIntegral μ (fun x => Real.cos ⟪w,(x:E)⟫) = 0 ∧ signedIntegral μ (fun x => Real.sin ⟪w,(x:E)⟫) = 0`

(We express "characteristic function is zero" through its real and imaginary parts as `signedIntegral`s, which is exactly the form Task 5 consumes. This folds the per-direction-pushforward reasoning of the spec's lemma 4 into this step.)

- [ ] **Step 1: Statement (with `sorry`)**
```lean
theorem charFun_eq_zero (hσ : Sigmoidal σ) {μ : SignedMeasure ↥K}
    (H0 : ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0)
    (w : EuclideanSpace ℝ (Fin n)) :
    signedIntegral μ (fun x => Real.cos ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫) = 0 ∧
    signedIntegral μ (fun x => Real.sin ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫) = 0 := by
  sorry
```

- [ ] **Step 2: Confirm the statement elaborates.**

- [ ] **Step 3: Prove.** Plan: from `signed_halfspace_eq_zero` the signed measure of every half-space `{s < ⟪w,x⟫}` (take `b = -s`) and hyperplane is `0`. Two viable routes — try (a) first:
  (a) **Pushforward to ℝ.** Form `ν := VectorMeasure.map μ (fun x => ⟪w, (x:E)⟫)` (a `SignedMeasure ℝ`). Half-spaces give `ν (Set.Ioi s) = 0` for all `s` and `ν {c} = 0`. Show `ν = 0` via a signed/vector-measure extensionality on the `Ioi` π-system (search `lean_leansearch "signed measure determined by Ioi"`, `lean_loogle "VectorMeasure.ext"`; fall back to `MeasureTheory.ext_of_generate...` applied to the Jordan parts). Then `signedIntegral μ (g ∘ ⟪w,·⟫) = signedIntegral ν g = 0` for `g = cos, sin` by the change-of-variables/`integral_map` lemma on each Jordan part. 
  (b) **Step-function approximation** (fallback if (a)'s ext lemma is missing): `⟪w,·⟫` is bounded on compact `K`, so `cos`/`sin` of it are uniform limits of step functions over a finite interval partition; each interval indicator is a difference of half-space indicators, so its signed integral is `0`; pass to the uniform limit (μ finite) to get `0`.
  Heavy iteration expected; pick whichever of (a)/(b) the available Mathlib API supports, and report which.

- [ ] **Step 4: Verify** — no errors, no `sorry`.

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Discriminatory.lean
git commit -m "feat(uat): characteristic function of mu vanishes"
```

---

### Task 5: `sigmoidal_discriminatory` (assemble) + wire-up

**Files:**
- Modify `LeanPlayground/UniversalApproximation/Discriminatory.lean` (add the theorem)
- Modify `LeanPlayground/UniversalApproximation/Activation.lean` (remove the admitted `sigmoidal_discriminatory`)
- Modify `LeanPlayground/UniversalApproximation/Theorem.lean` and `LeanPlayground/UniversalApproximation.lean` (add `import LeanPlayground.UniversalApproximation.Discriminatory`)

**Interfaces — Consumes:** `charFun_eq_zero`. **Produces:** the proved `sigmoidal_discriminatory {n} {K} {σ} (hσ : Sigmoidal σ) : Discriminatory K σ` (same signature as the removed admit).

- [ ] **Step 1: Add the proved theorem to `Discriminatory.lean` (with `sorry` first)**
```lean
theorem sigmoidal_discriminatory {K : Set (EuclideanSpace ℝ (Fin n))} {σ : ℝ → ℝ}
    (hσ : Sigmoidal σ) : Discriminatory K σ := by
  intro μ H0
  sorry
```

- [ ] **Step 2: Remove the admit from `Activation.lean`.** Delete the `theorem sigmoidal_discriminatory … := by sorry` block there (keep the `Discriminatory` definition). This avoids a duplicate declaration.

- [ ] **Step 3: Add imports.** Prepend `import LeanPlayground.UniversalApproximation.Discriminatory` to `Theorem.lean` and to the root `UniversalApproximation.lean`. Confirm `Theorem.lean` still resolves `sigmoidal_discriminatory` (now from `Discriminatory.lean`).

- [ ] **Step 4: Confirm everything elaborates** with the single `sorry` now in `Discriminatory.sigmoidal_discriminatory` (run `lake build`; expect `sorry` warnings only at `Discriminatory.lean` (this proof) and `Riesz.lean`).

- [ ] **Step 5: Prove the assembly.** Strategy: `haveI : CompactSpace ↥K := …` if needed. Let `J := μ.toJordanDecomposition`; push both parts to `E` with `Measure.map (Subtype.val)` (measurable embedding: `K` compact ⇒ closed ⇒ measurable; `MeasurableEmbedding.subtype_coe`). From `charFun_eq_zero` (cos & sin integrals of the signed `μ` vanish for all `w`), derive `charFun (J.posPart.map Subtype.val) = charFun (J.negPart.map Subtype.val)` (equate real & imaginary parts; `charFun … w = ∫ e^{i⟪w,y⟫}`, and `integral_map` turns it into the `↥K` integral of `cos⟪w,x⟫ + i sin⟪w,x⟫`). Apply `MeasureTheory.Measure.ext_of_charFun` to get the two pushed measures equal, then `MeasurableEmbedding.injective`/`Measure.map` injectivity to get `J.posPart = J.negPart`, hence `μ = 0` (`SignedMeasure` is `0` iff its Jordan parts agree — `JordanDecomposition` ext / `toSignedMeasure` injective). Search: `lean_leansearch "measure map injective measurable embedding"`, `lean_hover_info` on `JordanDecomposition`, `Measure.ext_of_charFun`.

- [ ] **Step 6: Verify** — `lake build` succeeds; `lean_diagnostic_messages` on `Discriminatory.lean` shows no `sorry`; project-wide the only `sorry` is `Riesz.lean`'s `riesz_repr`. Confirm `#check @UniversalApproximation.sigmoidal_discriminatory` shows the original signature.

- [ ] **Step 7: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Discriminatory.lean \
        LeanPlayground/UniversalApproximation/Activation.lean \
        LeanPlayground/UniversalApproximation/Theorem.lean \
        LeanPlayground/UniversalApproximation.lean
git commit -m "feat(uat): prove sigmoidal_discriminatory via charFun uniqueness; wire up Discriminatory.lean"
```

---

## Self-Review (completed by plan author)

- **Spec coverage:** spec lemmas 1–6 → Tasks 1, 2, 3, (4 folds spec-lemma-4 into) 4, 5. File moves (remove admit, add imports) → Task 5. Verification/done criteria → Task 5 Step 6. ✓
- **Placeholder scan:** the only `sorry`s are the deliberate per-lemma "write statement first" steps, each followed by a prove-it step; no "TODO"/"handle edge cases".
- **Type consistency:** `signedIntegral μ g` (g : ↥K → ℝ), `Sigmoidal` field names (`.continuous/.atBot/.atTop`), the half-space set `{x : ↥K | 0 < ⟪w,(x:E)⟫ + b}`, and `sigmoidal_discriminatory`'s signature all match `Activation.lean` and the spec. Task 4 outputs cos/sin `signedIntegral`s exactly as Task 5 consumes them.
- **Known risk:** Tasks 3 and 4 are the analytic core (dominated convergence; signed pushforward / measure-uniqueness on a π-system). Each has an explicit search-and-iterate step and, for Task 4, an (a)/(b) fallback. If one stays open after real effort, isolate it as a docstringed `sorry` and report (per the Global Constraints contingency) — the gap still shrinks.
