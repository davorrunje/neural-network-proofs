# Universal Approximation Theorem — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a compiling Lean 4 / Mathlib *scaffold* of the Cybenko Universal Approximation Theorem (general n-D), with exactly two deep analytic lemmas admitted behind named declarations.

**Architecture:** Define a general feedforward neural network and the single-hidden-layer family `S` as a `Submodule` of `C(K,ℝ)`. State density as `(S σ K).topologicalClosure = ⊤`. Prove the structural steps (subspace, continuity, Hahn–Banach reduction, the contradiction logic); admit `riesz_repr` (signed-measure representation of `(C(K,ℝ))*`) and `sigmoidal_discriminatory`.

**Tech Stack:** Lean 4, Mathlib `v4.32.0-rc1`, `lake`, lean-lsp MCP tools.

## Global Constraints

- All code under `LeanPlayground/UniversalApproximation/` (existing `LeanPlayground` lib; `lakefile.toml` target `LeanPlayground`).
- Each file begins `import Mathlib` and lives in `namespace UniversalApproximation`.
- Input space: `EuclideanSpace ℝ (Fin n)`; inner product written `⟪w, x⟫` (`open scoped RealInnerProductSpace`).
- Domain: `K : Set (EuclideanSpace ℝ (Fin n))`, `hK : IsCompact K`; approximation space `C(↥K, ℝ)` = `ContinuousMap ↥K ℝ`.
- **Exactly two planned admits**, each a named lemma with a docstring (missing math + "Cybenko 1989, Math. Control Signals Systems 2:303–314") and a single `sorry`: `riesz_repr`, `sigmoidal_discriminatory`. A 3rd admit is allowed only for the logistic-sigmoidal sanity lemma if proving it is not quick. **No bare `sorry` inside other proofs.**
- **Definition of done per file:** `lean_diagnostic_messages` reports **no `error`-severity items**; the only `warning`s are `declaration uses 'sorry'` on the admitted lemmas (plus harmless linter style notes).
- **Lean iteration is expected.** For every step that writes Lean, the implementer MUST loop: write → `mcp__lean-lsp__lean_run_code` or `lean_diagnostic_messages` → if errors, use `lean_leansearch` / `lean_loogle` / `lean_local_search` / `lean_hover_info` to find correct Mathlib names and fix → repeat until the done criterion holds. Exact Mathlib lemma names in this plan are best-effort; verify each before relying on it.
- Commit after each task. **If a commit fails (e.g. signing), continue anyway** and note it; do not block.

---

### Task 1: Scaffold + Activation definitions

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Activation.lean`

**Interfaces:**
- Produces: `UniversalApproximation.Sigmoidal : (ℝ → ℝ) → Prop` (fields `.continuous`, `.atBot`, `.atTop`); `UniversalApproximation.Discriminatory : Set (EuclideanSpace ℝ (Fin n)) → (ℝ → ℝ) → Prop`; `sigmoidal_discriminatory : Sigmoidal σ → Discriminatory K σ` (ADMITTED).

- [ ] **Step 1: Write the file**

```lean
import Mathlib

/-!
# Activation functions for the Universal Approximation Theorem
Defines the `Sigmoidal` predicate (Cybenko) and the `Discriminatory` predicate
that drives the Hahn–Banach/Riesz argument.
-/

namespace UniversalApproximation

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A continuous **sigmoidal** function (Cybenko 1989): continuous, with limit
`0` at `-∞` and `1` at `+∞`. -/
structure Sigmoidal (σ : ℝ → ℝ) : Prop where
  continuous : Continuous σ
  atBot : Tendsto σ atBot (𝓝 0)
  atTop : Tendsto σ atTop (𝓝 1)

/-- `σ` is **discriminatory** for the compact set `K`: the only signed measure
annihilating every superposition `x ↦ σ(⟪w,x⟫ + b)` is the zero measure. This is
the hypothesis the Riesz step of the UAT proof needs. -/
def Discriminatory (K : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ → ℝ) : Prop :=
  ∀ μ : SignedMeasure K,
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        ∫ x, σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) ∂μ.toJordanDecomposition.posPart
      - ∫ x, σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) ∂μ.toJordanDecomposition.negPart = 0)
      → μ = 0

/-- **ADMITTED (roadmap).** A continuous sigmoidal function is discriminatory.
Cybenko 1989 (Math. Control Signals Systems 2:303–314), §3: a Fourier/measure
argument. Discharging this is roadmap item 2. -/
theorem sigmoidal_discriminatory
    {K : Set (EuclideanSpace ℝ (Fin n))} {σ : ℝ → ℝ}
    (hσ : Sigmoidal σ) : Discriminatory K σ := by
  sorry

end UniversalApproximation
```

- [ ] **Step 2: Verify it compiles**

Run `mcp__lean-lsp__lean_diagnostic_messages` on the file (save first).
Expected: no `error` items; one `warning` = `declaration uses 'sorry'` at `sigmoidal_discriminatory`.
If `SignedMeasure`/integral API errors: confirm the integral-against-signed-measure spelling via `lean_leansearch "integral with respect to signed measure"` and `lean_hover_info` on `SignedMeasure.toJordanDecomposition`. The Jordan posPart/negPart difference is the intended faithful spelling; adjust to the exact Mathlib API. Keep `Discriminatory` measure-based.

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Activation.lean
git commit -m "feat(uat): activation predicates (Sigmoidal, Discriminatory) + admitted sigmoidal_discriminatory"
```

---

### Task 2: General feedforward network + continuity

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Network.lean`

**Interfaces:**
- Produces: `UniversalApproximation.Layer (a b : ℕ)` (weights + bias); `Network` (input dim, list of layers, output dim) with `Network.toFun : (Fin nIn → ℝ) → (Fin nOut → ℝ)`; `Network.continuous_toFun : Continuous σ → Continuous net.toFun`.

- [ ] **Step 1: Write the file**

```lean
import Mathlib

/-!
# Feedforward neural networks
A `Network` is a chain of affine-then-pointwise-activation layers. We prove its
denotation is continuous when the activation is.
-/

namespace UniversalApproximation

open scoped Matrix

variable (σ : ℝ → ℝ)

/-- One layer: an affine map `Fin a → ℝ`  ↦  `Fin b → ℝ` (weights `W`, bias `c`)
followed by pointwise activation `σ`. -/
structure Layer (a b : ℕ) where
  W : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ

/-- The function a layer computes (activation applied componentwise). -/
def Layer.toFun {a b : ℕ} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => σ ((L.W.mulVec x) i + L.c i)

/-- A feedforward network as a heterogeneous chain of layers between dimensions
given by `dims : List ℕ` (head = input dim, last = output dim). Implemented as a
dependent fold; the executor may instead model it as an inductive type if that
elaborates more cleanly — keep `toFun` and the continuity lemma as the interface. -/
structure Network where
  nIn : ℕ
  nOut : ℕ
  -- A single hidden layer of width `h` plus a linear (no-activation) output map is
  -- sufficient for the theorem; the general chain is modeled here.
  toFun : (Fin nIn → ℝ) → (Fin nOut → ℝ)

/-- Componentwise activation of a continuous function is continuous. -/
theorem Layer.continuous_toFun {a b : ℕ} (hσ : Continuous σ) (L : Layer a b) :
    Continuous (L.toFun σ) := by
  apply continuous_pi
  intro i
  exact hσ.comp ((L.W.continuous_mulVec x?).add continuous_const) -- adjust to real API
```

- [ ] **Step 2: Verify + iterate**

Run `lean_diagnostic_messages`. The `Layer.continuous_toFun` proof is a sketch: use `lean_leansearch "matrix mulVec is continuous"` / `lean_loogle "Continuous (Matrix.mulVec _)"` to find the right continuity lemma (candidates: `Matrix.mulVec` continuity via `continuous_matrix`/`LinearMap`/`Matrix.mulVecLin` as a `ContinuousLinearMap` in finite dimension). Reduce `Network` to whatever model (struct-with-`toFun`, inductive chain, or `List`-fold) compiles cleanly while preserving the interface. Done when no errors.

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Network.lean
git commit -m "feat(uat): feedforward Network/Layer definitions + continuity of denotation"
```

---

### Task 3: Generators and the family `S`

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Family.lean`

**Interfaces:**
- Consumes: `Sigmoidal` (Task 1); continuity facts (Task 2).
- Produces: `UniversalApproximation.generator (σ) (hσc : Continuous σ) (K hK) (w b) : C(↥K, ℝ)`; `UniversalApproximation.S (σ) (hσc) (K) (hK) : Submodule ℝ C(↥K, ℝ)`; `mem_S_iff_exists_finsum` characterizing membership as finite sums of generators.

- [ ] **Step 1: Write the file**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.UniversalApproximation.Network

/-!
# The single-hidden-layer family
The generators `x ↦ σ(⟪w,x⟫ + b)` and the submodule `S` of `C(K,ℝ)` they span.
-/

namespace UniversalApproximation

open scoped RealInnerProductSpace

variable {n : ℕ} (σ : ℝ → ℝ)

/-- The pre-activation `x ↦ ⟪w,x⟫ + b` is continuous. -/
theorem continuous_preactivation (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪w, x⟫ + b) :=
  (continuous_const.inner continuous_id).add continuous_const

/-- A single generator `x ↦ σ(⟪w,x⟫ + b)`, as a continuous map on the compact `K`. -/
def generator (hσc : Continuous σ) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) : C(↥K, ℝ) :=
  ⟨fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b),
    by have := hK.isCompact; fun_prop⟩  -- continuity; adjust to real API

/-- The single-hidden-layer family: the submodule of `C(K,ℝ)` spanned by all generators. -/
def S (hσc : Continuous σ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    Submodule ℝ C(↥K, ℝ) :=
  Submodule.span ℝ (Set.range fun wb : EuclideanSpace ℝ (Fin n) × ℝ =>
    generator σ hσc hK wb.1 wb.2)

end UniversalApproximation
```

- [ ] **Step 2: Verify + iterate**

Run `lean_diagnostic_messages`. For `generator` continuity: `↥K` carries the subspace topology; the map is `σ ∘ (preactivation ∘ Subtype.val)`. Use `Continuous.comp`, `continuous_subtype_val`, and `continuous_preactivation`; confirm `ContinuousMap` anonymous-constructor obligation via `lean_hover_info` on `ContinuousMap`. `fun_prop` may discharge it. Need `CompactSpace ↥K` (from `hK.compactSpace` / `isCompact_iff_compactSpace`) for the norm later, not for this file. Done when no errors.

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Family.lean
git commit -m "feat(uat): generators and the spanned family S ≤ C(K,ℝ)"
```

---

### Task 4: Riesz representation interface (ADMITTED)

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Riesz.lean`

**Interfaces:**
- Produces: `UniversalApproximation.riesz_repr` — for `L : C(↥K,ℝ) →L[ℝ] ℝ`, `∃ μ : SignedMeasure ↥K, (∀ g, L g = signedIntegral μ g) ∧ (L = 0 ↔ μ = 0)` (ADMITTED), where `signedIntegral μ g := ∫ x, g x ∂μ.toJordanDecomposition.posPart - ∫ x, g x ∂μ.toJordanDecomposition.negPart`.

- [ ] **Step 1: Write the file**

```lean
import Mathlib

/-!
# Riesz representation interface (ADMITTED — roadmap item 1)
The dual of `C(K,ℝ)` for compact `K` is represented by signed regular Borel
measures. Mathlib has Riesz–Markov–Kakutani for *positive* functionals; the
signed/dual form used here is the substantive gap. Cybenko 1989.
-/

namespace UniversalApproximation

open MeasureTheory

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- Integral of a continuous function against a signed measure, via its Jordan
decomposition. -/
noncomputable def signedIntegral (μ : SignedMeasure ↥K) (g : C(↥K, ℝ)) : ℝ :=
  (∫ x, g x ∂μ.toJordanDecomposition.posPart)
    - (∫ x, g x ∂μ.toJordanDecomposition.negPart)

/-- **ADMITTED (roadmap).** Riesz representation of `(C(K,ℝ))*` by signed measures. -/
theorem riesz_repr (L : C(↥K, ℝ) →L[ℝ] ℝ) :
    ∃ μ : SignedMeasure ↥K,
      (∀ g, L g = signedIntegral μ g) ∧ (L = 0 ↔ μ = 0) := by
  sorry

end UniversalApproximation
```

- [ ] **Step 2: Verify**

Run `lean_diagnostic_messages`. Expected: no errors; one `sorry` warning at `riesz_repr`. Confirm `SignedMeasure.toJordanDecomposition.posPart/negPart` names via `lean_hover_info`; align `signedIntegral` with the spelling chosen in Task 1's `Discriminatory` (they must match).

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Riesz.lean
git commit -m "feat(uat): admitted Riesz representation interface for (C(K,ℝ))*"
```

---

### Task 5: Hahn–Banach reduction + main theorem

**Files:**
- Create: `LeanPlayground/UniversalApproximation/Theorem.lean`

**Interfaces:**
- Consumes: `S`, `generator` (Task 3); `riesz_repr`, `signedIntegral` (Task 4); `Discriminatory`, `sigmoidal_discriminatory` (Task 1).
- Produces: `UniversalApproximation.dense_iff_forall_functional_eq_zero` (PROVED); `UniversalApproximation.universal_approximation` (main); `universal_approximation_eps` (ε-corollary).

- [ ] **Step 1: Write the file**

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.UniversalApproximation.Family
import LeanPlayground.UniversalApproximation.Riesz

/-!
# Universal Approximation Theorem (Cybenko, scaffold)
-/

namespace UniversalApproximation

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- **PROVED.** A subspace of `C(K,ℝ)` is dense iff every continuous linear
functional vanishing on it is zero. (Hahn–Banach reduction.) -/
theorem dense_iff_forall_functional_eq_zero
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (V : Submodule ℝ C(↥K, ℝ)) :
    V.topologicalClosure = ⊤ ↔
      ∀ L : C(↥K, ℝ) →L[ℝ] ℝ, (∀ g ∈ V, L g = 0) → L = 0 := by
  -- forward: dense ⇒ functional vanishing on V vanishes on closure = ⊤, hence 0.
  -- backward: if closure ≠ ⊤, Hahn–Banach (geometric_hahn_banach_point_closed /
  -- exists_extension_norm_eq) yields a nonzero L vanishing on V — contradiction.
  sorry  -- PROVE THIS (not an allowed admit); see Step 2.

/-- **Universal Approximation Theorem** (Cybenko, scaffold). The single-hidden-layer
family with a continuous sigmoidal activation is dense in `C(K,ℝ)`. -/
theorem universal_approximation
    (σ : ℝ → ℝ) (hσ : Sigmoidal σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    (S σ hσ.continuous hK).topologicalClosure = ⊤ := by
  haveI : CompactSpace ↥K := hK.compactSpace
  rw [dense_iff_forall_functional_eq_zero hK]
  intro L hL
  obtain ⟨μ, hμrepr, hμzero⟩ := riesz_repr L
  -- generators lie in S, so L (generator) = 0, i.e. signedIntegral μ (generator) = 0
  have hgen : ∀ w b, signedIntegral μ (generator σ hσ.continuous hK w b) = 0 := by
    intro w b
    have : generator σ hσ.continuous hK w b ∈ S σ hσ.continuous hK :=
      Submodule.subset_span ⟨(w, b), rfl⟩
    have := hL _ this
    rw [hμrepr] at this
    simpa using this
  -- discriminatory ⇒ μ = 0 ⇒ L = 0
  have : Discriminatory K σ := sigmoidal_discriminatory hσ
  have hμ : μ = 0 := this μ (by
    intro w b
    -- unfold signedIntegral to the posPart/negPart difference matching Discriminatory
    have := hgen w b
    simpa [signedIntegral] using this)
  exact hμzero.mpr hμ

/-- ε-form corollary. -/
theorem universal_approximation_eps
    (σ : ℝ → ℝ) (hσ : Sigmoidal σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (f : C(↥K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ S σ hσ.continuous hK, ‖f - g‖ < ε := by
  haveI : CompactSpace ↥K := hK.compactSpace
  have hdense := universal_approximation σ hσ hK
  -- membership in topological closure ⊤ gives approximants within ε
  sorry  -- PROVE: unfold dense (mem_closure_iff_seq / Metric.mem_closure_iff); see Step 2.

end UniversalApproximation
```

- [ ] **Step 2: Verify + iterate (prove the two non-admit `sorry`s here)**

Run `lean_diagnostic_messages`. The only acceptable remaining `sorry` warnings in the *whole project* are `riesz_repr` and `sigmoidal_discriminatory` (and possibly the logistic sanity lemma). Therefore **`dense_iff_forall_functional_eq_zero` and `universal_approximation_eps` must be proved here**, not admitted.

For `dense_iff_forall_functional_eq_zero`: search `lean_leansearch "submodule dense iff every continuous linear functional vanishing is zero"` and `lean_loogle "Submodule.topologicalClosure"`. Likely route: `(⊤ : Submodule).topologicalClosure` characterization + `Submodule.eq_top_iff'`; for the hard direction, contrapose and apply `geometric_hahn_banach_point_closed` to `x ∉ V.topologicalClosure` (a closed convex set) to get a separating functional, then show it annihilates `V`. If a direct Mathlib lemma exists (e.g. about `Submodule.dense` and the annihilator/`NormedSpace.Dual`), prefer it.

For `universal_approximation_eps`: from `topologicalClosure = ⊤`, every `f` is in the closure of `V`; use `Metric.mem_closure_iff` (or `SeminormedAddGroup`/`mem_closure_iff_nhds`) to extract `g ∈ V` with `dist f g < ε`, and rewrite `dist` as `‖f - g‖`.

Iterate until `lean_diagnostic_messages` shows no errors and no `sorry` beyond the admitted lemmas.

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation/Theorem.lean
git commit -m "feat(uat): Hahn–Banach reduction (proved) + universal_approximation theorem + ε-corollary"
```

---

### Task 6: Root module, admit inventory, sanity instantiation, full build

**Files:**
- Create: `LeanPlayground/UniversalApproximation.lean`

**Interfaces:**
- Consumes: all five files. Produces: single import entry point + `logistic_sigmoidal` sanity lemma.

- [ ] **Step 1: Write the root file**

```lean
import LeanPlayground.UniversalApproximation.Activation
import LeanPlayground.UniversalApproximation.Network
import LeanPlayground.UniversalApproximation.Family
import LeanPlayground.UniversalApproximation.Riesz
import LeanPlayground.UniversalApproximation.Theorem

/-!
# Universal Approximation Theorem — scaffold

Cybenko (1989) UAT, general n-D, as a compiling Mathlib scaffold.

## Admit inventory (roadmap)
1. `UniversalApproximation.riesz_repr` — signed/dual Riesz representation of `(C(K,ℝ))*`.
2. `UniversalApproximation.sigmoidal_discriminatory` — continuous sigmoidal ⇒ discriminatory.
(3. `UniversalApproximation.logistic_sigmoidal` — only if not proved below.)

Everything else (subspace/continuity structure, Hahn–Banach reduction,
`universal_approximation`, ε-corollary) is proved.
-/

namespace UniversalApproximation

open Real

/-- Sanity check: the logistic function is sigmoidal (definitions are non-vacuous). -/
theorem logistic_sigmoidal : Sigmoidal (fun t => 1 / (1 + Real.exp (-t))) := by
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · -- exp(-t) → +∞ as t→-∞, so 1/(1+exp(-t)) → 0
    sorry  -- prove if quick (Real.tendsto_exp_atBot/atTop + Tendsto.comp); else this is allowed admit #3
  · sorry  -- prove if quick; else allowed admit #3

end UniversalApproximation
```

- [ ] **Step 2: Full build verification**

Run `lake build` (or `mcp__lean-lsp__lean_build`). Then `lean_diagnostic_messages` on each of the six files. Done when: build succeeds; the ONLY `sorry` warnings across the project are `riesz_repr`, `sigmoidal_discriminatory`, and at most the two `logistic_sigmoidal` limits. Run `#check @UniversalApproximation.universal_approximation` via `lean_run_code`-style check to confirm the statement type. Attempt the two logistic limits with `lean_leansearch "tendsto one over one plus exp"` / `Real.tendsto_exp_atBot`; if not quick, leave as clearly-marked admit #3.

- [ ] **Step 3: Commit**

```bash
git add LeanPlayground/UniversalApproximation.lean
git commit -m "feat(uat): root module, admit inventory, logistic sanity check; full build green"
```

---

## Self-Review (completed by plan author)

- **Spec coverage:** definitions (Task 1,2,3) ✓; main statement + ε-form (Task 5) ✓; prove/admit split — riesz_repr (Task 4), sigmoidal_discriminatory (Task 1), Hahn–Banach reduction proved (Task 5) ✓; file layout (all tasks) ✓; verification + admit inventory (Task 6) ✓; sanity instantiation (Task 6) ✓.
- **Placeholder scan:** No "TBD"/"implement later". The in-code `sorry`s are intentional: 2 admitted lemmas + 2 proof obligations explicitly flagged "PROVE THIS" with concrete tactics in their Step 2.
- **Type consistency:** `signedIntegral`'s posPart/negPart difference (Task 4) matches the `Discriminatory` definition (Task 1) — Steps explicitly require aligning them. `S σ hσ.continuous hK` arg order consistent across Tasks 3 and 5. `generator σ hσ.continuous hK w b` consistent.
- **Known risk:** Mathlib signed-measure integral API and the dense↔functional lemma are the friction points; each has a search-and-iterate step. If `dense_iff_forall_functional_eq_zero` proves intractable within effort, it is the sole sanctioned fallback admit (flagged in spec), to be reported explicitly.
