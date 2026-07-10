# Leshno leaves D and A — Implementation Plan

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Discharge the two remaining `sorry` leaves of the Leshno M-class UAT — `exists_nonpoly_mollify` (D) and `mollify_ridge_mem_T` (A) — making `leshno_dense_iff` fully `sorry`-free.

**Architecture:** Factor the hard analytic content into reusable, Mathlib-upstream-ready `Contrib` lemmas (each its own namespace + inline `Intended Mathlib home:` header), then assemble in `Mollify.lean`. D follows the Pinkus distributional argument (iterated convolution derivative → uniform degree bound via Baire → moment-vanishing antiderivative → distributional polynomial recovery). A follows uniform point-sampling Riemann-sum approximation of the convolution, staged continuous-σ first then generalized to the M-class.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.32.0-rc1`), Mathlib (pinned), `lake`, lean-lsp MCP tools.

## Global Constraints

- Spec: `docs/superpowers/specs/2026-06-27-leshno-leaves-D-and-A-design.md`. Work branch: `feat/leshno-leaves-DA` (off merged `main`; already created, spec committed).
- **Do NOT change** the headline `leshno_dense_iff`, `mollify`, `ClassM`, `T`, or any already-proved lemma. The two leaf statements (`exists_nonpoly_mollify`, `mollify_ridge_mem_T`) keep their exact current signatures — only their proofs are filled.
- New general lemmas go under `LeanPlayground/Contrib/`, each: `import Mathlib`, a per-contribution `namespace`, a file docstring with an inline `Intended Mathlib home: …` line, per-declaration docstrings, ≤100-char lines, general typeclasses where natural. Project-specific assembly stays in `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean`.
- Smoothness is `ContDiff ℝ ∞` (C^∞), never `⊤` (= ω, analytic). Files using `∞` need `open scoped ContDiff`.
- Inner product `⟪w, x⟫` with `open scoped RealInnerProductSpace`; on `E = ℝ`, `⟪(1:ℝ), t⟫ = t`.
- **Per-lemma discipline (TDD analogue):** (a) write the declaration `:= by sorry`, confirm the *statement* elaborates (only a `sorry` warning, no error) via `mcp__lean-lsp__lean_diagnostic_messages`; (b) replace `sorry` with the real proof, confirm no `sorry` and run `mcp__lean-lsp__lean_verify <fully.qualified.name>` → axioms must be `[propext, Classical.choice, Quot.sound]` (plus `sorryAx` ONLY where a proof legitimately, transitively uses one of the still-open leaves); (c) `mcp__lean-lsp__lean_build` stays green; (d) commit. Never accumulate stray `sorry`s beyond the leaf currently being filled.
- **Definition of done per file:** `lean_diagnostic_messages` reports no `error`-severity items; no `sorry` beyond what the sequencing explicitly still allows.
- Verification = lean-lsp MCP tools (NOT pytest). After writing: `lean_diagnostic_messages`; at a tactic position `lean_goal`; for names `lean_local_search` FIRST (others — `lean_leansearch`/`lean_loogle`/`lean_state_search` — are rate-limited ~3/30s); `lean_multi_attempt` to test tactics without editing. If a diagnostic returns "Too many open files", call `mcp__lean-lsp__lean_build` once to restart the LSP, then retry.
- Commits are signed (SSH signing now works). Each commit message ends with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
  If a commit ever fails/hangs on signing, retry once with `git -c commit.gpgsign=false commit …` and report it.
- **Research-grade tasks (D-B2, D-B5, A-core-Mclass):** if a specific sub-goal is genuinely intractable after serious effort, STOP and report NEEDS_CONTEXT with the exact stuck goal and the missing Mathlib lemma — do NOT leave a hidden `sorry`, do NOT weaken a statement. A documented, reported blocker is an acceptable task outcome; a silent regression is not.

## File structure

New under `LeanPlayground/Contrib/` (each a focused, independently-verifiable contribution):
- `ConvolutionIteratedDeriv.lean` — D-B1: iterated derivative of a convolution.
- `SmoothCompactAntideriv.lean` — D-B4: moment-vanishing ⇒ iterated antiderivative is compactly supported.
- `PolynomialDistribution.lean` — D-B5: annihilating moment-vanishing test functions ⇒ a.e. polynomial.
- `TestFunctionDegreeBound.lean` — D-B2: uniform degree bound (Baire).
- `UniformRiemannConvolution.lean` — A-core: uniform Riemann-sum convergence (continuous, then a.e.-continuous bounded).

Modified:
- `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean` — the A and D assemblies; remove the two `sorry`s. Add `import`s of the new Contrib files.
- `LeanPlayground/UniversalApproximation/Leshno.lean` — update the admit inventory to "0 leaves".

Reuse (already proved): `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly`, `IteratedDerivPolynomial.exists_antideriv`, `RidgePowersSpan.ridgePow_span`, `contDiff_mollify` (and its `mollify = convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume` identity), `deriv_pow_mem`, `ClassM.aestronglyMeasurable`, `ClassM.locallyIntegrable`, `genFun_reparam_mem`, `T_isClosed`.

---

### Task 1: D-B1 — iterated convolution derivative

**Files:**
- Create: `LeanPlayground/Contrib/ConvolutionIteratedDeriv.lean`

**Interfaces:**
- Consumes: Mathlib `HasCompactSupport.hasDerivAt_convolution_left`, `MeasureTheory.convolution`.
- Produces: `ConvolutionIteratedDeriv.iteratedDeriv_convolution_left` (signature below), consumed by Task 7 (D-assembly).

- [ ] **Step 1: Write the statement + `sorry`; confirm it elaborates.**

```lean
import Mathlib

/-! # Iterated derivative of a convolution (smooth, compactly-supported left factor).
Intended Mathlib home: `Mathlib/Analysis/Calculus/ContDiff/Convolution` (confirm with maintainers). -/

namespace ConvolutionIteratedDeriv

open MeasureTheory

open scoped ContDiff

/-- For a `C^∞` compactly-supported `f` and a locally integrable `g`, the `n`-th derivative of the
real convolution `f ⋆ g` (with scalar multiplication) is the convolution of `f`'s `n`-th derivative
with `g`. (Differentiation falls on the smooth factor.) -/
theorem iteratedDeriv_convolution_left {f g : ℝ → ℝ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : LocallyIntegrable g volume) :
    iteratedDeriv n (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      = convolution (iteratedDeriv n f) g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  sorry

end ConvolutionIteratedDeriv
```
Run `mcp__lean-lsp__lean_diagnostic_messages` on the file → expect only `declaration uses 'sorry'`, no error. (If `convolution`/`ContinuousLinearMap.mul ℝ ℝ` need argument tweaks to elaborate, fix the statement minimally so the types check; keep the mathematical content.)

- [ ] **Step 2: Prove by induction on `n`.**
  - `n = 0`: `iteratedDeriv_zero`, both sides are `convolution f g …`.
  - `n+1`: `iteratedDeriv_succ` (`iteratedDeriv (n+1) h = deriv (iteratedDeriv n h)`); rewrite with the IH to `deriv (convolution (iteratedDeriv n f) g …)`. Each `iteratedDeriv n f` is still `C^∞` with compact support (`HasCompactSupport.iteratedDeriv` / `ContDiff.iterate_deriv`; `hfc.iteratedDeriv`), so `HasCompactSupport.hasDerivAt_convolution_left` gives `HasDerivAt (convolution (iteratedDeriv n f) g …) (convolution (deriv (iteratedDeriv n f)) g …) x` pointwise; conclude `deriv (…) = convolution (deriv (iteratedDeriv n f)) g …` via `HasDerivAt.deriv` + `funext`, and `deriv (iteratedDeriv n f) = iteratedDeriv (n+1) f` (`iteratedDeriv_succ`). Verify names with `lean_local_search`.

- [ ] **Step 3: Verify.** `lean_diagnostic_messages` → no error, no `sorry`. `lean_verify ConvolutionIteratedDeriv.iteratedDeriv_convolution_left` → axioms `[propext, Classical.choice, Quot.sound]`. `mcp__lean-lsp__lean_build` green.

- [ ] **Step 4: Commit.**
```bash
git add LeanPlayground/Contrib/ConvolutionIteratedDeriv.lean
git commit -m "feat(contrib): iterated derivative of a convolution (smooth compact left factor)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: A-core (continuous) — uniform Riemann-sum convergence of a convolution

**Files:**
- Create: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`

**Interfaces:**
- Consumes: Mathlib uniform-continuity-on-compact (`IsCompact.uniformContinuousOn_of_continuous` / `Continuous.uniformContinuous_of_…`), `intervalIntegral`/`MeasureTheory.integral`, `tsupport`.
- Produces: `UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous` (signature below), consumed by Task 3.

- [ ] **Step 1: Fix the Riemann-sum encoding + statement; confirm it elaborates.**

The convolution value at `s` is `∫ y, f (s - y) * φ y`. Discretize the compact `tsupport φ` (contained in some `Icc (-M) M`) into `m` equal cells with left nodes `yᵢ = -M + i·(2M/m)`, width `Δ = 2M/m`. Define
```lean
import Mathlib

/-! # Uniform Riemann-sum approximation of a convolution against a continuous kernel.
Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/

namespace UniformRiemannConvolution

open MeasureTheory Topology

/-- Point-sampling Riemann sum of `y ↦ f (s - y) * φ y` over `m` equal cells of `Icc (-M) M`. -/
noncomputable def riemannSum (f φ : ℝ → ℝ) (M : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    f (s - (-M + (i : ℝ) * (2 * M / m))) * φ (-M + (i : ℝ) * (2 * M / m)) * (2 * M / m)

/-- For continuous `f`, continuous `φ` supported in `Icc (-M) M`, and a compact `S`, the
point-sampling Riemann sums converge to the convolution integral uniformly for `s ∈ S`. -/
theorem tendstoUniformly_riemannSum_continuous
    {f φ : ℝ → ℝ} (hf : Continuous f) (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) S Filter.atTop := by
  sorry

end UniformRiemannConvolution
```
`lean_diagnostic_messages` → only `sorry` warning. (Adjust the `TendstoUniformlyOn`/`Filter.atTop` phrasing or restrict the integral to `Icc (-M) M` via `hsupp` if needed so it elaborates; the deliverable is "Riemann sums → convolution, uniform in `s ∈ S`".)

- [ ] **Step 2: Prove (continuous case).** On the compact `S - Icc (-M) M` (a compact superset of all relevant arguments `s - y`), `f` is uniformly continuous (`IsCompact.uniformContinuousOn`); `φ` is uniformly continuous on `Icc (-M) M`. Standard Riemann-sum error bound: the integrand `(s,y) ↦ f(s-y)φ(y)` is uniformly continuous in `y` uniformly over `s ∈ S`, so `|∫ - riemannSum| ≤ 2M · ω(Δ)` where `ω` is a joint modulus of continuity → 0 as `m → ∞`, uniformly in `s`. Reduce the integral to `Icc (-M) M` using `hsupp` (`MeasureTheory.setIntegral`/`integral_eq_setIntegral_of_support_subset`). Express the error as `∑ᵢ ∫_{cell i} (f(s-yᵢ)φ(yᵢ) - f(s-y)φ(y)) dy` and bound each cell. Candidate lemmas: `IsCompact.uniformContinuousOn`, `Metric.uniformContinuousOn_iff`, `MeasureTheory.norm_integral_le_of_norm_le`, `intervalIntegral` Riemann-sum lemmas if any. Use `lean_goal`/`lean_local_search` heavily.

- [ ] **Step 3: Verify.** `lean_diagnostic_messages` no error/`sorry`; `lean_verify UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous` axioms clean; `lean_build` green.

- [ ] **Step 4: Commit.**
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit -m "feat(contrib): uniform Riemann-sum approximation of a convolution (continuous kernel)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: A-assembly (continuous-σ instance) — validate the genFun assembly

**Files:**
- Modify: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean`

**Interfaces:**
- Consumes: `UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous` (Task 2), `genFun_reparam_mem`, `T_isClosed`, `ApproxByGen`/`T` (Family), `genFun`.
- Produces: `UniversalApproximation.Leshno.mollify_ridge_mem_T_of_continuous` — the same conclusion as `mollify_ridge_mem_T` but with `(hσc : Continuous σ)` replacing `hσ : ClassM σ`. Used only to validate the assembly; the final leaf (Task 6) reuses the shared assembly lemma below.

- [ ] **Step 1: Factor the σ-independent assembly into a private lemma; write statements + `sorry`.** In `Mollify.lean` add a private assembly lemma that turns "uniform Riemann-sum convergence of the convolution ridge" into `T`-membership, isolating the parts that do NOT depend on σ's regularity:

```lean
/-- Assembly core (σ-regularity-independent): if the ridge `x ↦ (σ⋆φ)(lam*(⟪w,x⟫+b)+c)` is a
uniform-on-`K` limit of the point-sampling Riemann sums (each of which is a `genSpan` element via
`genFun_reparam_mem`), it lies in `T σ K`. -/
private theorem mollify_ridge_mem_T_of_uniformRiemann {σ φ : ℝ → ℝ} (M : ℝ)
    (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c))
    (hunif : TendstoUniformlyOn
      (fun m (x : ↥K) => UniformRiemannConvolution.riemannSum σ φ M m (lam * (⟪w, (x:E)⟫ + b) + c))
      (fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) Set.univ Filter.atTop) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩ : C(↥K, ℝ)) ∈ T σ K := by
  sorry
```
Confirm it elaborates (`lean_diagnostic_messages`). (`mollify σ φ s = ∫ y, σ (s-y) * φ y` by definition, matching the Riemann-sum target.)

- [ ] **Step 2: Prove `mollify_ridge_mem_T_of_uniformRiemann`.** Membership in `T σ K` unfolds to `ApproxByGen σ K`: `∀ ε>0, ∃ g ∈ genSpan σ K, ∀ x, |target x - g x| < ε`. From `hunif`, pick `m` with `∀ x, |target x - riemannSum … x| < ε`. The Riemann sum, as a function of `x`, is `∑ᵢ (φ yᵢ · Δ) · (fun x => σ (lam*(⟪w,x⟫+b)+c - yᵢ))` where `σ(s - yᵢ) = σ(lam*(⟪w,x⟫+b) + (c - yᵢ))` — i.e. `(φ yᵢ Δ) • genFun σ (lam•w) (lam*b + c - yᵢ)` evaluated at `x` (use `genFun_reparam_mem σ K lam w b (c - yᵢ)`, noting `lam*(⟪w,x⟫+b)+(c-yᵢ) = lam*(⟪w,x⟫+b)+c - yᵢ`). A finite `ℝ`-combination of `genSpan` members is in `genSpan` (`Submodule.sum_mem`, `Submodule.smul_mem`). Take `g := that sum`. Done.

- [ ] **Step 3: Prove `mollify_ridge_mem_T_of_continuous` from Task 2 + the assembly.** State:
```lean
theorem mollify_ridge_mem_T_of_continuous {σ φ : ℝ → ℝ} (hσc : Continuous σ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩ : C(↥K, ℝ)) ∈ T σ K := by
  sorry
```
Proof: choose `M` with `tsupport φ ⊆ Icc (-M) M` (`HasCompactSupport` ⇒ bounded support; `hφc`). The image set `S := (fun x => lam*(⟪w,x⟫+b)+c) '' (univ : Set ↥K)` — actually apply `tendstoUniformly_riemannSum_continuous hσc hφ.continuous hM hsupp` with `S = Set.range (fun x:↥K => lam*(⟪w,x⟫+b)+c)`'s closure or just compose: since we feed the result through `mollify_ridge_mem_T_of_uniformRiemann` over `Set.univ` of `↥K`, transport the uniform-on-`S` convergence to uniform-on-`↥K` via the (continuous) parametrization `x ↦ lam*(⟪w,x⟫+b)+c` (`TendstoUniformlyOn.comp`). Conclude via `mollify_ridge_mem_T_of_uniformRiemann`.

- [ ] **Step 4: Verify.** `lean_diagnostic_messages` on `Mollify.lean` → no error; the only `sorry`s remaining are the two leaves `exists_nonpoly_mollify` and `mollify_ridge_mem_T` (the new lemmas are proved). `lean_verify` on `mollify_ridge_mem_T_of_continuous` and `mollify_ridge_mem_T_of_uniformRiemann` → clean axioms. `lean_build` green.

- [ ] **Step 5: Commit.**
```bash
git add LeanPlayground/UniversalApproximation/Leshno/Mollify.lean
git commit -m "feat(leshno): A assembly (σ-regularity-independent) + continuous-σ ridge∈T instance

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: D-B4 — moment-vanishing ⇒ compactly-supported iterated antiderivative

**Files:**
- Create: `LeanPlayground/Contrib/SmoothCompactAntideriv.lean`

**Interfaces:**
- Consumes: Mathlib `MeasureTheory.integral`, FTC (`intervalIntegral.integral_hasDerivAt`/`HasDerivAt` of `∫_a^x`), `HasCompactSupport`, `ContDiff`.
- Produces: `SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero` (signature below), consumed by Task 7.

- [ ] **Step 1: Statement + `sorry`; confirm elaborates.**

```lean
import Mathlib

/-! # A smooth compactly-supported function with vanishing moments is an iterated derivative
of a smooth compactly-supported function.
Intended Mathlib home: `Mathlib/Analysis/Calculus/BumpFunction/…` (confirm with maintainers). -/

namespace SmoothCompactAntideriv

open MeasureTheory

open scoped ContDiff

/-- If `g : ℝ → ℝ` is `C^∞`, compactly supported, and has vanishing moments
`∫ y, (y ^ j) * g y = 0` for all `j ≤ d`, then `g = iteratedDeriv (d+1) φ` for some `C^∞`
compactly-supported `φ`. (The `(d+1)`-fold indefinite integral `∫_{-∞}^x` stays compactly supported
exactly because the moments up to order `d` vanish.) -/
theorem exists_iteratedDeriv_eq_of_moments_zero {g : ℝ → ℝ} (d : ℕ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hmom : ∀ j ≤ d, ∫ y, (y ^ j) * g y = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ iteratedDeriv (d + 1) φ = g := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`.

- [ ] **Step 2: Prove by induction on `d+1` antiderivatives.** Define the single indefinite integral `I h x := ∫ y in Set.Iic x, h y` (or `∫ y in (-∞)..x`). For `h` smooth compactly supported with `∫ h = 0`, `I h` is smooth (FTC: `HasDerivAt (I h) (h x) x`, `deriv (I h) = h`) and **compactly supported** (constant `= 0` left of the support by emptiness, and `= ∫ h = 0` right of the support by the zero-integral condition). Iterate `d+1` times: the `k`-th antiderivative is compactly supported iff the `(k-1)`-moment vanishes; the moment conditions `∫ yʲ g = 0` (j ≤ d) are exactly what keep all `d+1` antiderivatives compactly supported (integration by parts relates the moment of `g` to the integral of the iterated antiderivative). Build `φ` as the `(d+1)`-fold antiderivative; `iteratedDeriv (d+1) φ = g` by `d+1` applications of `deriv (I h) = h`. Candidate lemmas: `intervalIntegral.integral_hasDerivAt_right`, `MeasureTheory.integral_Iic_…`, `HasCompactSupport`, integration-by-parts `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. This is delicate (the moment ↔ compact-support bookkeeping); budget effort.

- [ ] **Step 3: Verify.** diagnostics no error/`sorry`; `lean_verify SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero` clean; `lean_build` green.

- [ ] **Step 4: Commit.**
```bash
git add LeanPlayground/Contrib/SmoothCompactAntideriv.lean
git commit -m "feat(contrib): vanishing-moment smooth bump is an iterated derivative of a bump

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: D-B5 — distributional polynomial recovery (degree d)

**Files:**
- Create: `LeanPlayground/Contrib/PolynomialDistribution.lean`

**Interfaces:**
- Consumes: Mathlib `ae_eq_of_integral_contDiff_smul_eq` / `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (degree-0), `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly`, `SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero` (Task 4).
- Produces: `PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing` (signature below), consumed by Task 7.

- [ ] **Step 1: Statement + `sorry`; confirm elaborates.**

```lean
import Mathlib
import LeanPlayground.Contrib.IteratedDerivPolynomial
import LeanPlayground.Contrib.SmoothCompactAntideriv

/-! # Distributional characterization of polynomials (degree ≤ d).
Intended Mathlib home: `Mathlib/Analysis/Distribution/…` (confirm with maintainers). -/

namespace PolynomialDistribution

open MeasureTheory

open scoped ContDiff

/-- A locally integrable `f : ℝ → ℝ` that annihilates every `C^∞` compactly-supported test function
with vanishing moments up to order `d` (`∫ y, (y^j) * g y = 0` for `j ≤ d`) is a.e. equal to a
polynomial of degree `≤ d`. -/
theorem aePolynomial_of_annihilates_moment_vanishing {f : ℝ → ℝ} (d : ℕ)
    (hf : LocallyIntegrable f volume)
    (hann : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∀ j ≤ d, ∫ y, (y ^ j) * g y = 0) → ∫ y, g y * f y = 0) :
    ∃ p : Polynomial ℝ, f =ᵐ[volume] fun t => p.eval t := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`.

- [ ] **Step 2: Prove.** For any test `h`, `iteratedDeriv (d+1) h` has vanishing moments up to `d` (integration by parts: `∫ yʲ · h^(d+1) = 0` for `j ≤ d` since `h` is compactly supported and `j < d+1`). So by `hann`, `∫ (iteratedDeriv (d+1) h) · f = 0` for ALL test `h`. This says the distributional `(d+1)`-th derivative of `f` is `0`. Bootstrapping: by Mathlib's degree-0 `ae_eq_zero_of_integral_contDiff_smul_eq_zero` applied appropriately (and `exists_iteratedDeriv_eq_of_moments_zero` from Task 4 to realize moment-vanishing `g` as `h^(d+1)`), show `f` agrees a.e. with a `C^∞` function `F` whose `iteratedDeriv (d+1)` is `0`; then `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly` gives `F = p.eval` with `p.degree < d+1`, so `f =ᵐ p.eval`. (The realization of `f` by a smooth representative with vanishing `(d+1)`-th derivative is the crux assembly; use Task 4 to translate "annihilates moment-vanishing" into "distributional `(d+1)`-derivative is 0", then mollify-and-pass-to-limit or directly apply the degree-0 recovery to the `d`-th distributional derivative.) Budget serious effort; report NEEDS_CONTEXT with the exact stuck goal if the smoothing step resists.

- [ ] **Step 3: Verify.** diagnostics no error/`sorry`; `lean_verify PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing` → axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx` — Task 4 and `iteratedDeriv_eq_zero_imp_poly` are both proved). `lean_build` green.

- [ ] **Step 4: Commit.**
```bash
git add LeanPlayground/Contrib/PolynomialDistribution.lean
git commit -m "feat(contrib): distributional characterization of degree-≤d polynomials

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: A-core (M-class) + close `mollify_ridge_mem_T`

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`
- Modify: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean`

**Interfaces:**
- Consumes: `mollify_ridge_mem_T_of_uniformRiemann` (Task 3), `ClassM.locBdd`, `ClassM.discNull`.
- Produces: `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` and the fully-proved leaf `UniversalApproximation.Leshno.mollify_ridge_mem_T`.

- [ ] **Step 1: Add the M-class core statement + `sorry` to `UniformRiemannConvolution.lean`.**

```lean
/-- Same uniform Riemann-sum convergence as `tendstoUniformly_riemannSum_continuous`, but for `f`
only **locally bounded and a.e. continuous** (`volume (closure {t | ¬ ContinuousAt f t}) = 0`).
The null discontinuity set controls the cells straddling discontinuities (Lebesgue's criterion). -/
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) S Filter.atTop := by
  sorry
```
`lean_diagnostic_messages` → only `sorry` here (Task 2's lemma still proved).

- [ ] **Step 2: Prove the M-class core.** Split the per-cell error `∑ᵢ ∫_{cell} (f(s-yᵢ)φ(yᵢ) - f(s-y)φ(y)) dy` into the `φ`-variation term (handled exactly as the continuous case via uniform continuity of `φ` and the uniform bound on `f`) plus the `f`-variation term `∑ᵢ ∫_{cell} (f(s-yᵢ) - f(s-y)) φ(y) dy`. Bound the `f`-term using: `f` is bounded (`hbdd` on the compact `S - Icc (-M) M`) and a.e. continuous, so by Lebesgue's criterion `y ↦ f(s-y)` is Riemann integrable with oscillation summing to `0`; the cells straddling the (null-closure) discontinuity set contribute `≤ 2C · volume(neighborhood of discontinuities) → 0`, uniformly in `s` because translating the null closed set by `s` keeps measure `0` and the bound is `s`-uniform. Candidate tooling: `MeasureTheory.volume` of the discontinuity set, `IsCompact.exists_bound_of_continuousOn` for the bound, oscillation/`MeasureTheory` a.e.-continuity ⇒ Riemann-integrable results. This is the hardest analytic step; report NEEDS_CONTEXT with the precise stuck goal if it resists after serious effort. Verify `tendstoUniformly_riemannSum_aeContinuous` (axioms clean), commit this file.
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit -m "feat(contrib): uniform Riemann-sum convolution for bounded a.e.-continuous kernels

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

- [ ] **Step 3: Close the leaf `mollify_ridge_mem_T` in `Mollify.lean`.** Replace its `sorry`: choose `M` with `tsupport φ ⊆ Icc (-M) M`; apply `tendstoUniformly_riemannSum_aeContinuous` with `hbdd := hσ.locBdd`, `hdisc := hσ.discNull`, `hφ := hφ.continuous`, and `S := closure (Set.range (fun x:↥K => lam*(⟪w,x⟫+b)+c))` (compact: continuous image of compact `↥K`); transport to uniform-on-`↥K` and feed `mollify_ridge_mem_T_of_uniformRiemann` (exactly as Task 3 Step 3 did for the continuous case — reuse that wiring). No `sorry` remains in `mollify_ridge_mem_T`.

- [ ] **Step 4: Verify.** `lean_diagnostic_messages` on `Mollify.lean` → no error; the ONLY remaining `sorry` is `exists_nonpoly_mollify`. `lean_verify UniversalApproximation.Leshno.mollify_ridge_mem_T` → axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). `lean_build` green.

- [ ] **Step 5: Commit.**
```bash
git add LeanPlayground/UniversalApproximation/Leshno/Mollify.lean
git commit -m "feat(leshno): close mollify_ridge_mem_T (A) via uniform Riemann-sum convolution

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 7: D-B2 (Baire uniform degree bound) + close `exists_nonpoly_mollify`

**Files:**
- Create: `LeanPlayground/Contrib/TestFunctionDegreeBound.lean`
- Modify: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean`
- Modify: `LeanPlayground/UniversalApproximation/Leshno.lean`

**Interfaces:**
- Consumes: Mathlib `BaireSpace`/`nonempty_interior_of_iUnion_of_closed` (Baire category), `ConvolutionIteratedDeriv.iteratedDeriv_convolution_left` (Task 1), `SmoothCompactAntideriv.exists_iteratedDeriv_eq_of_moments_zero` (Task 4), `PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing` (Task 5), `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly`, `contDiff_mollify`, `mollify`.
- Produces: `TestFunctionDegreeBound.exists_uniform_degree_bound` (signature below) and the fully-proved leaf `UniversalApproximation.Leshno.exists_nonpoly_mollify`.

- [ ] **Step 1: Statement + `sorry` for the Baire degree bound; confirm elaborates.** Phrase the test-function space and the closed cover concretely enough to apply Baire. A workable encoding: parametrize test functions by a complete metric space (e.g. fix the support in `Icc (-R) R` and use the `C^∞`-norm, or restrict to a fixed `ContDiffBump`-scaled family) so the sets `Fd := {φ in the space | the polynomial `mollify σ φ` has degree ≤ d}` are closed and cover. Produce:

```lean
import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.Mollify

/-! # Uniform polynomial-degree bound for mollifications (Baire category).
Intended Mathlib home: distribution theory (new area; confirm with maintainers). -/

namespace TestFunctionDegreeBound

open MeasureTheory UniversalApproximation.Leshno

open scoped ContDiff

/-- If every `C^∞` compactly-supported mollification `σ⋆φ` is a polynomial, there is a single `d`
bounding all their degrees. -/
theorem exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : ClassM σ)
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ p : Polynomial ℝ, mollify σ φ = fun t => p.eval t) :
    ∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ p : Polynomial ℝ, mollify σ φ = (fun t => p.eval t) ∧ p.degree ≤ (d : ℕ) := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`. (If a usable complete-metric test-function space is hard to set up, an acceptable alternative encoding: bound the degree on each fixed-support slice `{φ : tsupport φ ⊆ Icc (-R) R}` with the Fréchet metric, then note the assembly only needs the bound on supports that arise — coordinate the exact encoding here so the statement is both true and elaborable.)

- [ ] **Step 2: Prove via Baire.** `Fd := {φ | deg ≤ d}` is closed (degree-`≤ d` is a closed condition: it is the vanishing of the `(d+1)`-th derivative, and `φ ↦ iteratedDeriv (d+1) (mollify σ φ)` is continuous in the test-function topology via `iteratedDeriv_convolution_left` (Task 1) + continuity of convolution); the `Fd` cover the (complete metric) space by `H`. `nonempty_interior_of_iUnion_of_closed` (Baire) ⇒ some `Fd` has interior ⇒ contains a ball ⇒ by the vector-space/scaling structure the degree bound `d` is global. (The "interior ⇒ global via scaling/translation-density" step is the delicate part.) Report NEEDS_CONTEXT with the exact stuck goal if the test-function-space topology setup resists. Verify (`lean_verify exists_uniform_degree_bound`), commit this file:
```bash
git add LeanPlayground/Contrib/TestFunctionDegreeBound.lean
git commit -m "feat(contrib): uniform degree bound for polynomial mollifications (Baire)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

- [ ] **Step 3: Close the leaf `exists_nonpoly_mollify` in `Mollify.lean`.** Contrapositive: assume `H : ∀ φ …, IsPolynomialFun (mollify σ φ)` (i.e. `¬∃φ …`), derive `IsAEPolynomial σ` to contradict `hnp`. Get the uniform degree `d` (`exists_uniform_degree_bound hσ H'`). For any test `g` with vanishing moments up to `d`: by `exists_iteratedDeriv_eq_of_moments_zero` (Task 4) write `g = iteratedDeriv (d+1) φ`; then
  `mollify σ g = mollify σ (iteratedDeriv (d+1) φ) = iteratedDeriv (d+1) (mollify σ φ)` (Task 1 via the `mollify = convolution …` identity from `contDiff_mollify`) `= 0` because `mollify σ φ` is a polynomial of degree `≤ d`. Hence `∫ g · σ = (mollify-style annihilation) = 0` for all moment-vanishing `g`; apply `aePolynomial_of_annihilates_moment_vanishing hσ.locallyIntegrable d` (Task 5) ⇒ `IsAEPolynomial σ`. Contradiction. (Mind the `∫ σ(0-y) g y` vs `∫ g · σ` orientation; `mollify σ g 0 = ∫ σ(-y) g y` — align the annihilation integral used in Task 5 with the value of `mollify σ g` at a point, or integrate against translates.) No `sorry` remains.

- [ ] **Step 4: Update the admit inventory.** In `LeanPlayground/UniversalApproximation/Leshno.lean`, rewrite the "Admit inventory" docstring section to state that **all six leaves are now proved** and the development is `sorry`-free (list the now-proved D and A and their new Contrib supports).

- [ ] **Step 5: Verify the whole development.** `lean_diagnostic_messages` on `Mollify.lean`, `Theorem.lean`, `Leshno.lean` → **no error, no `sorry` anywhere**. `git grep -nE "\bsorry\b|\badmit\b" -- 'LeanPlayground/UniversalApproximation/Leshno/*.lean' 'LeanPlayground/Contrib/*.lean'` → only docstring prose, zero proof-body `sorry`. `lean_verify UniversalApproximation.Leshno.leshno_dense_iff` → axioms `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**. `mcp__lean-lsp__lean_build` green.

- [ ] **Step 6: Commit.**
```bash
git add LeanPlayground/UniversalApproximation/Leshno/Mollify.lean LeanPlayground/UniversalApproximation/Leshno.lean
git commit -m "feat(leshno): close exists_nonpoly_mollify (D); leshno_dense_iff now sorry-free

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Final verification (whole branch)

- [ ] `mcp__lean-lsp__lean_build` succeeds (8582+ jobs, no errors).
- [ ] `git grep -nE "\bsorry\b|\badmit\b" -- 'LeanPlayground/UniversalApproximation/Leshno/*.lean' 'LeanPlayground/Contrib/*.lean'` lists **no proof-body `sorry`** (docstring mentions only).
- [ ] `lean_verify UniversalApproximation.Leshno.leshno_dense_iff` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- [ ] Each new `Contrib` file has a per-contribution namespace and an accurate inline `Intended Mathlib home:` header.
- [ ] `Leshno.lean` inventory states the development is `sorry`-free.
- [ ] No existing Cybenko file modified; the two leaf statements and all previously-proved lemmas unchanged.
- [ ] Open a PR to `main` summarizing the now-`sorry`-free Leshno UAT and the new upstreamable `Contrib` lemmas.
