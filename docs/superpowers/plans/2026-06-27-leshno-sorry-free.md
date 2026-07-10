# Leshno UAT — sorry-free finish Implementation Plan

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Discharge the two remaining `sorry` leaves (`TestFunctionDegreeBound.exists_uniform_degree_bound` and `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous`) via elementary in-repo routes, making `leshno_dense_iff` fully `sorry`-free.

**Architecture:** Two independent workstreams. **D** replaces the Baire argument with algebraic degree-invariance: convolution associativity + "polynomial ⋆ test function = polynomial whose top coefficient scales by the kernel's 0th moment". **A** replaces the BoxIntegral criterion with dominated convergence on an oscillation majorant over a fixed (s-independent) compact domain, reusing the already-proved continuous-case cell machinery.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.32.0-rc1`), Mathlib (pinned), `lake`, lean-lsp MCP tools.

## Global Constraints

- Spec: `docs/superpowers/specs/2026-06-27-leshno-sorry-free-design.md`. Work branch: `feat/leshno-sorry-free` (off merged `main`; already created, spec committed `7731ab5`).
- **Do NOT change** `leshno_dense_iff`, `mollify`, `ClassM`, `T`, the two leaf *statements* (`exists_uniform_degree_bound`, `tendstoUniformly_riemannSum_aeContinuous` keep their exact current signatures — only their `sorry` bodies are filled), or any already-proved lemma. No existing Cybenko file is modified.
- **No new Mathlib upstream dependency**; no `BaireSpace`/`CompleteSpace`/`BoxIntegral` development. Every lemma must close against current Mathlib.
- New general lemmas go under `LeanPlayground/Contrib/`, each: `import Mathlib`, per-contribution `namespace`, a file docstring with an inline `Intended Mathlib home: …` line, per-declaration docstrings, lines ≤100 **codepoints** (multi-byte glyphs like `≤ ∞ ⋆` count as one char; a byte-based check over-reports — verify by codepoint).
- Smoothness is `ContDiff ℝ ∞` (C^∞), never `⊤` (= ω/analytic). Files using `∞` need `open scoped ContDiff`. Discharge `↑k ≤ ∞` via `exact_mod_cast le_top` (bare `le_top` fails: `∞ ≠ ⊤`).
- Convolution orientation: `mollify σ φ = convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume` (proved lemma `UniversalApproximation.Leshno.mollify_eq_convolution`). So mathematical "σ⋆φ" is `convolution φ σ (mul ℝ ℝ) volume` — the *smooth* factor `φ` is the LEFT argument.
- **Per-lemma discipline (TDD analogue):** (a) write the declaration `:= by sorry`, confirm the *statement* elaborates (only a `sorry` warning, no error) via `mcp__lean-lsp__lean_diagnostic_messages`; (b) replace `sorry` with the real proof, confirm no `sorry`/error; (c) `mcp__lean-lsp__lean_verify <fully.qualified.name>` → axioms `[propext, Classical.choice, Quot.sound]` (NO `sorryAx` — every dependency is or will be proved); (d) `mcp__lean-lsp__lean_build` stays green; (e) signed commit. Never accumulate stray `sorry`s beyond the leaf currently being filled.
- Verification = lean-lsp MCP tools (NOT pytest). After writing: `lean_diagnostic_messages`; at a tactic position `lean_goal`; for names `lean_local_search` FIRST (others — `lean_leansearch`/`lean_loogle`/`lean_state_search` — rate-limited ~3/30s); `lean_multi_attempt` to test tactics without editing. "Too many open files" → call `mcp__lean-lsp__lean_build` once to restart the LSP, then retry.
- Commits signed; each message ends with: `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. If signing hangs/fails, retry once with `git -c commit.gpgsign=false commit …` and report it.
- **Research-grade steps (Task 2 / D4, Task 6 / A6):** if a sub-goal is genuinely intractable after serious effort, STOP and report NEEDS_CONTEXT with the exact stuck goal and the missing Mathlib lemma — never a hidden `sorry`, never a weakened statement.
- **For Lean proof tasks the "code" is the exact statement + the strategy.** Each task fixes the statement that must elaborate verbatim and a step-by-step proof strategy naming the Mathlib lemmas confirmed to exist. Tactic scripts are the implementer's to write, guided by the strategy; verify each named lemma with `lean_local_search`/`lean_hover_info` before relying on it.

## File structure

- **New** `LeanPlayground/Contrib/ConvolutionPolynomial.lean` (namespace `ConvolutionPolynomial`) — general convolution↔polynomial lemmas: D1 `convolution_comm_mul`, D2 convolution-exists helpers, D4 `monomial_conv_isPoly`, D5 `poly_conv_degree`. (Tasks 1–3.)
- **Modify** `LeanPlayground/Contrib/IteratedDerivPolynomial.lean` (existing namespace `IteratedDerivPolynomial`) — add D6 `iteratedDeriv_succ_eq_zero_of_natDegree_le` (the converse of the existing `iteratedDeriv_eq_zero_imp_poly`; natural home). (Task 1.)
- **Modify** `LeanPlayground/Contrib/TestFunctionDegreeBound.lean` — add D3 `mollify_conv_assoc`, D7 normalized bump, and the D-assembly; remove its `sorry`. Imports `ConvolutionPolynomial`. (Task 4.)
- **Modify** `LeanPlayground/Contrib/UniformRiemannConvolution.lean` — add A1–A7 + A-assembly beside the existing continuous-case lemmas; remove its `sorry`. (Tasks 5–8.)
- **Modify** `LeanPlayground/UniversalApproximation/Leshno.lean` — admit inventory → 0 leaves / fully `sorry`-free. (Task 8.)

Reuse (proved): `UniversalApproximation.Leshno.mollify_eq_convolution`, `ClassM.locallyIntegrable`, `ClassM.aestronglyMeasurable`, `ConvolutionIteratedDeriv.iteratedDeriv_convolution_left`, `IteratedDerivPolynomial.iteratedDeriv_eq_zero_imp_poly`, and (Task 5–8) the proved `UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous` + its `riemannSum` def.

---

## WORKSTREAM D — `exists_uniform_degree_bound` via degree-invariance

### Task 1: D foundational lemmas (commutativity, convolution-existence, poly iterated-deriv)

**Files:**
- Create: `LeanPlayground/Contrib/ConvolutionPolynomial.lean`
- Modify: `LeanPlayground/Contrib/IteratedDerivPolynomial.lean`

**Interfaces:**
- Consumes: Mathlib `convolution_flip`, `ContinuousLinearMap.flip_mul`, `HasCompactSupport.convolutionExists_left`, `HasCompactSupport.convolutionExists_right`, `Polynomial.deriv`, `Polynomial.iterate_derivative_eq_zero`, `iteratedDeriv_eq_iterate`.
- Produces: `ConvolutionPolynomial.convolution_comm_mul`, `ConvolutionPolynomial.convolutionExists_left_mul`, `ConvolutionPolynomial.convolutionExists_right_mul`; `IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le` (consumed by Task 3 and Task 4).

- [ ] **Step 1: Create `ConvolutionPolynomial.lean` with D1 statement + `sorry`; confirm it elaborates.**

```lean
import Mathlib

/-! # Convolution of polynomials with test functions, and commutativity for the `mul` pairing.
Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/

namespace ConvolutionPolynomial

open MeasureTheory

open scoped ContDiff

/-- Commutativity of the real convolution taken against scalar multiplication `mul ℝ ℝ`. -/
theorem convolution_comm_mul (f g : ℝ → ℝ) :
    convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume
      = convolution g f (ContinuousLinearMap.mul ℝ ℝ) volume := by
  sorry

end ConvolutionPolynomial
```
Run `mcp__lean-lsp__lean_diagnostic_messages` → only `declaration uses 'sorry'`, no error.

- [ ] **Step 2: Prove D1.** The spike proved this: `rw [convolution_flip]` reduces to the flipped bilinear map, then `ContinuousLinearMap.flip_mul` identifies `(mul ℝ ℝ).flip` with `mul ℝ ℝ` up to `mul_comm`. Confirm exact names with `lean_local_search "convolution_flip"` and `lean_local_search "flip_mul"`; close with `simp`/`ext`+`mul_comm` as needed. Verify clean axioms.

- [ ] **Step 3: Add D2 convolution-existence helpers + `sorry`; confirm they elaborate.** These package the integrability facts for the compactly-supported-factor cases reused by Task 4/Task 3.

```lean
/-- `φ ⋆ σ` exists pointwise when `φ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_left_mul {φ σ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hσ : LocallyIntegrable σ volume) :
    ConvolutionExists φ σ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  sorry

/-- `σ ⋆ ψ` exists pointwise when `ψ` is continuous with compact support and `σ` is locally
integrable. -/
theorem convolutionExists_right_mul {σ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ConvolutionExists σ ψ (ContinuousLinearMap.mul ℝ ℝ) volume := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`. (If `ConvolutionExists` needs a different exact form — e.g. `ConvolutionExistsAt` pointwise — adjust minimally so it elaborates; the deliverable is "the convolution integral converges everywhere".)

- [ ] **Step 4: Prove D2.** `HasCompactSupport.convolutionExists_left` expects the compactly-supported factor continuous and the other locally integrable; `convolutionExists_right` symmetric. Check exact signatures via `lean_hover_info` on each. Supply `hφ`/`hφc`/`hσ` (and `(mul ℝ ℝ)` continuity is automatic). Verify clean axioms.

- [ ] **Step 5: Add D6 to `IteratedDerivPolynomial.lean` + `sorry`; confirm it elaborates.** Open that file; add (inside `namespace IteratedDerivPolynomial`, after the existing `iteratedDeriv_eq_zero_imp_poly`):

```lean
/-- The converse direction: a polynomial of `natDegree ≤ d` has vanishing `(d+1)`-st iterated
derivative (as a function `ℝ → ℝ`). -/
theorem iteratedDeriv_succ_eq_zero_of_natDegree_le {p : Polynomial ℝ} {d : ℕ}
    (hp : p.natDegree ≤ d) :
    iteratedDeriv (d + 1) (fun x => p.eval x) = 0 := by
  sorry
```
`lean_diagnostic_messages` on the file → only the new `sorry` (the existing lemmas stay proved).

- [ ] **Step 6: Prove D6.** Rewrite `iteratedDeriv (d+1) (fun x => p.eval x)` to `fun x => (Polynomial.derivative^[d+1] p).eval x` via `iteratedDeriv_eq_iterate` + `Polynomial.deriv` (`deriv (fun x => p.eval x) = fun x => p.derivative.eval x`); then `Polynomial.iterate_derivative_eq_zero` gives `derivative^[d+1] p = 0` when `p.natDegree < d+1` (i.e. `≤ d`); conclude `= 0` by `funext` + `Polynomial.eval_zero`. Confirm names with `lean_local_search`. Verify clean axioms.

- [ ] **Step 7: Verify + commit.** `lean_diagnostic_messages` on both files → no error, only-intended state. `lean_verify` on `convolution_comm_mul`, `convolutionExists_left_mul`, `convolutionExists_right_mul`, `iteratedDeriv_succ_eq_zero_of_natDegree_le` → all `[propext, Classical.choice, Quot.sound]`. `lean_build` green.
```bash
git add LeanPlayground/Contrib/ConvolutionPolynomial.lean LeanPlayground/Contrib/IteratedDerivPolynomial.lean
git commit -m "feat(contrib): convolution commutativity/existence + polynomial iterated-deriv vanishing

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: D4 — convolution of a monomial with a test function is a polynomial (the crux)

**Files:**
- Modify: `LeanPlayground/Contrib/ConvolutionPolynomial.lean`

**Interfaces:**
- Consumes: Mathlib `sub_pow`, `MeasureTheory.integral_finset_sum`, `MeasureTheory.integral_const_mul`/`integral_mul_const`, `Polynomial` API (`Polynomial.eval`, `Polynomial.coeff`, `Polynomial.natDegree`).
- Produces: `ConvolutionPolynomial.monomial_conv_isPoly` (consumed by Task 3).

- [ ] **Step 1: Statement + `sorry`; confirm it elaborates.** Express "convolution of the monomial `x ↦ xⁿ` against a test `ψ`" as `fun x => ∫ y, (x - y)^n * ψ y` (this equals `convolution (fun x => x^n) ψ (mul ℝ ℝ) volume` at `x`; you may state it directly as the integral to keep the algebra explicit, or via `convolution` — pick whichever elaborates and prove the identity once).

```lean
/-- Convolving the monomial `x ↦ xⁿ` with a continuous compactly-supported `ψ` gives a polynomial
of degree `≤ n` whose `n`-th coefficient is the `0`-th moment `∫ ψ`. -/
theorem monomial_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (n : ℕ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, (x - y) ^ n * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ n ∧ q.coeff n = ∫ y, ψ y := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`.

- [ ] **Step 2: Prove D4.** Strategy:
  - Expand `(x - y)^n` via `sub_pow`: `(x - y)^n = ∑ m ∈ Finset.range (n+1), x^m * (-y)^(n-m) * (n.choose m)` (confirm the exact form/sign convention of `sub_pow` with `lean_hover_info`; it may be `∑ (x)^m (-y)^(n-m) choose`).
  - Pull the finite sum out of the integral: `∫ y, (∑ m, …) * ψ y = ∑ m, ∫ y, (term m) * ψ y` via `MeasureTheory.integral_finset_sum` (each summand integrable: `ψ` continuous compact support ⟹ `(poly in y)*ψ` integrable — use `Continuous.integrable_of_hasCompactSupport` / `HasCompactSupport.integrable`).
  - Each term `∫ y, x^m * (-y)^(n-m) * (n.choose m) * ψ y = x^m * [ (n.choose m) * ∫ y, (-y)^(n-m) * ψ y ]`, pulling the `x^m` constant-in-`y` factor out (`integral_const_mul`). Define `c m := (n.choose m) * ∫ y, (-y)^(n-m) * ψ y`.
  - So the function is `fun x => ∑ m ∈ range (n+1), c m * x^m`. Take `q := ∑ m ∈ range (n+1), Polynomial.C (c m) * Polynomial.X^m` (or `∑ m, Polynomial.monomial m (c m)`); then `q.eval x = ∑ c m * x^m` (`Polynomial.eval_finset_sum`, `eval_monomial`).
  - `q.natDegree ≤ n`: each `monomial m (c m)` has `natDegree ≤ m ≤ n` (`Polynomial.natDegree_monomial_le`), sum bound via `Polynomial.natDegree_sum_le`/`natDegree_le_iff_coeff_eq_zero`.
  - `q.coeff n = c n` (top index; lower monomials don't contribute to `coeff n`): `c n = (n.choose n) * ∫ y, (-y)^0 * ψ y = 1 * ∫ y, ψ y = ∫ ψ`. Compute via `Polynomial.coeff` of the monomial sum (`Polynomial.coeff_monomial`, `Finset.sum` picking out `m=n`), `Nat.choose_self`, `pow_zero`, `one_mul`.
  This is the substantial task — budget effort; use `lean_goal` at each rewrite. If a specific Mathlib lemma (e.g. integrability of `(poly)*ψ`, or `sub_pow`'s exact shape) resists, search with `lean_loogle`. Report NEEDS_CONTEXT with the exact stuck goal if the moment-coefficient bookkeeping is genuinely blocked.

- [ ] **Step 3: Verify + commit.** `lean_verify ConvolutionPolynomial.monomial_conv_isPoly` → clean axioms. `lean_build` green.
```bash
git add LeanPlayground/Contrib/ConvolutionPolynomial.lean
git commit -m "feat(contrib): convolution of a monomial with a test function is a polynomial (leading coeff = 0th moment)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: D5 — convolution of a polynomial with a test function; degree exactly preserved when `∫ψ ≠ 0`

**Files:**
- Modify: `LeanPlayground/Contrib/ConvolutionPolynomial.lean`

**Interfaces:**
- Consumes: `ConvolutionPolynomial.monomial_conv_isPoly` (Task 2), `Polynomial.as_sum_range`/`Polynomial.eval_eq_sum_range`, `Polynomial.natDegree`, `Polynomial.leadingCoeff`, `Polynomial.coeff_natDegree`.
- Produces: `ConvolutionPolynomial.poly_conv_isPoly` and `ConvolutionPolynomial.natDegree_poly_conv_eq` (consumed by Task 4).

- [ ] **Step 1: Statements + `sorry`; confirm they elaborate.**

```lean
/-- Convolving a polynomial `p` (as a function) with a continuous compactly-supported `ψ` gives a
polynomial of `natDegree ≤ p.natDegree`. -/
theorem poly_conv_isPoly {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, p.eval (x - y) * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree ≤ p.natDegree ∧ q.coeff p.natDegree = p.leadingCoeff * ∫ y, ψ y := by
  sorry

/-- When `∫ ψ ≠ 0`, the convolution preserves degree exactly. -/
theorem natDegree_poly_conv_eq {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (p : Polynomial ℝ) (hmom : (∫ y, ψ y) ≠ 0) :
    ∃ q : Polynomial ℝ, (fun x : ℝ => ∫ y, p.eval (x - y) * ψ y) = (fun x => q.eval x)
      ∧ q.natDegree = p.natDegree := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`.

- [ ] **Step 2: Prove `poly_conv_isPoly`.** Write `p.eval (x-y) = ∑ k ∈ range (p.natDegree+1), p.coeff k * (x-y)^k` (`Polynomial.eval_eq_sum_range`). Then `∫ y, p.eval (x-y) * ψ y = ∑ k, p.coeff k * ∫ y, (x-y)^k * ψ y` (linearity: `integral_finset_sum` + `integral_const_mul`). By Task 2, each `∫ y, (x-y)^k * ψ y = (q_k).eval x` with `q_k.natDegree ≤ k` and `q_k.coeff k = ∫ψ`. So the function `= (∑ k, p.coeff k • q_k).eval x`; take `q := ∑ k ∈ range (p.natDegree+1), p.coeff k • q_k`. Degree: `natDegree_sum_le` + each `≤ k ≤ p.natDegree`. Top coefficient `q.coeff p.natDegree`: only `k = p.natDegree` contributes `p.coeff (p.natDegree) * (q_{p.natDegree}.coeff p.natDegree) = p.leadingCoeff * ∫ψ` (lower `k` give `q_k.coeff p.natDegree = 0` since `q_k.natDegree ≤ k < p.natDegree`; use `Polynomial.coeff_eq_zero_of_natDegree_lt`). `p.leadingCoeff = p.coeff p.natDegree` by `Polynomial.coeff_natDegree`.

- [ ] **Step 3: Prove `natDegree_poly_conv_eq` from `poly_conv_isPoly`.** Take the same `q`. `q.natDegree ≤ p.natDegree` (have). For `≥`: `q.coeff p.natDegree = p.leadingCoeff * ∫ψ`. Since `p.leadingCoeff ≠ 0` (if `p ≠ 0`; handle `p = 0` separately — both sides `natDegree 0 = 0` and the integral function is `0`) and `∫ψ ≠ 0`, `q.coeff p.natDegree ≠ 0`, so `p.natDegree ≤ q.natDegree` (`Polynomial.le_natDegree_of_ne_zero`). Combine to `=`. (For `p = 0`: `p.eval (x-y) = 0`, function is `0 = (0:Polynomial).eval`, `q := 0`, `natDegree = 0 = p.natDegree`.)

- [ ] **Step 4: Verify + commit.** `lean_verify` both → clean axioms. `lean_build` green.
```bash
git add LeanPlayground/Contrib/ConvolutionPolynomial.lean
git commit -m "feat(contrib): convolution of a polynomial with a test function preserves degree (exactly, when 0th moment nonzero)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: D3 + D7 + assembly — close `exists_uniform_degree_bound`

**Files:**
- Modify: `LeanPlayground/Contrib/TestFunctionDegreeBound.lean`

**Interfaces:**
- Consumes: `MeasureTheory.convolution_assoc`, `ConvolutionPolynomial.convolution_comm_mul` + `convolutionExists_*_mul` (Task 1), `ConvolutionPolynomial.poly_conv_isPoly` + `natDegree_poly_conv_eq` (Task 3), `IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le` (Task 1), `mollify_eq_convolution`, `ClassM.locallyIntegrable`, `ContDiffBump.normed`/`contDiff_normed`/`hasCompactSupport_normed`/`integral_normed`.
- Produces: the fully-proved leaf `TestFunctionDegreeBound.exists_uniform_degree_bound`.

- [ ] **Step 1: Add `import LeanPlayground.Contrib.ConvolutionPolynomial` and D3 `mollify_conv_assoc` statement + `sorry`; confirm it elaborates.**

```lean
/-- Associativity bridge in the `mollify` orientation:
`(σ⋆φ) ⋆ ψ = σ ⋆ (φ⋆ψ)`, i.e. mollifying `σ` by `φ` then by `ψ` equals mollifying by `φ⋆ψ`. -/
theorem mollify_conv_assoc {σ φ ψ : ℝ → ℝ} (hσ : ClassM σ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    convolution (mollify σ φ) ψ (ContinuousLinearMap.mul ℝ ℝ) volume
      = mollify σ (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) := by
  sorry
```
`lean_diagnostic_messages` → only `sorry` here + the still-open leaf.

- [ ] **Step 2: Prove D3.** Rewrite `mollify σ φ = convolution φ σ (mul) volume` (`mollify_eq_convolution`) on the LHS and the RHS's outer `mollify σ (…) = convolution (…) σ (mul) volume`. Goal becomes `convolution (convolution φ σ L) ψ L = convolution (convolution φ ψ L) σ L` (with `L = mul ℝ ℝ`). Apply `MeasureTheory.convolution_assoc` to the LHS to get `convolution φ (convolution σ ψ L) L`, then `convolution_comm_mul` to swap `σ` and `ψ` inside / reorder, matching the RHS (`convolution φ ψ L` then `σ`) — the exact rewrite chain: `convolution_assoc` (coherence `mul_assoc`, measurability via continuity + `ClassM.locallyIntegrable`/`aestronglyMeasurable`, existence via Task 1 D2 helpers), then commutativity. Mind which `convolution_assoc`/`convolution_assoc'` variant's integrability hypotheses are dischargeable (the spike confirmed every convolution here has a compactly-supported factor; use Task 1's `convolutionExists_*_mul`). Use `lean_goal` to track the bilinear-map coherence side-goal (`mul_assoc`). If `convolution_assoc`'s hypotheses fight, report NEEDS_CONTEXT with the exact unmet hypothesis.

- [ ] **Step 3: Add D7 normalized bump as a `have`/`let` inside the assembly (no separate lemma needed).** In the proof of `exists_uniform_degree_bound`, construct `ψ₀`:

```lean
    let b0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    let ψ₀ : ℝ → ℝ := b0.normed volume
    have hψ₀sm : ContDiff ℝ ∞ ψ₀ := b0.contDiff_normed   -- adjust regularity arg to ∞
    have hψ₀c : HasCompactSupport ψ₀ := b0.hasCompactSupport_normed
    have hψ₀int : (∫ y, ψ₀ y) = 1 := b0.integral_normed
```
Confirm via `lean_hover_info` the exact names/regularity arguments (`contDiff_normed` may take `(n := ∞)` or need `le_top`). `∫ψ₀ ≠ 0` follows from `hψ₀int` by `norm_num`/`one_ne_zero`.

- [ ] **Step 4: Prove the assembly (replace the leaf's `sorry`).** Strategy:
  - From `H ψ₀ hψ₀sm hψ₀c` get `mollify σ ψ₀ = (p₀).eval` for some `p₀`; set `d₀ := p₀.natDegree`. Use `d := d₀` as the witness.
  - Goal: `∀ φ (smooth, compact), iteratedDeriv (d₀+1) (mollify σ φ) = 0`. Intro `φ hφ hφc`.
  - From `H φ` get `mollify σ φ = pφ.eval`. It suffices to show `pφ.natDegree ≤ d₀` (then D6 `iteratedDeriv_succ_eq_zero_of_natDegree_le` closes it, after rewriting `mollify σ φ = pφ.eval`).
  - Show `pφ.natDegree ≤ d₀`: consider `mollify σ (convolution φ ψ₀ (mul) volume)` — by D3 (with `φ`,`ψ₀`) it equals `convolution (mollify σ φ) ψ₀ (mul) volume = convolution (pφ.eval) ψ₀ (mul) volume`. By `natDegree_poly_conv_eq` (Task 3, `∫ψ₀ = 1 ≠ 0`) this is a polynomial of `natDegree = pφ.natDegree`. Also, by D3 commuted (`mollify σ (φ⋆ψ₀)` with the roles giving `convolution (mollify σ ψ₀) φ`), it equals `convolution (p₀.eval) φ (mul) volume`, a polynomial of `natDegree ≤ p₀.natDegree = d₀` (`poly_conv_isPoly`). Two polynomial representations of the same function are equal (`Polynomial.funext` over infinite ℝ — confirm name, e.g. `Polynomial.funext`), so `pφ.natDegree = (that degree) ≤ d₀`.
  - Note the orientation detail: `mollify σ (φ⋆ψ₀)` — to express it as `convolution (mollify σ ψ₀) φ`, apply D3 with the bump and `φ` swapped, plus `convolution_comm_mul` for `φ⋆ψ₀ = ψ₀⋆φ`. Track carefully with `lean_goal`; both routes go through `mollify_conv_assoc` + commutativity.
  - Conclude `iteratedDeriv (d₀+1) (mollify σ φ) = iteratedDeriv (d₀+1) (fun x => pφ.eval x) = 0` by D6.

- [ ] **Step 5: Verify.** `lean_diagnostic_messages` on `TestFunctionDegreeBound.lean` → no error, NO `sorry`. `lean_verify TestFunctionDegreeBound.exists_uniform_degree_bound` → `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`). `lean_verify UniversalApproximation.Leshno.exists_nonpoly_mollify` → should now have NO `sorryAx` (its only prior gap was this leaf). `lean_build` green.

- [ ] **Step 6: Commit.**
```bash
git add LeanPlayground/Contrib/TestFunctionDegreeBound.lean
git commit -m "feat(contrib): close exists_uniform_degree_bound via convolution degree-invariance (no Baire)

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## WORKSTREAM A — `tendstoUniformly_riemannSum_aeContinuous` via oscillation + DCT

### Task 5: A1–A3 — measurability and integrability prerequisites

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`

**Interfaces:**
- Consumes: Mathlib `MeasureTheory.measure_zero_iff_ae_notMem`, `subset_closure`, `ContinuousOn.aestronglyMeasurable`, `IsCompact.exists_bound_of_continuousOn`-style bounds, `HasCompactSupport.integrable`/`Continuous.integrable_of_hasCompactSupport`.
- Produces: private lemmas `aestronglyMeasurable_of_aeContinuous`, `ae_continuousAt_of_disc`, `integrable_translate_mul` (consumed by Tasks 7–8). Exact names below.

- [ ] **Step 1: Statements + `sorry`; confirm they elaborate.** Add to `UniformRiemannConvolution.lean` (these take the M-class hypotheses `hbdd`/`hdisc` directly so they are self-contained):

```lean
/-- A locally bounded, a.e.-continuous `f` is a.e.-strongly-measurable. -/
private theorem aestronglyMeasurable_of_aeContinuous {f : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0) :
    AEStronglyMeasurable f volume := by
  sorry

/-- The discontinuity hypothesis gives a.e. continuity. -/
private theorem ae_continuousAt_of_disc {f : ℝ → ℝ}
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0) :
    ∀ᵐ v : ℝ, ContinuousAt f v := by
  sorry
```
`lean_diagnostic_messages` → only `sorry` (+ the still-open leaf). (`integrable_translate_mul` is added in Step 4.)

- [ ] **Step 2: Prove `ae_continuousAt_of_disc`.** `measure_zero_iff_ae_notMem.mp hdisc : ∀ᵐ v, v ∉ closure {¬ContinuousAt f}`. Since `{¬ContinuousAt f} ⊆ closure {…}` (`subset_closure`), `v ∉ closure (…) → v ∉ {¬ContinuousAt f} → ContinuousAt f v`. Use `Filter.Eventually.mono`. Confirm `measure_zero_iff_ae_notMem` exact name (`lean_local_search`).

- [ ] **Step 3: Prove `aestronglyMeasurable_of_aeContinuous`.** `f` is continuous on the (co-null) set `{v | ContinuousAt f v}` (each point is a continuity point ⟹ `ContinuousOn` there via `ContinuousAt.continuousWithinAt`). `ContinuousOn.aestronglyMeasurable` needs the set measurable; the continuity-point set is measurable (its complement ⊆ a null hence measurable set; or use that `{ContinuousAt f}` is a `Gδ` — `lean_local_search "isGδ"`/`continuousAt`). Then extend to all of ℝ a.e. via `AEStronglyMeasurable.congr` on the co-null set, or use `MeasureTheory.aestronglyMeasurable_of_ae...`. If a cleaner Mathlib path exists (e.g. `ContinuousOn.aestronglyMeasurable` + `ae_restrict`), prefer it; confirm via `lean_loogle`. (This mirrors the already-proved `ClassM.aestronglyMeasurable` in `ClassM.lean` — read that proof and adapt.)

- [ ] **Step 4: Add A3 integrability lemma + `sorry`; confirm; prove.**

```lean
/-- For locally bounded a.e.-continuous `f` and continuous compactly-supported `φ`, the integrand
`y ↦ f (s - y) * φ y` is integrable. -/
private theorem integrable_translate_mul {f φ : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (s : ℝ) :
    Integrable (fun y => f (s - y) * φ y) volume := by
  sorry
```
Proof: `f (s - ·)` is `AEStronglyMeasurable` (A1 + composition with the measurable `y ↦ s - y`); it is bounded on the compact `tsupport φ` (translate of a compact set is compact ⟹ `s - tsupport φ` compact ⟹ `hbdd` gives a uniform bound there); `φ` continuous compact support ⟹ `(bounded) * φ` integrable (`HasCompactSupport.integrable_mul` or bound `|f(s-y)φ(y)| ≤ C·|φ(y)|` with `C|φ|` integrable). Use `lean_loogle` for the exact integrability-from-bound lemma.

- [ ] **Step 5: Verify + commit.** `lean_verify` all three private lemmas → clean axioms. `lean_diagnostic_messages` → leaf still the only public `sorry`. `lean_build` green.
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit -m "feat(contrib): a.e.-measurability + integrability prerequisites for the M-class Riemann lemma

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: A6 — a.e.-measurability of the oscillation majorant (the novel lemma)

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`

**Interfaces:**
- Consumes: Mathlib `Measurable.iSup`, `Measurable.ite`, `Measurable.comp` (translation `y ↦ y + q`), measurability of `f` (Task 5 A1), `ae_continuousAt_of_disc` (Task 5 A2).
- Produces: `oscMaj` (definition) + `aemeasurable_oscMaj` + `tendsto_oscMaj_ae` (consumed by Task 7).

- [ ] **Step 1: Define the oscillation majorant + its rational sibling + statements + `sorry`.**

```lean
open scoped Topology

/-- Oscillation majorant: `sup` of `|f v - f (v+h)|` over real shifts `h ∈ [0, Δ]`. -/
noncomputable def oscMaj (f : ℝ → ℝ) (Δ : ℝ) (v : ℝ) : ℝ :=
  ⨆ h : ↥(Set.Icc (0 : ℝ) Δ), |f v - f (v + (h : ℝ))|

/-- Rational-shift sibling (measurable). -/
noncomputable def oscMajRat (f : ℝ → ℝ) (Δ : ℝ) (v : ℝ) : ℝ :=
  ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Δ then |f v - f (v + (q : ℝ))| else 0

/-- The rational majorant is measurable when `f` is. -/
private theorem measurable_oscMajRat {f : ℝ → ℝ} (hf : Measurable f) (Δ : ℝ) :
    Measurable (oscMajRat f Δ) := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`. (If `f` is only `AEStronglyMeasurable`, replace `hf : Measurable f` with a measurable representative — see Step 3 note. Keep `oscMaj` as the genuine real sup; `oscMajRat` is the measurable handle.)

- [ ] **Step 2: Prove `measurable_oscMajRat`.** Countable `iSup` over `ℚ` of measurable functions: each `v ↦ if … then |f v - f (v + q)| else 0` is measurable (`Measurable.ite` on the constant predicate `0 ≤ q ∧ q ≤ Δ` — actually the predicate is independent of `v`, so it is `if (const) then g else 0`, measurable by cases on the `Prop`; `g v = |f v - f (v+q)|` measurable via `hf.sub (hf.comp (measurable_add_const q)) |>.abs`). Then `Measurable.iSup` (countable `ℚ`). The spike proved this in ~8 lines.

- [ ] **Step 3: Add `aemeasurable_oscMaj` + `sorry`; prove `oscMaj =ᵐ oscMajRat` off the discontinuity set, hence `AEMeasurable oscMaj`.**

```lean
/-- The real oscillation majorant is a.e.-measurable. -/
private theorem aemeasurable_oscMaj {f : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0) (Δ : ℝ) :
    AEMeasurable (oscMaj f Δ) volume := by
  sorry
```
Proof: get a measurable representative of `f` is awkward; instead argue directly. At every continuity point `v` of `f` (a.e., by A2), `h ↦ f (v+h)` is continuous, so `Set.Icc 0 Δ ∩ ℚ` is dense in `Set.Icc 0 Δ` and the real sup equals the rational sup: `oscMaj f Δ v = oscMajRat f Δ v` (continuity ⟹ `iSup` over the dense rationals matches; use `Continuous.iSup`-type / `Dense.iSup` reasoning, or `csSup` over a dense subset of a compact domain with the continuous map). Therefore `oscMaj f Δ =ᵐ oscMajRat f Δ`. For `measurable_oscMajRat` you need `Measurable f`: obtain it from A1 `AEStronglyMeasurable f` ⟹ a measurable `f'` with `f =ᵐ f'`; both `oscMaj`/`oscMajRat` built from `f` agree a.e. with those built from `f'` (the a.e.-equality of `f` and `f'` propagates through the countable rational sup and through the continuity-point identification). Net: `AEMeasurable (oscMaj f Δ)` via `oscMaj f Δ =ᵐ oscMajRat f' Δ` (measurable). **This is the delicate lemma** — budget effort; the cleanest assembly is: (i) `f =ᵐ f'` with `f'` measurable; (ii) `oscMajRat f' Δ` measurable (Step 2); (iii) `oscMaj f Δ =ᵐ oscMajRat f' Δ` by combining the continuity-point sup-equality with `f =ᵐ f'`. If step (iii)'s a.e. bookkeeping is genuinely blocked, report NEEDS_CONTEXT with the exact stuck goal.

- [ ] **Step 4: Add `tendsto_oscMaj_ae` + bound + `sorry`; prove.**

```lean
/-- At a.e. `v`, the oscillation majorant tends to `0` along `Δ → 0⁺` (here the cell width
`2*M/m → 0`); and it is bounded by `2*C` on any `|v| ≤ R`. -/
private theorem tendsto_oscMaj_ae {f : ℝ → ℝ}
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0) {M : ℝ} (hM : 0 < M) :
    ∀ᵐ v : ℝ, Filter.Tendsto (fun m : ℕ => oscMaj f (2 * M / m) v) Filter.atTop (𝓝 0) := by
  sorry
```
Proof: at a continuity point `v` (a.e., A2), given `ε>0` pick `δ>0` with `|f(v+h)-f v|<ε` for `|h|<δ`; for `m` large, `2M/m < δ`, so `oscMaj f (2M/m) v ≤ ε`. `oscMaj ≥ 0` always (sup of nonneg; the `h=0` element gives `0`). Conclude `Tendsto … (𝓝 0)` via `squeeze`/`tendsto_of_tendsto_of_tendsto_of_le_of_le` or `Metric.tendsto_atTop`. (The `2*C` bound is used in Task 7's dominator; you may fold it in there instead — keep this lemma to the a.e.-tendsto.)

- [ ] **Step 5: Verify + commit.** `lean_verify measurable_oscMajRat`, `aemeasurable_oscMaj`, `tendsto_oscMaj_ae` → clean axioms. `lean_build` green.
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit -m "feat(contrib): a.e.-measurability and a.e.-vanishing of the oscillation majorant

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 7: A7 — the dominated-convergence core (`∫ oscMaj → 0`)

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`

**Interfaces:**
- Consumes: `MeasureTheory.tendsto_integral_of_dominated_convergence`, `aemeasurable_oscMaj` + `tendsto_oscMaj_ae` (Task 6), `hbdd`, `MeasureTheory.integrableOn_const`.
- Produces: `tendsto_setIntegral_oscMaj` (consumed by Task 8).

- [ ] **Step 1: Statement + `sorry`; confirm it elaborates.**

```lean
/-- Over any fixed compact interval `[-R, R]`, the integral of the oscillation majorant over cells
of width `2*M/m` tends to `0` as `m → ∞`. -/
private theorem tendsto_setIntegral_oscMaj {f : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0) {M : ℝ} (hM : 0 < M) (R : ℝ) :
    Filter.Tendsto (fun m : ℕ => ∫ v in Set.Icc (-R) R, oscMaj f (2 * M / m) v)
      Filter.atTop (𝓝 0) := by
  sorry
```
`lean_diagnostic_messages` → only `sorry`.

- [ ] **Step 2: Prove via dominated convergence.** Apply `MeasureTheory.tendsto_integral_of_dominated_convergence` with the measure `volume.restrict (Set.Icc (-R) R)`:
  - `F m v := oscMaj f (2*M/m) v`; target `0`.
  - measurability: `aemeasurable_oscMaj` (Task 6), restricted (`.restrict`); the lemma wants `AEStronglyMeasurable` — on ℝ, `AEMeasurable → AEStronglyMeasurable` (`AEMeasurable.aestronglyMeasurable`).
  - dominator: the constant `2 * C₀` where `C₀` bounds `|f|` on `|t| ≤ R + |M|·2 + 1`... precisely: `oscMaj f Δ v = sup |f v - f(v+h)| ≤ 2·(bound on `|f|` over the relevant range)`. For `v ∈ Icc (-R) R` and `h ∈ [0, Δ]` with `Δ = 2M/m ≤ 2M`, arguments `v, v+h ∈ Icc (-R-2M) (R+2M)`; get `C` from `hbdd (R + 2*M)`; then `oscMaj f Δ v ≤ 2*C`. The constant `2*C` is integrable on the compact `Icc (-R) R` (`integrableOn_const`, finite measure). Prove the pointwise bound `‖F m v‖ ≤ 2*C` a.e. (`oscMaj ≥ 0`, and each `|f v - f(v+h)| ≤ |f v| + |f(v+h)| ≤ 2C`, so the sup `≤ 2C`; `Real.iSup_le`).
  - a.e. convergence: `tendsto_oscMaj_ae` (Task 6).
  Confirm `tendsto_integral_of_dominated_convergence`'s exact hypothesis shape via `lean_hover_info`; the integral is a `setIntegral` so phrase via `volume.restrict`. Budget care on the bound lemma (`Real.iSup_le` needs the index type nonempty — `Set.Icc 0 Δ` nonempty since `Δ ≥ 0`).

- [ ] **Step 3: Verify + commit.** `lean_verify tendsto_setIntegral_oscMaj` → clean axioms. `lean_build` green.
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit -m "feat(contrib): dominated-convergence core — integral of oscillation majorant vanishes

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 8: A4 + A5 + assembly — close `tendstoUniformly_riemannSum_aeContinuous`, flip inventory

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean`
- Modify: `LeanPlayground/UniversalApproximation/Leshno.lean`

**Interfaces:**
- Consumes: the proved `tendstoUniformly_riemannSum_continuous` (for the φ-variation technique — read its proof), `integrable_translate_mul` (Task 5), `tendsto_setIntegral_oscMaj` (Task 7), `intervalIntegral.integral_comp_sub_left`, `intervalIntegral.sum_integral_adjacent_intervals`, `Metric.tendstoUniformlyOn_iff`.
- Produces: the fully-proved leaf `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous`; updated admit inventory.

- [ ] **Step 1: Replace the leaf's `sorry` — set up the error split.** Read the existing `tendstoUniformly_riemannSum_continuous` proof end-to-end first; reuse its cell/partition definitions (`q`-rounding to left node, `sum_integral_adjacent_intervals`, the `g_eq` integral reduction to `Icc (-M) M`). Use `Metric.tendstoUniformlyOn_iff`: `∀ ε>0, ∀ᶠ m, ∀ s ∈ S, dist (riemannSum … m s) (∫ …) < ε`. Pick `L` with `S ⊆ Icc (-L) L` (`hS.isBounded` ⟹ bounded ⟹ contained in some `Icc`; or `IsCompact.bddAbove`/`bddBelow`). Write the per-`s` error as `φ-variation + f-variation` exactly as in the spec.

- [ ] **Step 2: Prove the φ-variation term → 0 uniformly.** Port the continuous-case argument: `f` bounded by `C₁` on the compact `S - Icc (-M) M` (via `hbdd`), `φ` uniformly continuous on `Icc (-M) M` (`IsCompact.uniformContinuousOn` or `Continuous.uniformContinuous` if globally — φ is continuous with compact support, hence uniformly continuous: `HasCompactSupport`+`Continuous` ⟹ `UniformContinuous`, confirm lemma). Bound `|∫ f(s-y)(φ(y)-φ(q y)) dy| ≤ C₁ · 2M · ω_φ(Δ_m) → 0`. This mirrors the proved lemma's structure — adapt its tactic block.

- [ ] **Step 3: Prove the f-variation term → 0 uniformly via Task 7.** The term `∫_{[-M,M]} (f(s-y) - f(s - q y)) φ(q y) dy`. Bound `|·| ≤ ‖φ‖∞ · ∫_{[-M,M]} |f(s-y) - f(s - q y)| dy`. Substitute `v = s - y` (`intervalIntegral.integral_comp_sub_left`): domain becomes `Icc (s-M) (s+M) ⊆ Icc (-(L+M)) (L+M)`. Within each cell `|y - q y| < Δ_m`, so the shift `|（s-q y) - (s-y)| = |y - q y| < Δ_m`, giving `|f(s-y) - f(s-q y)| ≤ oscMaj f Δ_m (s-y)` (the sup over `[0,Δ_m]` dominates the specific shift; ensure shift sign matches `oscMaj`'s `[0,Δ]` — if the shift is negative, use that `oscMaj` with `[0,Δ]` covers `v` and `v+h`; you may need `|f v - f(v+h)|` for `h∈[-Δ,Δ]` — if so widen `oscMaj` to `Set.Icc (-Δ) Δ` in Task 6, a trivial change, OR note `q y ≤ y` so `s - q y ≥ s - y`, shift `= y - q y ∈ [0,Δ)` is nonneg and `oscMaj`'s `[0,Δ]` is exactly right). So `∫_{[-M,M]} |f(s-y)-f(s-q y)| dy ≤ ∫_{Icc (-(L+M)) (L+M)} oscMaj f Δ_m v dv` (extend the integration domain — integrand nonneg, monotone domain; `setIntegral_mono_set`). By Task 7 (`tendsto_setIntegral_oscMaj … (L+M)`) this → 0, uniformly in `s` (the bound is `s`-independent). Combine the two terms: `∀ᶠ m, ∀ s ∈ S, error < ε`.

- [ ] **Step 4: Verify the leaf.** `lean_diagnostic_messages` on `UniformRiemannConvolution.lean` → no error, NO `sorry`. `lean_verify UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` → `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`). `lean_verify UniversalApproximation.Leshno.mollify_ridge_mem_T` → NO `sorryAx` now. `lean_build` green.

- [ ] **Step 5: Flip the admit inventory in `Leshno.lean`.** Rewrite the "Admit inventory" docstring section to state the development is now **fully `sorry`-free** (0 leaves): both former leaves (`exists_uniform_degree_bound`, `tendstoUniformly_riemannSum_aeContinuous`) are proved; list them under "Proved" with their routes (degree-invariance; oscillation+DCT). Remove the "Remaining documented research leaves" section.

- [ ] **Step 6: Whole-development verification.** `git grep -nE "\bsorry\b|\badmit\b" -- 'LeanPlayground/**/*.lean'` → only docstring prose, ZERO proof-body `sorry`. `lean_verify UniversalApproximation.Leshno.leshno_dense_iff` → `[propext, Classical.choice, Quot.sound]`, **NO `sorryAx`**. `mcp__lean-lsp__lean_build` green.

- [ ] **Step 7: Commit.**
```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean LeanPlayground/UniversalApproximation/Leshno.lean
git commit -m "feat(leshno): close tendstoUniformly_riemannSum_aeContinuous (A); leshno_dense_iff now sorry-free

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Final verification (whole branch)

- [ ] `mcp__lean-lsp__lean_build` succeeds (8582+ jobs, no errors).
- [ ] `git grep -nE "\bsorry\b|\badmit\b" -- 'LeanPlayground/**/*.lean'` lists **no proof-body `sorry`** (docstring mentions only, if any).
- [ ] `lean_verify UniversalApproximation.Leshno.leshno_dense_iff` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- [ ] `lean_verify` on `exists_uniform_degree_bound` and `tendstoUniformly_riemannSum_aeContinuous` → both clean (no `sorryAx`).
- [ ] New `Contrib` files have per-contribution namespaces + accurate inline `Intended Mathlib home:` headers.
- [ ] `Leshno.lean` inventory states the development is `sorry`-free.
- [ ] No existing Cybenko file modified; the two leaf statements and all previously-proved lemmas unchanged; no `BaireSpace`/`BoxIntegral` development added.
- [ ] Open a PR to `main` summarizing the now-fully-`sorry`-free Leshno UAT and the new upstreamable `Contrib` lemmas.
