# ForMathlib Conformance — Phase 2 (proof decomposition) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Refactor the long monolithic proofs in the nine `NeuralNetworkProofs/ForMathlib/` files into
small, named `private` auxiliary lemmas (Mathlib style), **drop the `maxHeartbeats` override**, and
**extract the shared Riemann cell-skeleton** — all strictly behavior-preserving.

**Architecture:** One file per task (files are independent — Phase 2 changes only proof bodies / adds
`private` lemmas; public statements, signatures, and axioms are unchanged). Each task decomposes that
file's long proofs, then verifies the file builds and `#print axioms` is unchanged. The shared
cell-skeleton lemmas are extracted in the `UniformRiemannConvolution` task and used by both its
Riemann proofs.

**Tech Stack:** Lean 4 + Mathlib. Verification via lean-lsp MCP tools (`lean_goal`, `lean_multi_attempt`,
`lean_diagnostic_messages`, `lean_verify`, `lean_local_search`, `lean_loogle`, `lean_hover_info`) and
`lake build` / `#print axioms` via `lake env lean`.

## Branch & sequencing

- Branch **off `main` after PR #12 merges** (so Phase 2 builds on the minimized-import ForMathlib).
  Suggested branch: `refactor/formathlib-phase2`.
- Builds are light now (Phase 1 minimized ForMathlib imports), so per-file `lake build` /
  `lake env lean` no longer hit the `import Mathlib` EMFILE problem. **Do not** run many full-Mathlib
  builds concurrently regardless; verify per-file with `lake env lean <file>` (concurrent-safe) and do
  a single controller `lake build` at the end of each task. (Hard lesson from the dev-module attempt:
  concurrent heavy builds + git-index races corrupt the build state — prefer shared-checkout +
  `lake env lean`, or strictly serial.)

## Global Constraints

- **Behavior-preserving.** No public statement, signature, or theorem name changes; no axiom changes.
  Only proof bodies are refactored, and new declarations introduced are `private` (a `private`
  auxiliary lemma may be promoted to public + documented only if it reads as reusable API).
- **No `sorry`/`admit`** ever; if a decomposition can't be completed soundly, leave that proof intact
  and report NEEDS_CONTEXT — never weaken or admit.
- **No `set_option maxHeartbeats`** may remain in `ForMathlib` when Phase 2 is done (decomposition
  must bring each piece within the default budget).
- Imports stay minimal (Phase 1); do not re-add `import Mathlib`. Adding a `private` lemma must not
  require a broader import — if it genuinely does, that's a signal the decomposition boundary is wrong.
- Line length ≤ 100 codepoints.
- Commits SSH-signed (`git commit -S`).
- **Verification bar per task:** `lake build` green; `#print axioms` (fresh oleans) on the file's
  public declarations AND on the downstream headlines
  (`UniversalApproximation.Leshno.leshno_dense_iff`, `UniversalApproximation.Cybenko.universal_approximation`)
  = `[propext, Classical.choice, Quot.sound]`; `git diff` shows only proof-body/`private`-lemma changes
  (no public signature touched).

## Decomposition method (applies to every task)

For each long proof: with `lean_goal` open at the proof, identify the logically separable sub-steps
(a self-contained `have` block, a reusable bound, an instance-field proof, a per-case argument). Lift
each into a `private theorem`/`private lemma` with a Mathlib-style name and the **minimal** hypotheses
it needs, placed immediately above its consumer. Rewrite the original proof as a short assembly of
those lemmas. Build incrementally (`lean_diagnostic_messages`) and confirm `#print axioms` is unchanged
after each file. A single irreducible computation (one `ring`/`simp`/`field_simp`/`fun_prop` block)
may stay inline if no meaningful sub-lemma exists — note it if kept.

---

### Task 1: `UniformRiemannConvolution` — the giants + shared skeleton (flagship)

**Files:** Modify `NeuralNetworkProofs/ForMathlib/UniformRiemannConvolution.lean`.

**Interfaces:**
- Produces shared `private` skeleton lemmas (used by both Riemann proofs), e.g. the equispaced node
  facts and the cell-sum rewrites. Suggested names (final names at implementer's discretion, kept
  consistent within the file): `private` lemmas for the node sequence `a i = -M + i·Δ` and its facts
  (`…_zero`, `…_last`, `…_step`, monotone, bounds), the convolution-integral→cell-sum rewrite
  (`riemann_integral_eq_cell_sum`), and the Riemann-sum→cell-sum rewrite (`riemannSum_eq_cell_sum`).
- Public statements `tendstoUniformly_riemannSum_continuous` and
  `tendstoUniformly_riemannSum_aeContinuous` are unchanged.

- [ ] **Step 1: Extract the `f`-agnostic cell-skeleton into shared `private` lemmas.** Both
  `tendstoUniformly_riemannSum_continuous` (~137 lines) and `tendstoUniformly_riemannSum_aeContinuous`
  (~458 lines) re-derive the same setup: the node sequence and `ha0`/`ham`/`hastep`/`ha_le`/`ha_lb`/
  `ha_ub`, the `g_eq`/`hg_sum`/`hr_sum` rewrites, and the `Nat.ceil` mesh-below-δ argument. Lift these
  `f`-agnostic pieces into `private` lemmas (parameterized by `M`, `m`, the cell width `Δ`) above both
  proofs. Verify with `lean_diagnostic_messages` as you go.

- [ ] **Step 2: Rewrite `tendstoUniformly_riemannSum_continuous`** as a short assembly using the
  skeleton lemmas + its per-cell uniform-continuity bound (itself a `private` lemma if it shortens the
  proof). Keep the statement identical.

- [ ] **Step 3: Decompose `tendstoUniformly_riemannSum_aeContinuous`** (the good/bad-cell argument)
  into named `private` lemmas, per the spec: the **φ-variation bound**; the **good-cell oscillation
  bound** (uniform continuity of the kernel on the compact complement of `Metric.thickening δ₀ K`);
  the **bad-cell measure bound** (`Metric.cthickening` measure → 0 via
  `tendsto_measure_cthickening_of_isCompact`); the **per-cell split**; and the **assembly**. Each
  becomes a `private` lemma with minimal hypotheses; the main proof assembles them.

- [ ] **Step 4: Remove `set_option maxHeartbeats 1600000 in`** (line ~203) and its explanatory
  comment. The decomposition must make the main proof elaborate within the default budget.

- [ ] **Step 5: Verify.** `lean_diagnostic_messages`: zero errors, zero `sorry`. Confirm no
  `maxHeartbeats` remains: `grep -n maxHeartbeats NeuralNetworkProofs/ForMathlib/UniformRiemannConvolution.lean` → empty.
  `lean_verify` both public theorems → `[propext, Classical.choice, Quot.sound]`. `git diff` touches
  only proof bodies + new `private` lemmas (the two public signatures unchanged).

- [ ] **Step 6: Build + commit.**

```bash
lake build NeuralNetworkProofs.ForMathlib.UniformRiemannConvolution
git add NeuralNetworkProofs/ForMathlib/UniformRiemannConvolution.lean
git commit -S -m "refactor(formathlib): decompose Riemann-convolution proofs; drop maxHeartbeats"
```

---

### Task 2: `RidgePowersSpan`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/RidgePowersSpan.lean`.

- [ ] **Step 1: Decompose `ridgePoly_span` (~100 lines)** — the polarization/span argument — into
  `private` lemmas for its separable steps (e.g. the coefficient identity, the spanning step), then
  rewrite as an assembly. Also decompose `coeff_ridgePoly_one` (~25) and `coeff_scaleHom` (~23) if a
  named sub-lemma improves clarity (else leave if a single computation).
- [ ] **Step 2: Verify** (`lean_diagnostic_messages` clean; `lean_verify RidgePowersSpan.ridgePoly_span`
  → standard axioms; diff is proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/RidgePowersSpan.lean
git commit -S -m "refactor(formathlib): decompose ridgePoly_span and coeff lemmas"
```

---

### Task 3: `RieszKantorovich`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/RieszKantorovich.lean`.

- [ ] **Step 1: Decompose** `Lpos` (~40), `rkSup_smul` (~35), `instSemilatticeSup` (~29), `rkSup_add`
  (~23). For the instance `instSemilatticeSup`, lift each field's proof (`le_sup_left`/`le_sup_right`/
  `sup_le`, etc.) into a `private` lemma and build the instance from them. Note: this file carries the
  3 term-mode `neg_smul`/`neg_neg` fixes from PR #12 — preserve them.
- [ ] **Step 2: Verify** (clean; `lean_verify` the public decls → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/RieszKantorovich.lean
git commit -S -m "refactor(formathlib): decompose RieszKantorovich lattice/sup proofs"
```

---

### Task 4: `PolynomialDistribution`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/PolynomialDistribution.lean`.

- [ ] **Step 1: Decompose `aePolynomial_of_annihilates_moment_vanishing` (~89)** into `private`
  lemmas for its separable steps, and `exists_factor` (~33) if it helps. Rewrite as assemblies.
- [ ] **Step 2: Verify** (clean; `lean_verify PolynomialDistribution.aePolynomial_of_annihilates_moment_vanishing`
  → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/PolynomialDistribution.lean
git commit -S -m "refactor(formathlib): decompose aePolynomial_of_annihilates_moment_vanishing"
```

---

### Task 5: `ConvolutionDegreeBound`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean`.

- [ ] **Step 1: Decompose** `conv_left_comm_mul` (~70) and `exists_uniform_degree_bound` (~54) into
  `private` lemmas (e.g. the associativity/commutativity bridge steps for the former; the bump-degree
  and two-route degree-equality steps for the latter). Rewrite as assemblies.
- [ ] **Step 2: Verify** (clean; `lean_verify` both public decls → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean
git commit -S -m "refactor(formathlib): decompose conv_left_comm_mul and exists_uniform_degree_bound"
```

---

### Task 6: `ConvolutionPolynomial`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/ConvolutionPolynomial.lean`.

- [ ] **Step 1: Decompose** `monomial_conv_isPoly` (~53) and `poly_conv_isPoly` (~49) into `private`
  lemmas (e.g. the per-monomial coefficient/integral identity), then rewrite as assemblies.
- [ ] **Step 2: Verify** (clean; `lean_verify` both → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/ConvolutionPolynomial.lean
git commit -S -m "refactor(formathlib): decompose monomial_conv_isPoly and poly_conv_isPoly"
```

---

### Task 7: `IteratedDerivPolynomial`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/IteratedDerivPolynomial.lean`.

- [ ] **Step 1: Decompose** `iteratedDeriv_eq_zero_imp_poly` (~66) and `exists_antideriv` (~31) into
  `private` lemmas, then rewrite as assemblies.
- [ ] **Step 2: Verify** (clean; `lean_verify` both → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/IteratedDerivPolynomial.lean
git commit -S -m "refactor(formathlib): decompose iteratedDeriv_eq_zero_imp_poly and exists_antideriv"
```

---

### Task 8: `SmoothCompactAntideriv`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/SmoothCompactAntideriv.lean`.

- [ ] **Step 1: Decompose** `exists_iteratedDeriv_eq_of_moments_zero` (~36), `moment_antideriv` (~34),
  `hasCompactSupport_antideriv` (~27) into `private` lemmas where it improves clarity; rewrite as
  assemblies.
- [ ] **Step 2: Verify** (clean; `lean_verify` the public decls → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/SmoothCompactAntideriv.lean
git commit -S -m "refactor(formathlib): decompose SmoothCompactAntideriv moment/antideriv proofs"
```

---

### Task 9: `ConvolutionIteratedDeriv`

**Files:** Modify `NeuralNetworkProofs/ForMathlib/ConvolutionIteratedDeriv.lean`.

- [ ] **Step 1: `iteratedDeriv_convolution_left` (~27)** is borderline; decompose only if a named
  sub-lemma genuinely clarifies (e.g. a single-derivative-through-convolution step that the induction
  uses). If it's one irreducible induction, leave it and note so in the commit.
- [ ] **Step 2: Verify** (clean; `lean_verify ConvolutionIteratedDeriv.iteratedDeriv_convolution_left`
  → standard axioms; diff proof-only).
- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/ForMathlib/ConvolutionIteratedDeriv.lean
git commit -S -m "refactor(formathlib): tidy iteratedDeriv_convolution_left"
```

---

### Task 10: Final whole-ForMathlib verification

- [ ] **Step 1: Full build.** `lake build` → green.
- [ ] **Step 2: No `maxHeartbeats` anywhere in ForMathlib.**
  `grep -rn maxHeartbeats NeuralNetworkProofs/ForMathlib/` → empty.
- [ ] **Step 3: Downstream axioms unchanged** (fresh oleans):

```bash
cat > /tmp/ck_p2.lean << 'EOF'
import NeuralNetworkProofs
open UniversalApproximation.Cybenko UniversalApproximation.Leshno
#print axioms universal_approximation
#print axioms leshno_dense_iff
EOF
lake env lean /tmp/ck_p2.lean
```
Expected: both `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 4: No long proofs remain** (sanity, not a hard gate): spot-check that the decomposed
  proofs are now short; any intentionally-kept single-computation proof >~20 lines is noted in its
  file. No public signature changed across the branch (`git diff main -- '*.lean' | grep -E '^[+-](theorem|lemma|def|instance)'` shows no signature edits, only additions of `private` lemmas).

---

## Self-Review

**Spec coverage.** Drop `maxHeartbeats` → Task 1 Step 4 + Task 10 Step 2. Decompose the 3 giants
(`tendstoUniformly_riemannSum_aeContinuous`, `tendstoUniformly_riemannSum_continuous`, `ridgePoly_span`)
→ Tasks 1, 2. Shared cell-skeleton extraction → Task 1 Step 1. All 22 listed proofs covered across
Tasks 1–9 (one task per file). Behavior-preservation + downstream-axiom invariant → Global Constraints
+ Task 10. Covered.

**Placeholder scan.** No "TBD"/"implement later". Decomposition is given as a *strategy with named
sub-lemmas* rather than verbatim Lean — appropriate for proof-refactoring (the exact lemma bodies come
from the existing proofs' sub-steps; the implementer lifts them with LSP), with NEEDS_CONTEXT as the
discipline if a decomposition can't be completed soundly. Suggested lemma names are explicitly
implementer's-discretion-but-consistent.

**Type/consistency.** The only cross-task interface is Task 1's shared skeleton lemmas, used within
Task 1's own two proofs (same file) — no cross-file signature coupling, since every other task is
self-contained in one file and changes no public API. The axiom-gate theorem names match the post-reorg
namespaces.
