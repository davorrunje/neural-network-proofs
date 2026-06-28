# Decouple `ConvolutionDegreeBound` from Leshno — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `ForMathlib/TestFunctionDegreeBound.lean` Leshno-free and upstream-ready by restating its
lemmas over `convolution`/`LocallyIntegrable`/an inline polynomial predicate, renaming it to
`ConvolutionDegreeBound`, and adapting the sole consumer in-place.

**Architecture:** One atomic refactor. The module rename plus the signature generalization break the
consumer's import and call site simultaneously, so the whole change lands in a single task whose
deliverable is a green `lake build` with unchanged axiom sets. `mollify σ φ` is definitionally
`convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume` (`mollify_eq_convolution`), and
`LocallyIntegrable σ volume` implies `AEStronglyMeasurable σ volume`
(`LocallyIntegrable.aestronglyMeasurable`), so the generalization is mechanical and strength-preserving.

**Tech Stack:** Lean 4 + Mathlib. Verification via lean-lsp MCP tools (`lean_diagnostic_messages`,
`lean_verify`, `lean_goal`, `lean_multi_attempt`, `lean_loogle`, `lean_local_search`,
`lean_hover_info`) and `lake build` / `#print axioms` via `lake env lean`.

## Global Constraints

- Do not change the *statement* of `exists_nonpoly_mollify` or any headline theorem; only
  `exists_uniform_degree_bound` and `mollify_conv_assoc` are restated (a generalization —
  `ClassM σ → LocallyIntegrable σ volume` — so the consumer still type-checks).
- No new Mathlib upstream dependency; `import Mathlib` plus the sibling `ForMathlib` files only.
- The decoupled `ConvolutionDegreeBound.lean` must contain no `import …UniversalApproximation…` and
  no reference to `mollify`, `ClassM`, or `IsPolynomialFun`.
- Preserve git history via `git mv`.
- Line length ≤ 100 codepoints (glyphs like `≤ ∞ ℝ • ⋆ ∫` count as one codepoint each).
- A reintroduced/hidden `sorry` is never acceptable; report NEEDS_CONTEXT instead.
- Commits SSH-signed (`git commit -S`).
- Verification bar: `#print axioms` (on freshly-built oleans) for the renamed lemmas, for
  `exists_nonpoly_mollify`, and for `leshno_dense_iff` must be `[propext, Classical.choice, Quot.sound]`.

## File Structure

- `NeuralNetworkProofs/ForMathlib/TestFunctionDegreeBound.lean` → **renamed** (`git mv`) to
  `NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean`; contents generalized.
- `NeuralNetworkProofs/UniversalApproximation/Leshno/Mollify.lean` — import + one call site adapted.
- `NeuralNetworkProofs/UniversalApproximation/Leshno.lean` — admit-inventory docstring references updated.

---

### Task 1: Generalize and rename `ConvolutionDegreeBound`, adapt the consumer

**Files:**
- Rename + modify: `NeuralNetworkProofs/ForMathlib/TestFunctionDegreeBound.lean` →
  `NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation/Leshno/Mollify.lean` (imports + `exists_nonpoly_mollify`)
- Modify: `NeuralNetworkProofs/UniversalApproximation/Leshno.lean` (inventory docstring)

**Interfaces:**
- Produces (new, in `namespace ConvolutionDegreeBound`):
  - `conv_left_comm_mul {σ φ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)`
    `(hφ : Continuous φ) (hφc : HasCompactSupport φ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :`
    `convolution (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) ψ (ContinuousLinearMap.mul ℝ ℝ) volume`
    `= convolution (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) σ (ContinuousLinearMap.mul ℝ ℝ) volume`
    (the old `mollify_conv_assoc`, restated: `(φ⋆σ)⋆ψ = (φ⋆ψ)⋆σ`).
  - `exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)`
    `(H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →`
    `  ∃ p : Polynomial ℝ, convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => p.eval t) :`
    `∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →`
    `  iteratedDeriv (d + 1) (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) = 0`
- Consumes (unchanged, from this file): `ConvolutionPolynomial.{convolution_comm_mul,`
  `convolutionExists_left_mul, convolutionExists_right_mul, natDegree_poly_conv_eq, poly_conv_isPoly}`,
  `IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le`, and Mathlib's
  `convolution_assoc`, `LocallyIntegrable.aestronglyMeasurable`, `Polynomial.funext`.

- [ ] **Step 1: Rename the file (preserve history).**

```bash
cd /workspaces/lean-playground
git mv NeuralNetworkProofs/ForMathlib/TestFunctionDegreeBound.lean \
       NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean
```

- [ ] **Step 2: Edit the header and imports of `ConvolutionDegreeBound.lean`.**

Replace the top of the file (imports + module docstring + namespace/opens). Remove the Leshno import
and the `open UniversalApproximation.Leshno`; keep the two `ForMathlib` imports:

```lean
import Mathlib
import NeuralNetworkProofs.ForMathlib.ConvolutionPolynomial
import NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial

/-! # Uniform iterated-derivative bound for polynomial convolutions.

If convolving a fixed locally integrable `σ` against every smooth compactly-supported test function
yields an everywhere polynomial, then a single `d` bounds all those polynomials' degrees
simultaneously (equivalently, the `(d+1)`-st iterated derivative of every such convolution vanishes).

The argument is elementary and Baire-free: convolving against a fixed normalized bump `ψ₀`
(`∫ ψ₀ = 1`) preserves polynomial degree, and associativity/commutativity of convolution relates
`φ ⋆ σ` to `ψ₀ ⋆ σ`. Intended Mathlib home: alongside `Mathlib/Analysis/Convolution`. -/

namespace ConvolutionDegreeBound

open MeasureTheory

open scoped ContDiff
```

(Removed: `import NeuralNetworkProofs.UniversalApproximation.Leshno.MollifyDef`,
`open UniversalApproximation.Leshno`. Namespace `TestFunctionDegreeBound` → `ConvolutionDegreeBound`.)

- [ ] **Step 3: Delete the two `private` Leshno-derived lemmas.**

Remove `private theorem classM_aestronglyMeasurable …` and `private theorem classM_locallyIntegrable …`
entirely. They are replaced at use sites by `hσ` (the `LocallyIntegrable` hypothesis) and
`hσ.aestronglyMeasurable`.

- [ ] **Step 4: Restate `mollify_conv_assoc` as `conv_left_comm_mul`.**

The old lemma began with `rw [mollify_eq_convolution, mollify_eq_convolution]` and then worked purely
with convolutions. Restate it directly in convolution form (so that opening `rw` is dropped), change
the hypothesis to `LocallyIntegrable σ volume`, and replace the two derived facts:
`classM_locallyIntegrable hσ` → `hσ`, and `classM_aestronglyMeasurable hσ` → `hσ.aestronglyMeasurable`.
New statement and proof skeleton (the interior — the `hLHS`/`hRHS`/`congr` block using
`convolution_assoc` and `ConvolutionPolynomial.convolution_comm_mul` — is unchanged from the old
proof after the opening `rw` is removed):

```lean
/-- `(φ ⋆ σ) ⋆ ψ = (φ ⋆ ψ) ⋆ σ` for the real (`mul`) convolution, with `σ` locally integrable and
`φ, ψ` continuous with compact support. -/
theorem conv_left_comm_mul {σ φ ψ : ℝ → ℝ} (hσ : LocallyIntegrable σ volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    convolution (convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume) ψ
        (ContinuousLinearMap.mul ℝ ℝ) volume
      = convolution (convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) volume) σ
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have hσint : LocallyIntegrable σ volume := hσ
  have hσm : AEStronglyMeasurable σ volume := hσ.aestronglyMeasurable
  -- … (unchanged interior from the old `mollify_conv_assoc`: hφm, hψm, hcoh, norm factors,
  --     hcSψ, hLHS via `convolution_assoc`, hRHS via `convolution_assoc` + `convolution_comm_mul`,
  --     final `congr 1` + `convolution_comm_mul`) …
```

Guidance: copy the body of the old `mollify_conv_assoc` verbatim *after* its opening
`rw [mollify_eq_convolution, mollify_eq_convolution]` line; substitute the two `classM_*` calls as
above. The old `funext x` and the `hLHS : convolution (convolution φ σ L volume) ψ L volume x = …`
already match the new (convolution-form) goal. The old proof ended by rewriting the inner factor
`σ ⋆ ψ = ψ ⋆ σ`; that still closes the new goal. Verify with `lean_goal` as you port it.

- [ ] **Step 5: Restate `exists_uniform_degree_bound` over the general hypotheses.**

New signature (per Interfaces). Changes to the body:
- Hypothesis `hσ : LocallyIntegrable σ volume` (was `ClassM σ`).
- `H φ hφ hφc` now returns `⟨p, hp⟩` with `hp : convolution φ σ (mul ℝ ℝ) volume = fun t => p.eval t`
  *directly* (no `IsPolynomialFun` unfolding).
- Every `mollify σ ψ` in the body becomes `convolution ψ σ (ContinuousLinearMap.mul ℝ ℝ) volume`.
- Calls to `mollify_conv_assoc hσ …` become `conv_left_comm_mul hσ …`, adjusting orientation: the old
  proof used `mollify_conv_assoc` to rewrite `convolution (mollify σ φ) ψ₀ = mollify σ (φ⋆ψ₀)`; the new
  `conv_left_comm_mul` directly gives `(φ⋆σ)⋆ψ₀ = (φ⋆ψ₀)⋆σ`. Re-derive the two representations
  (`hFA`, `hFB`) of `(φ⋆ψ₀)⋆σ` accordingly: Route A via `conv_left_comm_mul` from `φ⋆σ = p_φ.eval`
  and `natDegree_poly_conv_eq` (degree `= p_φ.natDegree`); Route B via `convolution_comm_mul` +
  `conv_left_comm_mul` from `ψ₀⋆σ = p₀.eval` and `poly_conv_isPoly` (degree `≤ p₀.natDegree`); then
  `Polynomial.funext` gives `q1 = q2` and the bound. The `hbridge` helper
  (`convolution (p.eval) ψ (mul) = fun x => ∫ y, p.eval (x - y) * ψ y`) and the bump `ψ₀` setup are
  unchanged. The conclusion is now `iteratedDeriv (d+1) (convolution φ σ (mul ℝ ℝ) volume) = 0`,
  closed by `IteratedDerivPolynomial.iteratedDeriv_succ_eq_zero_of_natDegree_le` exactly as before.

Build the proof incrementally with `lean_goal`/`lean_multi_attempt`. If any step is genuinely blocked,
report NEEDS_CONTEXT with the exact stuck goal — do not `sorry` or weaken the statement.

- [ ] **Step 6: Verify `ConvolutionDegreeBound.lean` in isolation.**

The file no longer imports any Leshno module, so it elaborates independently. Check with
`lean_diagnostic_messages` (zero errors/`sorry`), then
`lean_verify ConvolutionDegreeBound.exists_uniform_degree_bound` and
`lean_verify ConvolutionDegreeBound.conv_left_comm_mul` → axioms `[propext, Classical.choice, Quot.sound]`.
Confirm by search that the file contains no `mollify`, `ClassM`, `IsPolynomialFun`, or
`import …UniversalApproximation…`:

```bash
grep -nE "mollify|ClassM|IsPolynomialFun|UniversalApproximation" NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean || echo "CLEAN"
```
Expected: `CLEAN`.

- [ ] **Step 7: Adapt the consumer `Mollify.lean`.**

(a) Update the import (line 10):

```lean
import NeuralNetworkProofs.ForMathlib.ConvolutionDegreeBound
```

(b) In `exists_nonpoly_mollify`, replace the single call
`obtain ⟨d, hd⟩ := TestFunctionDegreeBound.exists_uniform_degree_bound hσ H'` with a bridged call
that (i) passes `hσ.locallyIntegrable`, (ii) converts `H'` (the `IsPolynomialFun (mollify …)` form) to
the inline-convolution form, and (iii) converts the returned bound back to `mollify` form so the rest
of the proof is unchanged:

```lean
  -- General (convolution-form) hypothesis from the mollify-form `H'`.
  have Hconv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ p : Polynomial ℝ,
        convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume = fun t => p.eval t := by
    intro φ hφ hφc
    obtain ⟨p, hp⟩ := H' φ hφ hφc          -- hp : mollify σ φ = fun t => p.eval t
    exact ⟨p, by rw [← mollify_eq_convolution]; exact hp⟩
  obtain ⟨d, hdC⟩ :=
    ConvolutionDegreeBound.exists_uniform_degree_bound hσ.locallyIntegrable Hconv
  -- Back to mollify form for the rest of the proof.
  have hd : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      iteratedDeriv (d + 1) (mollify σ φ) = 0 := by
    intro φ hφ hφc
    rw [mollify_eq_convolution]; exact hdC φ hφ hφc
```

Then the existing downstream uses of `d` and `hd` (the `aePolynomial_of_annihilates_moment_vanishing`
argument) remain unchanged. Read lines 102–160 of `Mollify.lean` first and confirm `hd` is consumed in
`mollify` form (`iteratedDeriv (d+1) (mollify σ ψ)`); if a use site referenced the old `hd` name, it
now resolves to this bridged `hd`.

- [ ] **Step 8: Update the admit inventory in `Leshno.lean`.**

Replace the references to the old name (in the "Proved" inventory block, ~lines 49–59) so they read
`ConvolutionDegreeBound.exists_uniform_degree_bound` (and `…conv_left_comm_mul` where the old
`mollify_conv_assoc`/`TestFunctionDegreeBound` was named). Keep line length ≤ 100 codepoints.

```bash
grep -n "TestFunctionDegreeBound\|mollify_conv_assoc" NeuralNetworkProofs/UniversalApproximation/Leshno.lean
```
Update each hit to the new name; re-run the grep and expect no remaining `TestFunctionDegreeBound`.

- [ ] **Step 9: Full build.**

```bash
lake build
```
Expected: `Build completed successfully`. If the consumer bridge has a type mismatch, fix it
(commonly: the `← mollify_eq_convolution` direction, or `hσ.locallyIntegrable` vs `hσ`); re-run.

- [ ] **Step 10: Verify axioms unchanged (freshly-built oleans).**

```bash
cat > /tmp/check_decouple.lean << 'EOF'
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem
import NeuralNetworkProofs.ForMathlib.ConvolutionDegreeBound
open UniversalApproximation.Leshno
#print axioms ConvolutionDegreeBound.exists_uniform_degree_bound
#print axioms ConvolutionDegreeBound.conv_left_comm_mul
#print axioms exists_nonpoly_mollify
#print axioms leshno_dense_iff
EOF
lake env lean /tmp/check_decouple.lean
```
Expected: each line reports `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

- [ ] **Step 11: Confirm no dangling references to the old module/namespace.**

```bash
grep -rn "TestFunctionDegreeBound" NeuralNetworkProofs/ docs/ || echo "NO STALE REFS"
```
Expected: `NO STALE REFS` (docs may legitimately mention the rename; if a live `.lean` reference
remains, fix it).

- [ ] **Step 12: Commit (signed).**

```bash
git add NeuralNetworkProofs/ForMathlib/ConvolutionDegreeBound.lean \
        NeuralNetworkProofs/UniversalApproximation/Leshno/Mollify.lean \
        NeuralNetworkProofs/UniversalApproximation/Leshno.lean
git commit -S -m "refactor(contrib): decouple ConvolutionDegreeBound from Leshno (convolution form)"
```

---

## Self-Review

**Spec coverage.** The three substitutions (`mollify`→`convolution`, `ClassM`→`LocallyIntegrable`,
`IsPolynomialFun`→inline) → Steps 4,5,7. Delete `private classM_*` → Step 3. Remove Leshno import →
Step 2. Rename file+namespace → Steps 1,2. Consumer adaptation (statement unchanged) → Step 7.
Inventory update → Step 8. Verification (build + axioms + no-Leshno-refs) → Steps 6,9,10,11. Covered.

**Placeholder scan.** No "TBD"/"implement later". Step 4/5 hand the implementer the new signatures and
the precise transformation rules with the named lemmas; the proof *interiors* are explicitly "copy the
old body and apply these substitutions", not vague gestures — appropriate, since the old proof already
operates in convolution orientation. NEEDS_CONTEXT is the escape if a port step is genuinely blocked.

**Type consistency.** `conv_left_comm_mul` and `exists_uniform_degree_bound` signatures in the
Interfaces block match their use in Steps 4,5,7,10. The consumer bridge uses `hσ.locallyIntegrable`
(`ClassM.locallyIntegrable`, which exists publicly in `Mollify.lean`) and `mollify_eq_convolution`
(in `MollifyDef.lean`, imported by `Mollify.lean`). The conclusion/`H` forms match between the
producer (Task interface) and the consumer bridge (Step 7).
