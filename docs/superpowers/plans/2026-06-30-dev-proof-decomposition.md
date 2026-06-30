# Development-Proof Decomposition Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decompose the long proofs in the Cybenko and Leshno developments into small, well-named
lemmas for readability/maintainability, behavior-preserving except where renaming intermediates.

**Architecture:** Two concurrent tracks (Cybenko, Leshno), serial within each, processed **bottom-up
in dependency order**. One file = one task (implementer + reviewer). Each file's consumers are always
downstream (not yet processed), so a rename only ever ripples forward. Spec:
`docs/superpowers/specs/2026-06-30-dev-proof-decomposition-design.md`.

**Tech Stack:** Lean 4 + Mathlib; Lake 5.0.0; lean-lsp MCP tools; subagent-driven-development.

## Global Constraints

- **Frozen invariant — only two declarations.** `UniversalApproximation.Cybenko.universal_approximation`
  and `UniversalApproximation.Leshno.leshno_dense_iff` must keep their **exact statements** and their
  **axiom profile** `[propext, Classical.choice, Quot.sound]`. Everything between leaves and these two
  headlines may be restructured.
- **No `sorry`/`admit`/`native_decide`.** A genuine blocker is reported as `NEEDS_CONTEXT`, never hidden.
- **No new `import Mathlib`** (bare) and **no `set_option maxHeartbeats`** anywhere (there are none in
  these modules today — keep it that way).
- **Line length ≤ 100 codepoints** (Mathlib glyphs count as 1; measure with
  `python3 -c "import sys;[print(len(l.rstrip(chr(10)))) for l in open(sys.argv[1])]" FILE | sort -rn | head`).
- **Cross-file renames allowed.** File-local lemmas: rename/restructure freely, prefer `private`.
  Exported lemmas (consumed by other files): renaming is allowed but the **same commit must update all
  in-repo call sites** (pure identifier swaps). A downstream file may legitimately appear in two task
  diffs (a rename-only touch, then its own decomposition task).
- **Judgment-driven, not mechanical.** Extract a named sub-lemma only where it genuinely clarifies the
  argument or is plausibly reusable for the monotone-NN work. Never split solely to cut a line count.
  Extracted lemmas carry a docstring and minimal hypotheses. **No-op tasks are valid** — if a file has
  nothing worth decomposing, report "left intact" with a one-line rationale and move on.
- **Deferred signing (hard requirement).** The user is NOT available during execution and SSH signing
  needs their live confirmation. Therefore **every execution commit is made UNSIGNED**
  (`git -c commit.gpgsign=false commit`). The whole branch is **batch-signed in one step before the PR**
  (Task F3), which the user must be present for. Never attempt `-S` during a task.
- **Implementers stage only** (`git add <file>`) and never commit; the controller commits (unsigned).
- **Branch:** `refactor/dev-proof-decomposition` (already exists, based on merged `main`, carries the
  signed spec commit). One branch, one PR.

## Per-Task Protocol (applies to every Cybenko/Leshno file task C*/L*)

Each file task follows the same five steps; only the **file** and its **target proofs** differ.

1. **Read the file and locate the long proofs** named in the task (line ranges are indicative; the
   file may have shifted). Use `lean_file_outline` / `lean_diagnostic_messages` to orient.
2. **Decompose by judgment.** Lift each genuinely-separable sub-argument into a named lemma
   (`private` if file-local) with a docstring and minimal hypotheses; rename cryptic intermediates
   (updating downstream call sites in-repo if the lemma is exported). If nothing clarifies, NO-OP.
3. **Build + diagnostics clean.** Build only this module:
   `lake build NeuralNetworkProofs.UniversalApproximation.<Module>` → exit 0; and
   `lean_diagnostic_messages` on the file → zero errors, zero `sorry`, zero linter warnings.
4. **Headline axioms unchanged.** Run the axiom gate (controller does this against fresh oleans):
   ```bash
   cat > /tmp/ck_dev.lean <<'EOF'
   import NeuralNetworkProofs
   open UniversalApproximation.Cybenko UniversalApproximation.Leshno
   #print axioms universal_approximation
   #print axioms leshno_dense_iff
   EOF
   lake env lean /tmp/ck_dev.lean
   ```
   Both must print `[propext, Classical.choice, Quot.sound]`.
5. **Stage + commit.** Implementer: `git add` the touched file(s), STOP. Controller commits unsigned:
   `git -c commit.gpgsign=false commit -m "refactor(<track>): decompose <file> proofs"`, runs the
   review-package, dispatches the task reviewer, records the task in `.superpowers/sdd/progress.md`.

---

## Cybenko track (bottom-up)

### Task C1: Cybenko/Activation

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko/Activation.lean` (62 lines).

**Targets:** Only `noncomputable def signedIntegral` and `def Discriminatory` — no proofs. **Expected
NO-OP.** Confirm there is nothing to decompose and report intact.

- [ ] Apply the Per-Task Protocol. Likely no file change.

### Task C2: Cybenko/Discriminatory

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko/Discriminatory.lean` (389 lines).

**Targets (heaviest file in the track):**
- `sigmoidal_tendsto_neg` (~lines 61–168) — long; likely a limit/algebra split.
- `signed_halfspace_eq_zero` (~169–232).
- `charFun_eq_zero` (~233–349) — largest single proof; extract the self-contained analytic steps.
- `sigmoidal_discriminatory` (~350–389).
- `Sigmoidal.bounded` (~19–52) if a sub-step clarifies.

- [ ] Apply the Per-Task Protocol. Build target: `NeuralNetworkProofs.UniversalApproximation.Cybenko.Discriminatory`.

### Task C3: Cybenko/Family

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko/Family.lean` (58 lines).

**Targets:** `continuous_preactivation`, `generator_mem_S` — both short. **Likely NO-OP or one small
extraction.**

- [ ] Apply the Per-Task Protocol. Build target: `...Cybenko.Family`.

### Task C4: Cybenko/Riesz

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko/Riesz.lean` (184 lines).

**Targets:**
- `continuous_isOrderBounded` (~35–75).
- `riesz_repr` (~76–184) — long; extract the order-bounded / positivity construction steps.

- [ ] Apply the Per-Task Protocol. Build target: `...Cybenko.Riesz`.

### Task C5: Cybenko/Theorem

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko/Theorem.lean` (141 lines).

**Targets:**
- `dense_iff_forall_functional_eq_zero` (~37–98) — main decomposition target.
- `universal_approximation` (~99–124) — **HEADLINE: statement frozen**, proof body may be decomposed.
- `universal_approximation_eps` (~125–141).

- [ ] Apply the Per-Task Protocol. Build target: `...Cybenko.Theorem`. Confirm the
  `universal_approximation` statement line is byte-unchanged.

### Task C6: Cybenko.lean (root)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Cybenko.lean` (96 lines).

**Targets:** Root re-export module. **Expected NO-OP** unless it carries inline proofs worth lifting.

- [ ] Apply the Per-Task Protocol. Likely no file change.

---

## Leshno track (bottom-up)

### Task L1: Leshno/ClassM

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/ClassM.lean` (66 lines).

**Targets:** `ClassM.of_continuous` (~40–58), `isPolynomialFun_of_continuous_of_aePolynomial`
(~59–66). **Likely minor or NO-OP.**

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.ClassM`.

### Task L2: Leshno/MollifyDef

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/MollifyDef.lean` (34 lines).

**Targets:** `mollify` def + `mollify_eq_convolution`. **Expected NO-OP.**

- [ ] Apply the Per-Task Protocol. Likely no file change.

### Task L3: Leshno/Family

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/Family.lean` (141 lines).

**Targets:**
- `T_isClosed` (~105–128) — main target.
- `genFun_reparam_mem` (~89–104), `denselyApproximates_of_forall_T_eq_top` (~134–141) if helpful.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.Family`.

### Task L4: Leshno/SmoothEngine

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/SmoothEngine.lean` (320 lines).

**Targets (heavy):**
- `deriv_pow_mem` (~73–258) — largest single proof in the repo; extract the Taylor/segment and span
  membership steps (note `taylor_seg_bound` is already a `private` helper at ~35–72 — reuse/extend it).
- `smooth_engine` (~269–320).
- `exists_deriv_ne` (~259–268) if a sub-step clarifies.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.SmoothEngine`.

### Task L5: Leshno/Ridge

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/Ridge.lean` (224 lines).

**Targets:**
- `approxByGen_ridge_of_compact_image` (~33–74).
- `ridge_density` (~126–224) — long; extract the `Tplain`/`mem_T_iff_mem_Tplain` span-transfer steps.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.Ridge`.

### Task L6: Leshno/Mollify

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/Mollify.lean` (274 lines).

**Targets:**
- `exists_nonpoly_mollify` (~107–206) — largest; extract the non-polynomial-preservation steps.
- `mollify_ridge_mem_T_of_continuous` (~207–245) and `contDiff_mollify` (~86–106) if helpful.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.Mollify`.

### Task L7: Leshno/Converse

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/Converse.lean` (271 lines).

**Targets:** Many small declarations plus longer ones:
- `aePolynomial_not_dense` (~222–271) — main target.
- `aeEq_poly_of_affine` (~95–128), `subset_of_ae_restrict_mem` (~197–221),
  `aePolyOn_of_mem_genSpan` (~184–196) if a sub-step clarifies. Leave the one-line `@[simp]`/`def`
  declarations intact.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.Converse`.

### Task L8: Leshno/Theorem

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno/Theorem.lean` (89 lines).

**Targets:**
- `univariate_density` (~38–77) — main target.
- `leshno_dense` (~78–84).
- `leshno_dense_iff` (~85–89) — **HEADLINE: statement frozen**, proof body may be decomposed.

- [ ] Apply the Per-Task Protocol. Build target: `...Leshno.Theorem`. Confirm the `leshno_dense_iff`
  statement line is byte-unchanged.

### Task L9: Leshno.lean (root)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Leshno.lean` (78 lines).

**Targets:** Root re-export module. **Expected NO-OP.**

- [ ] Apply the Per-Task Protocol. Likely no file change.

---

## Final tasks

### Task F1: Whole-branch verification

**Files:** none (verification only).

- [ ] **Step 1: Full build.** `lake build` → "Build completed successfully". If EMFILE strikes, fall
  back to the serial per-module build documented in `CLAUDE.md`.
- [ ] **Step 2: Both headlines axiom-clean** (fresh oleans), via the Step-4 snippet — both must be
  `[propext, Classical.choice, Quot.sound]`.
- [ ] **Step 3: Hygiene scan.**
  ```bash
  grep -rn "maxHeartbeats\|^import Mathlib$" NeuralNetworkProofs/UniversalApproximation/   # expect none
  grep -rn "sorry\|admit" NeuralNetworkProofs/UniversalApproximation/                      # expect none
  ```
- [ ] **Step 4: Line length.** Confirm no line in any touched file exceeds 100 codepoints.
- [ ] **Step 5: Sorry-free gate.** `lake env lean scripts/check_sorry_free.lean` → no `sorryAx`.

### Task F2: Final whole-branch review

**Files:** none (review only).

- [ ] **Step 1:** Build the review package from the branch point:
  `BASE=$(git merge-base origin/main HEAD); scripts/review-package "$BASE" HEAD` (path printed).
- [ ] **Step 2:** Dispatch the final reviewer on the most capable model (opus) with the package path
  and the Global Constraints. Verify: no headline statement/axiom changed; no `sorry`; cross-file
  renames have all call sites updated; decomposition genuinely clarifies; lines ≤ 100.
- [ ] **Step 3:** Dispatch ONE fix subagent for any Critical/Important findings (complete list), then
  re-verify (F1) and re-review. Record Minor findings in the ledger.

### Task F3: Batch-sign and open PR

**Files:** none (git + PR).

> Run this only with the user present — signing needs their live confirmation.

- [ ] **Step 1: Confirm signing works.**
  `echo test | ssh-keygen -Y sign -f ~/.ssh/signing_key.pub -n git` → prints a SIGNATURE block (not
  "agent refused operation"). If it fails, STOP and ask the user to re-enable their forwarded agent.
- [ ] **Step 2: Batch-sign the branch.**
  `BASE=$(git merge-base origin/main HEAD); git rebase --exec 'git commit --amend --no-edit -S' "$BASE"`
- [ ] **Step 3: Verify every commit is signed.**
  `git log --format='%h %G? %s' "$BASE"..HEAD` → every line shows `G`.
- [ ] **Step 4: Re-verify after the rebase** (amend rewrites hashes; content is unchanged): repeat F1
  Step 1 (`lake build`) and Step 2 (both headline axioms).
- [ ] **Step 5: Push.** `git push -u origin refactor/dev-proof-decomposition`.
- [ ] **Step 6: Open the PR.** `gh pr create --base main --head refactor/dev-proof-decomposition`
  with a body summarizing the two tracks, the frozen invariant, and the verification results
  (build green, both headlines `[propext, Classical.choice, Quot.sound]`). Confirm CI passes.
