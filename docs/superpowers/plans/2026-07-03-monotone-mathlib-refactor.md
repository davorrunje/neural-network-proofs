# Monotone-NN Mathlib-Standards Refactor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Refactor the monotone-NN development (`NeuralNetworkProofs/UniversalApproximation/Monotone/`)
to Mathlib-idiomatic quality (Approach A: full re-model), preserving the two headline theorems.

**Architecture:** Re-model internals — bundle stack monotonicity via `OrderHom`, de-flatten the
domination gadget, replace junk-value telescoping with `Finset.sum_range_sub'`, adopt `MonotoneOn`,
extract general lemmas to a new `Monotone/Basic.lean` — while keeping the headline statements and the
`MonoNet` interface byte-identical.

**Tech Stack:** Lean 4 + Mathlib; Lake 5.0.0; lean-lsp MCP tools; subagent-driven-development.

## Global Constraints

- **Two frozen headlines** — statement text byte-identical AND axiom profile
  `[propext, Classical.choice, Quot.sound]` (fresh oleans):
  `UniversalApproximation.Monotone.monotone_interpolation`,
  `UniversalApproximation.Monotone.monotone_approximation`.
- **Frozen interface (so the headline text still elaborates to the same proposition):** the symbols
  the headlines name keep their **exact type signatures** and keep faithfully modeling their concepts:
  `MonoNet d` (Type), `MonoNet.toFun : MonoNet d → (Fin d → ℝ) → ℝ` (the network denotation),
  `MonoNet.depth : MonoNet d → ℕ` (structural; `= 4` still provable), `MonoNet.IsMonotone : MonoNet d
  → Prop` (still means "all layer weights ≥ 0 and read-out weights ≥ 0"). Their *definitions* and all
  other declarations may change freely.
- **`sorry`/`admit`-free.** A genuine blocker → `NEEDS_CONTEXT`, never hidden, never a weakened
  statement.
- **No `set_option maxHeartbeats`** in committed code. **Line length ≤ 100 codepoints.** Docstrings on
  public declarations.
- **Behavior-preserving only at the two headlines.** Intermediate signatures (e.g. `readW`, the
  domination layer indexing, `MonotoneOn` hypotheses on helper lemmas) may change.
- **Extracted general lemmas stay project-local** in `Monotone/Basic.lean` (not `ForMathlib/`).
- **Deferred signing.** Execution commits are **unsigned** (`git -c commit.gpgsign=false commit`);
  implementers stage only, the controller commits. Batch-sign only the **unpushed** commits before the
  PR (the repo blocks force-push). PR opened only after every commit shows `G`.
- **Branch:** `refactor/monotone-mathlib-idiom` (exists, off `main`, carries the signed spec commit).
- Build only the module under work; the controller runs full `lake build` + the headline axiom gate.

## Frozen headline statements (must remain byte-identical)

```lean
theorem monotone_interpolation {d n : ℕ} (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧ ∀ i, N.toFun (x i) = y i

theorem monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0:Fin d → ℝ) 1 → b ∈ Set.Icc (0:Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |N.toFun x - f x| ≤ ε
```

## Per-Task Protocol (every re-model task T1–T7)

1. **Read the current file** (`git show HEAD:<path>` or open it) to learn the exact declarations you
   are changing and which downstream files consume them.
2. **Apply the re-model targets** for the file (below). Keep any frozen-interface signature
   byte-identical (`MonoNet`/`.toFun`/`.depth`/`.IsMonotone`); change definitions/proofs/other decls
   freely. A transient `sorry` while developing is fine; the **staged** file must be `sorry`-free.
3. **Build the module** `lake build NeuralNetworkProofs.UniversalApproximation.Monotone.<M>` → exit 0;
   `lean_diagnostic_messages` → zero errors/`sorry`/linter-warnings.
4. **Headline preservation** (for files upstream of a headline — all except `Monotone.lean`): the
   controller runs the axiom gate; you confirm the headline statement text is unchanged
   (`git diff` shows no edit to the `theorem monotone_interpolation …`/`monotone_approximation …`
   signature lines) and, where practical, `lean_verify` the relevant headline →
   `[propext, Classical.choice, Quot.sound]`.
5. **Stage** the file(s) (`git add`); STOP. The controller commits unsigned, runs the review-package,
   dispatches the reviewer, and records the task in `.superpowers/sdd/progress.md`.

---

## Task 1: Extracted general lemmas (`Monotone/Basic.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Basic.lean`.

**Interfaces — Produces** (final names/statements the implementer finalizes; keep them general and
independent of the network model):
- `sum_le_one_card_le_iff` (or similar): for a `Fintype ι` and `g : ι → ℝ` with `∀ i, g i ≤ 1`,
  `(Fintype.card ι : ℝ) ≤ ∑ i, g i ↔ ∀ i, g i = 1`. (Generalizes `Domination.sum_thresh_ge_iff`.)
- `dist_le_of_coord`: for `x y : Fin d → ℝ` and `0 ≤ c`, `(∀ i, |x i − y i| ≤ c) → dist x y ≤ c`
  (via `dist_pi_le_iff`; `dist` on `Fin d → ℝ` is the sup metric). (From `Approximation.dist_le_of_coord`.)
- `sort_key_linear_extension` (generalizes `Interpolation.reindex_linear_extension`): the statement
  that `Tuple.sort` of an injective lex key `fun i => (a i, toLinearExtension (b i))` yields a
  permutation `π` with `b (π s) ≤ b (π t) → s ≤ t`. State it as generally as the interpolation use
  needs; if a fully general form is awkward, a form specialized to the interpolation key is
  acceptable — but it must not mention the network model.

**Steps:**
- [ ] Write the three lemmas with clean, general statements and proofs (use `dist_pi_le_iff`,
  `Finset.sum_lt_sum`/`Finset.sum_eq_card`-style reasoning, `Tuple.sort_sorted`/`Tuple.eq_sort_iff`).
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Basic` exit 0.
- [ ] Stage; controller commits unsigned.

---

## Task 2: Re-model the network model (`Monotone/Defs.lean`)  ★ linchpin

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Defs.lean`.

**Interfaces — Consumes:** none. **Produces (frozen signatures — keep byte-identical):** `MonoNet`,
`MonoNet.toFun`, `MonoNet.depth`, `MonoNet.IsMonotone`. **May change:** `θ` (rename), `ThreshStack`
internals, the monotonicity lemmas' proofs, `Layer.toFun_monotone` (relocate/rename).

**Re-model targets:**
- Rename `θ → heaviside`; keep `if 0 ≤ z then 1 else 0`; prove `heaviside_monotone`,
  `heaviside_nonneg`, `heaviside_le_one` cleanly.
- Add `ThreshStack.toOrderHom : S.IsMonotone → ((Fin a → ℝ) →o (Fin b → ℝ))` by induction using
  `OrderHom.comp`; define/redefine `ThreshStack.toFun` as its coercion (keep `ThreshStack.toFun`'s
  signature so `MonoNet.toFun` is unaffected), and prove `MonoNet.monotone_toFun` from `OrderHom`
  monotonicity + non-negative read-out. Keep `depth`/`IsMonotone` structural and their signatures.
- Replace the manual `Matrix.mulVec`/`gcongr` layer-monotonicity with
  `Matrix.dotProduct_le_dotProduct_of_nonneg_right`; relocate/rename the lemma out of the misleading
  `Layer.*` prefix (e.g. `layer_toFun_monotone`).
- Keep the dependent-dimension chain (heterogeneous dims).

**Steps:**
- [ ] Apply the re-model; keep `MonoNet`/`.toFun`/`.depth`/`.IsMonotone` signatures byte-identical.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Defs` exit 0.
- [ ] Report the final signatures of every public decl (downstream tasks depend on them). Stage;
  controller commits unsigned.

**Escape hatch:** if `toOrderHom` bundling *complicates* rather than clarifies, report
`DONE_WITH_CONCERNS`/`NEEDS_CONTEXT` and fall back to keeping the current `monotone_toFun` recursion
(still doing the `heaviside` rename + `Matrix.dotProduct` layer lemma). Do NOT `sorry`.

---

## Task 3: De-flatten the domination gadget (`Monotone/Domination.lean`)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Domination.lean`.

**Interfaces — Consumes:** `Defs` (re-modeled), `Basic.sum_le_one_card_le_iff`. **Produces (keep
signatures — `Interpolation` consumes them):** `dominationStack`, `dominationStack_depth`,
`dominationStack_isMonotone`, `dominationStack_apply`.

**Re-model targets:**
- Index the middle layer by `Fin n × Fin d` (curry), flattening to `Fin (n*d)` only at the layer's
  type boundary, to remove the `finProdFinEquiv.symm` / `Fintype.sum_prod_type` /
  `Finset.sum_eq_single` gymnastics in the `_apply` proofs.
- Use `Basic.sum_le_one_card_le_iff` in place of the inline `sum_thresh_ge_iff` (delete the local one).
- Keep `dominationStack`'s four public signatures stable (esp. `dominationStack_apply : … = if p i ≤ x
  then 1 else 0`).

**Steps:**
- [ ] Apply re-model; `lean_diagnostic_messages` clean; `lake build …Monotone.Domination` exit 0.
- [ ] Report final signatures (unchanged expected). Stage; controller commits unsigned.

---

## Task 4: Re-model the interpolation crux (`Monotone/Interpolation.lean`)  ★ crux

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Interpolation.lean`.

**Interfaces — Consumes:** `Defs`, `Domination` (re-modeled), `Basic.sort_key_linear_extension`.
**Produces (FROZEN):** `monotone_interpolation` — statement byte-identical, axiom-clean.

**Re-model targets:**
- Replace `readW` (Fin-predecessor `y' i − y' (i−1)`) + `Ycum` (ℕ junk-off-range) + `telescope_pred`
  with **forward differences and `Finset.sum_range_sub'`**: phrase the read-out so the telescoping sum
  is `∑ k ∈ range …, (Y (k+1) − Y k) = Y … − Y 0` via the library lemma. Delete `telescope_pred` and
  the `0−1=0` / `if _ = 0` / `if h : k < n … else 0` guards (use honest `Fin`/`range` indexing).
- **Reuse `dominationStack` + `dominationStack_isMonotone`** in building `stack₃` and proving
  `interpNet_isMonotone`; delete the duplicated domination-layer non-negativity re-derivation.
- Use `Basic.sort_key_linear_extension` for the reindex linear-extension fact (delete the local
  `reindex_linear_extension` or thin it to a call).
- The read-out change may alter `readW`/`readBias`'s form — that is allowed (not frozen); only the
  headline `monotone_interpolation` is frozen.

**Steps:**
- [ ] Apply re-model; `lean_diagnostic_messages` clean; `lake build …Monotone.Interpolation` exit 0;
  confirm `monotone_interpolation` statement line unchanged (`git diff`) and
  `lean_verify …monotone_interpolation` → `[propext, Classical.choice, Quot.sound]`.
- [ ] Stage; controller commits unsigned. NEEDS_CONTEXT (not `sorry`) if the telescoping re-model
  won't close.

---

## Task 5: Re-model the grid (`Monotone/Grid.lean`)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Grid.lean`.

**Interfaces — Consumes:** `Defs`. **Produces (Approximation consumes):** the grid enumeration, the
monotone-dataset property, and `grid_neighbors`. Signatures may change (e.g. `MonotoneOn`, `m+1`) —
report the final forms for Task 6.

**Re-model targets:**
- State the monotone-dataset property with `MonotoneOn f (Set.Icc (0:Fin d→ℝ) 1)` instead of the
  longhand `∀ ⦃a b⦄, … a ∈ … → …`.
- Use resolution `m + 1` in the grid types so the `m = 0` junk branch in `gridPoint_mem_Icc`
  disappears (or otherwise remove that dead branch cleanly).
- `gridPoint_injective` via `div_left_injective₀`; floor/ceil clamp cleanup with
  `Nat.ceil_le_floor_add_one` and a cleaner `Fin.mk`.

**Steps:**
- [ ] Apply re-model; `lean_diagnostic_messages` clean; `lake build …Monotone.Grid` exit 0.
- [ ] Report final signatures for Task 6. Stage; controller commits unsigned.

---

## Task 6: Re-model the approximation wrapper (`Monotone/Approximation.lean`)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Approximation.lean`.

**Interfaces — Consumes:** `Defs`, `Interpolation`, `Grid` (re-modeled), `Basic.dist_le_of_coord`.
**Produces (FROZEN):** `monotone_approximation` — statement byte-identical, axiom-clean.

**Re-model targets:**
- Thread `MonotoneOn` through the private sandwich lemmas (`hfl`/`hfr` via `MonotoneOn.` API); the
  headline's own `hmono` hypothesis is part of the frozen statement and must NOT change — only the
  surrounding private lemmas / the internal use of `Grid`'s `MonotoneOn`-shaped property adapt. If
  `Grid` now exposes `MonotoneOn`, bridge the frozen `hmono` to it locally.
- Use `Basic.dist_le_of_coord` (delete the local copy).
- Keep the clean uniform-continuity helper.

**Steps:**
- [ ] Apply re-model; `lean_diagnostic_messages` clean; `lake build …Monotone.Approximation` exit 0;
  confirm `monotone_approximation` statement line unchanged and
  `lean_verify …monotone_approximation` → `[propext, Classical.choice, Quot.sound]`.
- [ ] Stage; controller commits unsigned.

---

## Task 7: Wiring + docstrings (`Monotone.lean`)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone.lean`.

**Steps:**
- [ ] Add `import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic`; update the module
  docstring's file/bullet list to include `Basic` and reflect any renamed pieces (`heaviside`).
- [ ] `lake build NeuralNetworkProofs.UniversalApproximation.Monotone` exit 0; diagnostics clean.
- [ ] Stage; controller commits unsigned.

---

## Task F1: Whole-branch verification

- [ ] Full `lake build` → success (serial per-module fallback per `CLAUDE.md` if EMFILE).
- [ ] Headline axiom gate (fresh oleans): both headlines `[propext, Classical.choice, Quot.sound]`.
- [ ] `lake env lean scripts/check_sorry_free.lean` → all 5 project headlines clean.
- [ ] Confirm the two headline statements are **byte-identical** to `main`
  (`git diff origin/main -- …/Interpolation.lean …/Approximation.lean` shows no change to the two
  `theorem` signature lines).
- [ ] Hygiene: no `sorry`/`admit`/`maxHeartbeats` in `Monotone/`; all changed files ≤ 100 codepoints.

## Task F2: Final whole-branch review

- [ ] `review-package $(git merge-base origin/main HEAD) HEAD`; dispatch the final reviewer on the
  most capable model with the Global Constraints. Verify: headline statements byte-identical + axioms
  clean; `MonoNet`/`.toFun`/`.depth`/`.IsMonotone` still faithfully model the concepts (depth-4
  structural, `IsMonotone` = weights ≥ 0); the re-model is genuinely more idiomatic (no new
  hacks/junk-values reintroduced); no `sorry`; ≤ 100 codepoints; extracted `Basic` lemmas are general
  and correctly used.
- [ ] Dispatch ONE fix subagent for any Critical/Important findings; re-verify (F1) and re-review. Log
  Minor findings.

## Task F3: Batch-sign and open PR (requires the user present)

- [ ] Confirm signing works (`echo test | ssh-keygen -Y sign -f ~/.ssh/signing_key.pub -n git`).
- [ ] Sign only the **unpushed** commits: `git rebase --exec 'git commit --amend --no-edit -S'
  <last-pushed-commit>` (do NOT rebase already-pushed commits).
- [ ] `git log --format='%h %G? %s' <base>..HEAD` → every line `G`.
- [ ] Re-verify build + both headline axioms after the rebase; push (fast-forward); open PR
  (`gh pr create --base main`) summarizing the re-model + verification; confirm CI.
