# Monotone Saturating-Activation UAT — Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the shared, activation-generic monotone-interpolation core (indicator-gadget
abstraction + one telescoping engine) and re-derive the merged Mikulincer–Reichman headlines as its
exact (ε=0, threshold) special case — behavior-preserving.

**Architecture:** Generalize the threshold-only model in `Defs.lean` to a per-layer *monotone-
activation* MLP (`heaviside` = one instance); introduce `IsEpsIndicator` (a monotone sub-network
approximating the coordinatewise domination indicator to accuracy ε); refactor `Interpolation.lean`
into a gadget-based engine that yields interpolation with error controlled by ε, with ε=0 recovering
the exact M-R `monotone_interpolation`. Sets up Phases 2 (Thm 3.5) and 3 (Props 3.10/3.11).

**Tech Stack:** Lean 4 + Mathlib; Lake 5.0.0; lean-lsp MCP tools; subagent-driven-development.

**Phasing:** This is **Phase 1 of 3** (spec: `docs/superpowers/specs/2026-07-05-monotone-saturating-uat-design.md`).
Phase 2 (`Saturating.lean` + Theorem 3.5) and Phase 3 (`Equivalence.lean`/`NonPositive.lean`) get
their own plans **after** Phase 1 lands and the spec's *faithfulness gate* (exact vs ε-approximate
Thm 3.5) is resolved from the primary source. Do NOT start Phase 2/3 from this plan.

## Global Constraints

- **Frozen headlines** — byte-identical statements + axiom profile `[propext, Classical.choice,
  Quot.sound]` (fresh oleans): `UniversalApproximation.Monotone.monotone_interpolation` and
  `monotone_approximation`. Their proofs are refactored to route through the new engine; the symbols
  they name — `MonoNet`, `MonoNet.toFun`, `MonoNet.depth`, `MonoNet.IsMonotone` — keep their exact
  type signatures and faithful meanings (`toFun` = denotation, structural `depth` with `= 4`
  provable, `IsMonotone` = all weights ≥ 0 and, now, each layer's activation `Monotone`).
- **`sorry`/`admit`-free** (blocker → `NEEDS_CONTEXT`, never hidden, never a weakened statement);
  **no `set_option maxHeartbeats`**; **lines ≤ 100 codepoints**; docstrings on public declarations.
- **Historical notes:** where an M-R proof is re-routed through the engine, add a docstring line
  ("proof refactored through the shared ε-indicator engine; originally the standalone threshold
  construction of PR #16") and a short note in the spec/docs. Git history also tracks it.
- **Deferred signing:** execution commits **unsigned**; batch-sign only the **unpushed** commits
  before the PR (repo blocks force-push); PR opened only after every commit shows `G`.
- **Branch:** `feat/monotone-saturating-uat` (exists, off `main`, carries the signed spec commit).
- Build only the module under work; controller runs full `lake build` + the headline axiom gate.

## Frozen headline statements (must remain byte-identical)

```lean
theorem monotone_interpolation {d n : ℕ} (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧ ∀ i, N.toFun (x i) = y i

theorem monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0:Fin d → ℝ) 1 → b ∈ Set.Icc (0:Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |N.toFun x - f x| ≤ ε
```

## Per-Task Protocol (every task T1–T5)

1. Read the current file(s) (`git show HEAD:<path>`) and the interfaces named in the task.
2. Apply the task's targets. Keep frozen-interface signatures byte-identical; a transient `sorry`
   while developing is fine, the **staged** file must be `sorry`-free.
3. Build the module `lake build NeuralNetworkProofs.UniversalApproximation.Monotone.<M>` → exit 0;
   `lean_diagnostic_messages` → zero errors/`sorry`/linter-warnings.
4. For tasks upstream of a frozen headline: confirm the headline statement lines are unchanged
   (`git diff origin/main -- <file>`) and (controller) the axiom gate stays clean.
5. Stage (`git add`); STOP. Controller commits unsigned, packages, dispatches the reviewer, records
   the task in `.superpowers/sdd/progress.md`.

---

## Task 1: Generalize the model to per-layer monotone activations (`Defs.lean`)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Defs.lean`.

**Interfaces — Produces (frozen, keep byte-identical):** `MonoNet`, `MonoNet.toFun`,
`MonoNet.depth`, `MonoNet.IsMonotone`, `MonoNet.monotone_toFun`. **May change (internal):**
`ThreshStack` and its `toFun`/`depth`/`IsMonotone`/`toOrderHom`.

**Targets:**
- Generalize the hidden stack so each layer carries its own activation. Concretely, change the
  `cons` constructor to also hold an activation `σ : ℝ → ℝ` (rename `ThreshStack` → e.g. `ActStack`,
  or keep the name), have `toFun` apply that layer's `σ`, and have `IsMonotone` additionally require
  `Monotone σ` for each layer (alongside `∀ i j, 0 ≤ L.W i j`). `toOrderHom`/`monotone_toFun` now use
  the per-layer `Monotone σ` hypothesis via `OrderHom.comp` exactly as before.
- Provide a **threshold specialization**: a helper that builds a stack using `heaviside` at every
  layer (the M-R model), plus a lemma that `heaviside` satisfies the per-layer `Monotone` obligation
  (reuse `heaviside_monotone`).
- Keep `MonoNet` = generalized stack + non-negative read-out; keep `MonoNet.toFun`/`.depth`/
  `.IsMonotone` signatures and `MonoNet.monotone_toFun` (now: monotone stack + nonneg read-out).

**Steps:**
- [ ] Generalize the stack + activation-carrying `cons`; update `toFun`/`depth`/`IsMonotone`/
  `toOrderHom`/`monotone_toFun`; add the threshold specialization helper + its `Monotone` lemma.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Defs` exit 0. (Downstream files break
  until T2/T3 — expected; do not touch them here.)
- [ ] Report the exact new API (stack constructor, threshold helper, all lemma signatures). Stage;
  controller commits unsigned.

## Task 2: Indicator-gadget abstraction + threshold instance (`Indicator.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Indicator.lean`; retire the
threshold-specific content of `Domination.lean` (move `dominationStack` here, or re-export).

**Interfaces — Consumes:** Task 1 model + threshold helper; `Basic` if needed. **Produces:**
- `IsEpsIndicator {d n} (S : <stack> d n) (p : Fin n → (Fin d → ℝ)) (ε : ℝ) : Prop` :=
  `∀ x i, |S.toFun x i − (if p i ≤ x then 1 else 0)| ≤ ε` (monotone stack approximating the
  coordinatewise domination indicators of the points `p` to accuracy `ε`).
- `dominationStack (p) : <stack> d n` (the M-R threshold gadget, now on the generalized model),
  with `dominationStack_depth = 2`, `dominationStack_isMonotone`, `dominationStack_apply` (unchanged
  meaning: `= if p i ≤ x then 1 else 0`), and **`dominationStack_isEpsIndicator :
  IsEpsIndicator (dominationStack p) p 0`** (exact — from `dominationStack_apply`).

**Steps:**
- [ ] Define `IsEpsIndicator`; port `dominationStack` (+ its lemmas) to the generalized model
  (`heaviside` layers); prove `dominationStack_isEpsIndicator … 0`.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Indicator` exit 0.
- [ ] Report signatures. Stage; controller commits unsigned.

## Task 3: Gadget-based interpolation engine + exact M-R corollary (`Interpolation.lean`) ★ crux

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone/Interpolation.lean`.

**Interfaces — Consumes:** Tasks 1–2 (`IsEpsIndicator`, `dominationStack_isEpsIndicator`), `Basic`.
**Produces (FROZEN):** `monotone_interpolation` — byte-identical, axiom-clean.

**Targets:**
- **Engine lemma** (new, general): for a monotone dataset reindexed via `Basic.sort_key_linear_extension`,
  given an `IsEpsIndicator (S) (x∘reindex) ε` gadget, the depth-4 net (gadget → `revPrefixLayer`
  level-sets → telescoping non-negative read-out) satisfies, for each dataset point,
  `|N.toFun (x' j) − y' j| ≤ C · ε` for an explicit `C` (e.g. total read-out variation
  `∑ |readW|`, i.e. `y' (n-1) − y' 0`). Keep the reindex/`revPrefixLayer`/telescoping machinery from
  the current proof; the change is threading the gadget's `ε`-bound instead of the exact
  `dominationStack_apply` equality.
- **Exact corollary:** specialize the engine at the threshold gadget (`dominationStack`,
  `ε = 0` via `dominationStack_isEpsIndicator`) ⇒ `|N.toFun (x' j) − y' j| ≤ 0` ⇒ exact equality;
  transport through the permutation ⇒ **`monotone_interpolation`** (byte-identical statement).
  `interpNet.depth = 4` by `rfl`; `interpNet.IsMonotone` (nonneg weights + monotone activations).

**Steps:**
- [ ] Add the general engine lemma (gadget + ε → interpolation error ≤ C·ε); adapt reindex/
  revPrefix/telescoping to the ε-bound form.
- [ ] Derive `monotone_interpolation` as the ε=0 threshold instance; confirm statement byte-identical
  (`git diff origin/main`) and `lean_verify …monotone_interpolation` → `[propext, Classical.choice,
  Quot.sound]`.
- [ ] Add the historical-note docstring line. `lean_diagnostic_messages` clean; module build exit 0.
- [ ] Stage; controller commits unsigned. **NEEDS_CONTEXT (not `sorry`) if the ε-bound telescoping
  won't close** — do not weaken the frozen statement.

## Task 4: Confirm consumers unaffected (`Grid.lean`, `Approximation.lean`)

**Files:** Read/adjust `Grid.lean`, `Approximation.lean` only if needed.

`monotone_approximation` consumes `monotone_interpolation` (frozen, unchanged) via `Grid`; the model
generalization should not change their statements. Expected NO-OP beyond confirming they build.

**Steps:**
- [ ] `lake build …Monotone.Grid` and `…Monotone.Approximation` exit 0; if the generalized model
  requires a trivial adaptation (e.g. an activation argument in a construction they reference), apply
  the minimal change. Confirm `monotone_approximation` statement byte-identical.
- [ ] Stage any change (or report NO-OP); controller commits unsigned.

## Task 5: Wiring + historical notes (`Monotone.lean`, docs)

**Files:** Modify `NeuralNetworkProofs/UniversalApproximation/Monotone.lean`; add a historical note
under `docs/`.

**Steps:**
- [ ] Update `Monotone.lean` imports/docstring: add `Indicator`; reflect `Domination` retirement/
  rename; note the model is now activation-generic (`heaviside` instance). Ensure both headlines
  remain transitively imported.
- [ ] Add a short `docs/superpowers/` history note: "M-R (PR #16) generalized through the shared
  ε-indicator engine in Phase 1; threshold = ε=0 instance."
- [ ] `lake build NeuralNetworkProofs.UniversalApproximation.Monotone` exit 0. Stage; controller
  commits unsigned.

---

## Task F1: Whole-branch verification

- [ ] Full `lake build` green (serial per-module fallback per `CLAUDE.md` if EMFILE).
- [ ] Both frozen headlines `[propext, Classical.choice, Quot.sound]` on fresh oleans; statement lines
  byte-identical to `origin/main` (`git diff`).
- [ ] `lake env lean scripts/check_sorry_free.lean` clean.
- [ ] No `sorry`/`admit`/`maxHeartbeats` in `Monotone/`; all changed files ≤ 100 codepoints.

## Task F2: Final whole-branch review

- [ ] `review-package $(git merge-base origin/main HEAD) HEAD`; dispatch the final reviewer (most
  capable model) with the Global Constraints. Verify: frozen headlines byte-identical + axiom-clean;
  `MonoNet` interface + meanings preserved; the engine genuinely generalizes (ε=0 ⇒ exact, no gap);
  `IsEpsIndicator` is a faithful abstraction; no `sorry`; ≤ 100 codepoints; historical notes present.
- [ ] Dispatch ONE fix subagent for any Critical/Important findings; re-verify (F1) and re-review;
  log Minor findings.

## Task F3: Batch-sign and open PR (requires the user present)

- [ ] Confirm signing (`echo test | ssh-keygen -Y sign -f ~/.ssh/signing_key.pub -n git`).
- [ ] Sign only the unpushed commits: `git rebase --exec 'git commit --amend --no-edit -S'
  <last-pushed-commit>` (never re-sign already-pushed commits).
- [ ] `git log --format='%h %G? %s' <base>..HEAD` → every line `G`.
- [ ] Re-verify build + both headline axioms after the rebase; push (fast-forward); open PR
  (`gh pr create --base main`) summarizing the unification (engine + M-R = ε=0 instance) + the
  verification; confirm CI. Note in the PR that Phases 2/3 follow, gated on the faithfulness question.
