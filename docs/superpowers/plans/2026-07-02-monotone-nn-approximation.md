# Monotone Neural Network Approximation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize, `sorry`-free in Lean 4 + Mathlib, Result 1 of Mikulincer–Reichman
(arXiv:2207.05275): a depth-4 monotone threshold network interpolates any monotone dataset and
approximates any continuous monotone function on `[0,1]^d` to arbitrary `ℓ∞` accuracy.

**Architecture:** A fresh monotone-threshold-network model under
`NeuralNetworkProofs/UniversalApproximation/Monotone/` (namespace `UniversalApproximation.Monotone`),
reusing `NeuralNetwork.Layer`. Build the model + monotonicity, the 2-layer domination gadget, the
depth-4 interpolation construction (Theorem 1), then the grid + uniform-continuity + sandwich wrapper
(Theorem 2).

**Tech Stack:** Lean 4 + Mathlib; Lake 5.0.0; lean-lsp MCP tools; subagent-driven-development.

## Global Constraints

- **Two public headlines** (final binder details may adjust, math content fixed):
  `UniversalApproximation.Monotone.monotone_interpolation` and
  `UniversalApproximation.Monotone.monotone_approximation`. Both must have axiom profile
  `[propext, Classical.choice, Quot.sound]`.
- **`sorry`/`admit`-free.** A genuine research blocker is reported as `NEEDS_CONTEXT`, never hidden
  behind `sorry` and never worked around by weakening a statement.
- **No `set_option maxHeartbeats`** left in committed code (use it only as a transient local probe).
- **Line length ≤ 100 codepoints** (Mathlib glyphs = 1 codepoint).
- **Docstrings** on every public declaration.
- **Depth is structural**, not a label: `depth` is computed from the network's layers, and
  `N.depth = 4` is a proven fact about each construction.
- **Scope:** depth-4 + existence only. Do NOT track neuron counts / size bounds; do NOT attempt
  Result 2, the totally-ordered depth-3 refinement, or the Lemma-3 lower bound.
- **Deferred signing.** Execution commits are made **unsigned** (`git -c commit.gpgsign=false
  commit`). The controller commits (implementers stage only). The branch is **batch-signed in one
  step before the PR** (signing only unpushed commits; the repo blocks force-push). Never attempt
  `-S` during a task.
- **Branch:** `feat/monotone-nn-approximation` (exists, off `main`, carries the signed spec commit).
- Build only the module under work (`lake build NeuralNetworkProofs.UniversalApproximation.Monotone.<M>`);
  the controller runs full `lake build` + the headline axiom gate.

## Headline signatures (target)

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

The order on `Fin d → ℝ` is the Pi (coordinatewise) order; `Set.Icc 0 1` is the unit cube.

---

## Task 1: Model definitions and monotonicity (`Monotone/Defs.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Defs.lean`.

**Interfaces — Produces:**
- `θ : ℝ → ℝ`, `θ_monotone : Monotone θ`, `θ_nonneg`, `θ_le_one`.
- `ThreshStack : ℕ → ℕ → Type` with `nil`/`cons`; `ThreshStack.toFun`, `.depth`, `.IsMonotone`.
- `MonoNet (d : ℕ)` (structure: `width`, `stack : ThreshStack d width`, `readW`, `readBias`);
  `MonoNet.toFun`, `MonoNet.depth`, `MonoNet.IsMonotone`.
- `MonoNet.monotone_toFun : N.IsMonotone → Monotone N.toFun`.

**Definitions (write verbatim):**

```lean
import Mathlib
import NeuralNetworkProofs.NeuralNetwork.Network

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- Threshold (Heaviside) gate: `1` if `0 ≤ z`, else `0`. -/
noncomputable def θ (z : ℝ) : ℝ := if 0 ≤ z then 1 else 0

/-- A stack of threshold layers `Fin a → ℝ ⟶ Fin b → ℝ`; each `cons` layer applies the affine
map `W.mulVec x + c` then `θ` pointwise (`NeuralNetwork.Layer.toFun θ`). -/
inductive ThreshStack : ℕ → ℕ → Type
  | nil (n : ℕ) : ThreshStack n n
  | cons {a b c : ℕ} (L : NeuralNetwork.Layer a b) (rest : ThreshStack b c) : ThreshStack a c

/-- Denotation of a threshold stack. -/
def ThreshStack.toFun : {a b : ℕ} → ThreshStack a b → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil _, x => x
  | _, _, .cons L rest, x => rest.toFun (L.toFun θ x)

/-- Number of threshold layers. -/
def ThreshStack.depth : {a b : ℕ} → ThreshStack a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.depth + 1

/-- All layer weights are non-negative. -/
def ThreshStack.IsMonotone : {a b : ℕ} → ThreshStack a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons L rest => (∀ i j, 0 ≤ L.W i j) ∧ rest.IsMonotone

/-- A monotone threshold network: a threshold hidden stack + a non-negative linear read-out. -/
structure MonoNet (d : ℕ) where
  width : ℕ
  stack : ThreshStack d width
  readW : Fin width → ℝ
  readBias : ℝ

/-- Network denotation: `∑ i, readW i * (stack output)_i + readBias`. -/
noncomputable def MonoNet.toFun {d} (N : MonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, N.readW i * N.stack.toFun x i) + N.readBias

/-- Total depth: threshold layers plus the read-out layer. -/
def MonoNet.depth {d} (N : MonoNet d) : ℕ := N.stack.depth + 1

/-- Monotone network: non-negative hidden weights and non-negative read-out weights. -/
def MonoNet.IsMonotone {d} (N : MonoNet d) : Prop :=
  N.stack.IsMonotone ∧ ∀ i, 0 ≤ N.readW i
```

**Proof obligations (strategy):**
- `θ_monotone`: `intro a b h; unfold θ; split_ifs <;> [rfl; · linarith? ; · positivity/simp ; rfl]` —
  the only nontrivial case (`0 ≤ a`, `¬ 0 ≤ b`) is impossible via `le_trans`. `θ_nonneg`, `θ_le_one`
  by `split_ifs`.
- Helper `Layer.toFun_monotone`: for `L : NeuralNetwork.Layer a b` with `0 ≤ L.W i j` for all `i j`,
  `Monotone (L.toFun θ)`. Proof: pointwise; `θ_monotone.comp` of the affine map; the affine map
  `x ↦ (W.mulVec x) i + c i` is monotone in `x` because `W.mulVec x i = ∑ j, W i j * x j` and each
  `W i j ≥ 0` (`Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`). Use `Matrix.mulVec` unfolded to
  `∑`.
- `ThreshStack.monotone_toFun : S.IsMonotone → Monotone S.toFun` by induction on `S` (`nil` =
  `monotone_id`; `cons` = `(ih).comp (Layer.toFun_monotone ...)`).
- `MonoNet.monotone_toFun`: `N.toFun` is `x ↦ ∑ i, readW i * stack.toFun x i + readBias`. Each summand
  is monotone (`readW i ≥ 0` times a monotone nonneg-valued `stack.toFun · i`; use
  `mul_le_mul_of_nonneg_left` and `Finset.sum_le_sum`). Conclude `Monotone N.toFun`.

**Steps:**
- [ ] Write the definitions above; confirm the file elaborates (transient `sorry` in proofs is OK
  *within* the task, never committed).
- [ ] Prove `θ_monotone`, `θ_nonneg`, `θ_le_one`, `Layer.toFun_monotone`,
  `ThreshStack.monotone_toFun`, `MonoNet.monotone_toFun`.
- [ ] `lean_diagnostic_messages` on the file → zero errors, zero `sorry`, zero linter warnings.
- [ ] `lake build NeuralNetworkProofs.UniversalApproximation.Monotone.Defs` → exit 0.
- [ ] Stage (`git add` the file); controller commits unsigned.

---

## Task 2: Domination gadget (`Monotone/Domination.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Domination.lean`.

**Interfaces — Consumes:** all of Task 1. **Produces:**
- `dominationStack {d n} (p : Fin n → (Fin d → ℝ)) : ThreshStack d n` — a **2-layer** threshold
  stack whose output coordinate `i` is the domination indicator of point `p i`.
- `dominationStack_depth : (dominationStack p).depth = 2`.
- `dominationStack_isMonotone : (dominationStack p).IsMonotone`.
- `dominationStack_apply : (dominationStack p).toFun x i = if p i ≤ x then 1 else 0`
  (equivalently `= θ (…)`, i.e. `1` iff `x` dominates `p i` coordinatewise, else `0`).

**Construction (paper layers 1–2):**
- Layer 1 `L₁ : Layer d (n*d)`: neuron indexed by `(i,r)` (via `finProdFinEquiv`/`Fin.pair`, `i : Fin
  n`, `r : Fin d`) has weight row `e_r` (`W (⟨i,r⟩) k = if k = r then 1 else 0`, all `≥ 0`) and bias
  `c (⟨i,r⟩) = - (p i) r`. So `L₁.toFun θ x ⟨i,r⟩ = θ (x r - (p i) r) = 𝟙(x r ≥ (p i) r)`.
- Layer 2 `L₂ : Layer (n*d) n`: neuron `i` sums the `d` coordinate indicators of point `i` and
  thresholds at `d`: weight `W i ⟨i',r⟩ = if i' = i then 1 else 0` (`≥ 0`), bias `c i = - d`. So
  `L₂.toFun θ y i = θ (∑_{r} y⟨i,r⟩ - d)`.
- `dominationStack p := .cons L₁ (.cons L₂ (.nil n))`.

**Proof obligations (strategy):**
- `dominationStack_apply`: unfold `toFun` twice. Inner: `L₁.toFun θ x ⟨i,r⟩ = θ (x r - (p i) r)`
  (mulVec of a one-hot row = the picked coordinate: `Matrix.mulVec` with `Finset.sum_eq_single`).
  Then `∑_r θ(x r - (p i) r)` is a sum of `0/1` terms; it equals `d` iff every term is `1` iff
  `∀ r, (p i) r ≤ x r` iff `p i ≤ x` (Pi order: `Pi.le_def`). `θ (∑ - d) = 1` iff `∑ ≥ d` iff all
  coordinates dominated. Key sub-lemma: a sum of `θ`-values (each `≤ 1`) over `Fin d` is `≥ d` iff
  each is `1` (`Finset.sum_eq_card`-style: `∑ ≤ card` with equality iff all `= 1`; use
  `θ_le_one` and `Finset.sum_lt_sum`/`Finset.sum_eq_of_...`).
- Non-negativity of both weight matrices is immediate from the one-hot/`if` definitions.
- `depth` by `rfl`.

**Steps:**
- [ ] Write `dominationStack` and the three lemmas.
- [ ] Prove them; the crux is the "sum of 0/1 indicators `= d` iff all dominated" step — isolate it
  as a `private` lemma `sum_thresh_ge_iff`.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Domination` exit 0.
- [ ] Stage; controller commits unsigned.

---

## Task 3: Interpolation — Theorem 1 (`Monotone/Interpolation.lean`)  ★ crux

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Interpolation.lean`.

**Interfaces — Consumes:** Tasks 1–2. **Produces:** public `monotone_interpolation` (signature above).

**Construction (paper layers 3–4, plus the essential reindexing):**

1. **Reindex to a `y`-monotone linear extension.** The read-out weights `y_i − y_{i−1}` are
   non-negative only if `y` is nondecreasing along the index order AND that order is a linear
   extension of the coordinatewise order (needed for Lemma 5). Obtain a permutation `π : Fin n ≃ Fin
   n` such that, writing `x' = x ∘ π`, `y' = y ∘ π`:
   - `y'` is monotone (`∀ a ≤ b, y' a ≤ y' b`), and
   - `π` is a **linear extension**: `x' a ≤ x' b → a ≤ b`.
   Achieve by sorting indices by the key `(y i, ρ i)` where `ρ` ranks points by a linear extension
   of the finite partial order on `{x i}` (Mathlib: `Mathlib.Order.Extension.Linear` —
   `LinearExtension`, `toLinearExtension`; and `Tuple.sort`/`MonoOfFin`/`Finset.orderIsoOfFin` for
   the sort). Prove both properties from: monotone dataset (`hmono`) + injectivity (`hinj`) ⇒ the
   combined key order refines `≤`. *If assembling `π` with both properties proves hard, this is the
   NEEDS_CONTEXT point — report it, do not `sorry`.*
2. **Layer 3 (reverse prefix sum)** on top of `dominationStack x'` (which outputs `E i = 𝟙(x ≥ x'
   i)`): `L₃ : Layer n n`, neuron `i` = `θ (∑_{r ≥ i} E r − 1)` (weight `W i r = if i ≤ r then 1
   else 0`, all `≥ 0`; bias `-1`). Stack: `stack₃ := .cons L₁ (.cons L₂ (.cons L₃ (.nil n)))`, a
   depth-3 `ThreshStack d n`.
3. **Read-out (layer 4):** `readW i = y' i − y' (i-1)` (with `y' (-1) := 0`, i.e. `readW 0 = y' 0`;
   use `Fin` pred with junk-at-0 handled), `readBias = 0`. `N := ⟨n, stack₃, readW, 0⟩`; `N.depth =
   4` by `rfl`.

**Key lemmas (Lemmas 4–5 + telescoping):**
- Reuse `dominationStack_apply`: at input `x' j`, `E i = 𝟙(x' i ≤ x' j)`.
- `revPrefix_apply` (Lemma 5): `stack₃.toFun (x' j) i = if i ≤ j then 1 else 0`. Proof: layer 3 =
  `θ(∑_{r ≥ i} 𝟙(x' r ≤ x' j) − 1)` = `1` iff `∃ r ≥ i, x' r ≤ x' j`. `i ≤ j` ⇒ `r = j` works
  (`x' j ≤ x' j`). `i > j` ⇒ for `r ≥ i > j`, `x' r ≤ x' j` would give (linear extension) `r ≤ j`,
  contradiction; so the sum is `0`. Uses the reindexing's linear-extension property.
- `readW_nonneg`: `y' i − y' (i-1) ≥ 0` from `y'` monotone.
- Telescoping: `N.toFun (x' j) = ∑_{i ≤ j} (y' i − y' (i-1)) = y' j` (`Finset.sum_range_succ_sub`/
  `Finset.sum_Ioc`-telescope, or `Finset.sum_range` telescoping on `Fin`).
- Transport back through `π`: `N.toFun (x k) = y k` for the original indices (since `x' (π⁻¹ k) = x
  k`, `y' (π⁻¹ k) = y k`).
- `N.IsMonotone`: hidden weights all `≥ 0` (one-hot/`if`), `readW ≥ 0` above.

**Steps:**
- [ ] Build the reindexing `π` with its two properties (isolate as `private` lemmas).
- [ ] Define `L₃`, `stack₃`, `readW`, `N`; prove `depth = 4`, `IsMonotone`.
- [ ] Prove `revPrefix_apply` and the telescoping value lemma; assemble `monotone_interpolation`.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Interpolation` exit 0;
  `lean_verify UniversalApproximation.Monotone.monotone_interpolation` →
  `[propext, Classical.choice, Quot.sound]`.
- [ ] Stage; controller commits unsigned. **If genuinely blocked on the reindexing or telescoping,
  report `NEEDS_CONTEXT` with the precise obstruction — never `sorry`.**

---

## Task 4: Grid and sandwich (`Monotone/Grid.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Grid.lean`.

**Interfaces — Consumes:** Task 1 (order facts only). **Produces:**
- `grid {d} (m : ℕ) : Finset (Fin d → ℝ)` — the points `k ↦ (k i / m)` for `k i ∈ {0,…,m}` inside
  the cube; spacing `1/m`. (Index the grid by `Fin d → Fin (m+1)`.)
- `gridDataset` packaging: the (injective) enumeration `g : Fin N → (Fin d → ℝ)` of grid points and
  its samples `f ∘ g`, with `∀ a b, g a ≤ g b → f (g a) ≤ f (g b)` from `f` monotone (⇒ a monotone
  dataset feeding Task 3).
- `grid_neighbors`: for `x ∈ Icc 0 1`, there are grid indices with points `x₋ ≤ x ≤ x₊`, both in the
  grid, with `‖x₊ − x₊‖`-type bound `∀ i, x₊ i − x₋ i ≤ 1/m` (per-coordinate; enough for the
  sandwich via uniform continuity in sup metric).

**Strategy:** `x₋ i = ⌊m · x i⌋ / m`, `x₊ i = ⌈m · x i⌉ / m` (clamp into `[0,1]`); use
`Nat.floor`/`Int.floor` lemmas (`Int.floor_le`, `Int.le_ceil`, `Int.ceil_le`), `x₋ ≤ x ≤ x₊`
coordinatewise, and `x₊ i − x₋ i ≤ 1/m`. Monotone dataset property is immediate from `f` monotone on
the cube. Keep it elementary; no measure theory.

**Steps:**
- [ ] Define `grid`, the enumeration `g` (with injectivity), the monotone-dataset property, and
  `grid_neighbors`.
- [ ] Prove them (floor/ceil bounds). `lean_diagnostic_messages` clean; `lake build …Monotone.Grid`
  exit 0.
- [ ] Stage; controller commits unsigned.

---

## Task 5: Approximation — Theorem 2 (`Monotone/Approximation.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Approximation.lean`.

**Interfaces — Consumes:** Tasks 1, 3, 4. **Produces:** public `monotone_approximation`.

**Strategy:**
- Uniform continuity: `Set.Icc (0:Fin d→ℝ) 1` is compact (`isCompact_Icc` on the Pi order, or
  `Metric.isCompact_iff`/`Pi` compactness). `ContinuousOn` on a compact set ⇒ uniformly continuous
  (`CompactSpace`/`IsCompact.uniformContinuousOn_of_continuous` or
  `ContinuousOn` + `IsCompact` ⇒ `UniformContinuousOn`). Extract `δ > 0` with
  `‖a − b‖_∞ ≤ δ → |f a − f b| ≤ ε` on the cube. Pick `m` with `1/m ≤ δ` (`exists_nat_one_div_lt`).
- Build the grid (`m`) and the monotone dataset (Task 4), apply `monotone_interpolation` (Task 3) to
  get `N` with `N.depth = 4`, `N.IsMonotone`, `N (g a) = f (g a)`.
- For `x ∈ Icc 0 1` with neighbors `x₋ ≤ x ≤ x₊` (Task 4): `MonoNet.monotone_toFun` gives
  `f x₋ = N x₋ ≤ N x ≤ N x₊ = f x₊`; `f` monotone gives `f x₋ ≤ f x ≤ f x₊`. Both `N x` and `f x`
  lie in `[f x₋, f x₊]`; `|f x₊ − f x₋| ≤ ε` (uniform continuity, `‖x₊−x₋‖_∞ ≤ 1/m ≤ δ`) ⇒
  `|N x − f x| ≤ ε` (`abs_sub_le_of_mem_Icc`/`abs_le` bookkeeping).

**Steps:**
- [ ] Assemble the proof; isolate `uniformContinuity`/`sandwich` as `private` lemmas if it clarifies.
- [ ] `lean_diagnostic_messages` clean; `lake build …Monotone.Approximation` exit 0;
  `lean_verify UniversalApproximation.Monotone.monotone_approximation` →
  `[propext, Classical.choice, Quot.sound]`.
- [ ] Stage; controller commits unsigned. NEEDS_CONTEXT (not `sorry`) if blocked.

---

## Task 6: Root re-export and wiring (`Monotone.lean`)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone.lean`; modify
`NeuralNetworkProofs.lean` to import it.

**Steps:**
- [ ] `Monotone.lean`: module docstring + `import` the four `Monotone/*` files; re-export both
  headlines (they are already in-namespace). Add `import NeuralNetworkProofs.UniversalApproximation.Monotone`
  to root `NeuralNetworkProofs.lean` so `lake build` checks the headlines.
- [ ] `lake build NeuralNetworkProofs.UniversalApproximation.Monotone` and `lake build
  NeuralNetworkProofs` → exit 0.
- [ ] Stage; controller commits unsigned.

---

## Task F1: Whole-branch verification

- [ ] Full `lake build` → success (serial per-module fallback per `CLAUDE.md` if EMFILE).
- [ ] Headline axiom gate (fresh oleans): `import NeuralNetworkProofs; open
  UniversalApproximation.Monotone; #print axioms monotone_interpolation; #print axioms
  monotone_approximation` via `lake env lean` → both `[propext, Classical.choice, Quot.sound]`.
- [ ] `lake env lean scripts/check_sorry_free.lean` clean (extend it to include the two new headlines
  if that script enumerates headlines).
- [ ] Hygiene: no `sorry`/`admit`/`maxHeartbeats` in `Monotone/`; all changed files ≤ 100 codepoints.

## Task F2: Final whole-branch review

- [ ] `review-package $(git merge-base origin/main HEAD) HEAD`; dispatch the final reviewer on the
  most capable model with the Global Constraints. Verify: headlines have the exact axiom profile;
  the model faithfully encodes "monotone threshold network, depth 4"; no `sorry`; constructions have
  non-negative weights; docstrings; lines ≤ 100.
- [ ] Dispatch ONE fix subagent for any Critical/Important findings; re-verify (F1) and re-review.
  Log Minor findings.

## Task F3: Batch-sign and open PR (requires the user present)

- [ ] Confirm signing works (`echo test | ssh-keygen -Y sign -f ~/.ssh/signing_key.pub -n git`).
- [ ] Sign only the **unpushed** commits: `git rebase --exec 'git commit --amend --no-edit -S'
  <last-pushed-commit>` (do NOT rebase already-pushed commits — the repo blocks force-push).
- [ ] `git log --format='%h %G? %s' <base>..HEAD` → every line `G`.
- [ ] Re-verify build + both headline axioms after the rebase; push (fast-forward); open PR
  (`gh pr create --base main`) with a body summarizing both headlines + verification; confirm CI.
