# Runje et al. — Partial-Monotone UAP Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize, sorry-free, that the architecture `g(u,x) = MonoNet(concat(clamp(φ(u)), x))` — with `φ` an unconstrained Leshno single-hidden-layer embedding — is (a) always monotone in `x` (soundness) and (b) a universal approximator of continuous functions monotone in `x` on the unit cube (UAP). Credited **Runje et al.**

**Architecture:** New namespace `UniversalApproximation.Runje` under `NeuralNetworkProofs/UniversalApproximation/Runje/`. Reuse `Monotone.monotone_approximation` (joint monotone UAP on the cube) and `Leshno.leshno_dense`/`DenselyApproximates` (unconstrained UAP) as black boxes. Proof = soft partition-of-unity reduction + clamp fix (spec §6).

**Tech Stack:** Lean 4, Mathlib, Lake 5.0.0. LSP tools (`lean_goal`, `lean_leansearch`, `lean_loogle`, `lean_multi_attempt`, `lean_diagnostic_messages`) for proof development.

**Spec:** `docs/superpowers/specs/2026-07-10-runje-partial-monotone-uap-design.md`.

## Global Constraints

- **No `sorry`/`admit`.** Every commit must be sorry-free. A research blocker is reported as `NEEDS_CONTEXT`, never hidden.
- **Line length ≤ 100 codepoints** (measure codepoints, not bytes: `python3 -c "print(len(line))"`).
- **Minimal, precise imports** — no blanket `import Mathlib`. Confirm with a clean build; `#min_imports`/`lake exe shake` under-report, so verify.
- **Namespace:** `UniversalApproximation.Runje`. Module prefix `NeuralNetworkProofs.UniversalApproximation.Runje.<File>`.
- **File header** (every file): Apache-2.0 block, `Authors: Davor Runje`, then a `/-! ... -/` module doc crediting **Runje et al.**
- **Build a module:** `lake build NeuralNetworkProofs.UniversalApproximation.Runje.<File>`. If a from-scratch rebuild hits `Too many open files`, build serially per module (CLAUDE.md build gotcha).
- **Sorry-free gate:** `lake env lean scripts/check_sorry_free.lean` — a clean headline reports exactly `[propext, Classical.choice, Quot.sound]`; any `sorryAx` fails.
- **`#print axioms` reads the compiled olean** — rebuild before trusting it.

## Reused external signatures (verbatim)

```lean
-- Monotone/Defs.lean
structure MonoNet (d : ℕ) where
  width : ℕ ; stack : ActStack d width ; readW : Fin width → ℝ ; readBias : ℝ
noncomputable def MonoNet.toFun {d} (N : MonoNet d) (x : Fin d → ℝ) : ℝ
def MonoNet.IsMonotone {d} (N : MonoNet d) : Prop
theorem MonoNet.monotone_toFun {d} (N : MonoNet d) (h : N.IsMonotone) : Monotone N.toFun

-- Monotone/Approximation.lean
theorem monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |N.toFun x - f x| ≤ ε

-- Leshno/Family.lean
def genFun (σ : ℝ → ℝ) {K : Set E} (w : E) (b : ℝ) : ↥K → ℝ := fun x => σ (⟪w, (x:E)⟫ + b)
def genSpan (σ : ℝ → ℝ) (K : Set E) : Submodule ℝ (↥K → ℝ)
def DenselyApproximates (σ : ℝ → ℝ) : Prop :=
  ∀ {n} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → ∀ (f : C(↥K, ℝ)) {ε},
    0 < ε → ∃ g ∈ genSpan σ K, ∀ x, |f x - g x| < ε

-- Leshno/Theorem.lean
theorem leshno_dense {σ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) : DenselyApproximates σ
```

---

### Task 1: `Clamp.lean` — the coordinatewise clamp

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/Clamp.lean`

**Interfaces:**
- Consumes: Mathlib only.
- Produces:
  - `clamp01 : ℝ → ℝ`
  - `clamp01_nonneg : ∀ t, 0 ≤ clamp01 t`
  - `clamp01_le_one : ∀ t, clamp01 t ≤ 1`
  - `clamp01_mem_Icc : ∀ t, clamp01 t ∈ Set.Icc (0:ℝ) 1`
  - `clamp01_eq_self : ∀ {t}, t ∈ Set.Icc (0:ℝ) 1 → clamp01 t = t`
  - `clamp01_continuous : Continuous clamp01`
  - `abs_clamp01_sub_le : ∀ a b, |clamp01 a - clamp01 b| ≤ |a - b|`

- [ ] **Step 1: Write the file with all definitions and statements.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Unit-interval clamp (Runje et al.)

The fixed bounded output activation `clamp01` used by the partial-monotone architecture of
Runje et al. It clamps a real into `[0,1]`; baked into `PartMonoNet.toFun` so the embedding
value fed to the monotone network always lies in the unit cube.
-/

namespace UniversalApproximation.Runje

/-- Clamp a real into the unit interval `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma clamp01_mem_Icc (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clamp01_nonneg t, clamp01_le_one t⟩

lemma clamp01_eq_self {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right h.2, max_eq_right h.1]

lemma clamp01_continuous : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma abs_clamp01_sub_le (a b : ℝ) : |clamp01 a - clamp01 b| ≤ |a - b| := by
  sorry
```

- [ ] **Step 2: Prove `abs_clamp01_sub_le`.**

Strategy: `max`/`min` with a constant are `1`-Lipschitz. Either (a) `LipschitzWith.dist_le_mul` from `lipschitzWith_const.max ...` / `LipschitzWith.min`/`.max`, then `Real.dist_eq`; or (b) directly: `clamp01` composes `fun t => min 1 t` and `fun t => max 0 t`, each of which satisfies `|f a − f b| ≤ |a − b|` (search `abs_max_sub_max_le_abs`, `abs_min_sub_min_le_abs` via `lean_loogle`). Verify the exact lemma names with `lean_leansearch "min is 1-Lipschitz absolute value"`.

- [ ] **Step 3: Build and check no `sorry`.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.Clamp`
Expected: builds with no errors, no `sorry` warning. Confirm with `lean_diagnostic_messages` on the file (no `declaration uses 'sorry'`).

- [ ] **Step 4: Commit.**

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/Clamp.lean
git commit -m "feat(runje): clamp01 unit-interval clamp + lemmas"
```

---

### Task 2: `Defs.lean` — `PartMonoNet` and soundness

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/Defs.lean`

**Interfaces:**
- Consumes: `MonoNet`, `MonoNet.toFun`, `MonoNet.IsMonotone`, `MonoNet.monotone_toFun` (Monotone.Defs); `clamp01`, `clamp01_*` (Task 1); `Fin.append`, `Fin.append_left`, `Fin.append_right`, `Fin.addCases`.
- Produces:
  - `structure PartMonoNet (df dm : ℕ)` with fields `embWidth : ℕ`, `emb : (Fin df → ℝ) → (Fin embWidth → ℝ)`, `mono : MonoNet (embWidth + dm)`
  - `PartMonoNet.toFun (P) (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ`
  - `PartMonoNet.monotone_snd (P) (h : P.mono.IsMonotone) (u) : Monotone (P.toFun u)`

- [ ] **Step 1: Write the file.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.Clamp

/-!
# Partial-monotone networks (Runje et al.)

A `PartMonoNet` embeds the non-monotone input block through an unconstrained map `emb`,
clamps it into `[0,1]`, concatenates it with the monotone block, and feeds the result to a
monotone network. Soundness: the denotation is monotone in the monotone block for every fixed
non-monotone input. UAP is proved in `Approximation.lean`.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone

/-- A partial-monotone network: unconstrained embedding + monotone network over the
concatenation of the clamped embedding with the monotone inputs. -/
structure PartMonoNet (df dm : ℕ) where
  /-- Embedding width. -/
  embWidth : ℕ
  /-- Unconstrained embedding of the non-monotone block. -/
  emb : (Fin df → ℝ) → (Fin embWidth → ℝ)
  /-- Monotone network over the concatenated `[clamp(emb u), x]`. -/
  mono : MonoNet (embWidth + dm)

/-- Denotation: clamp the embedding, append the monotone inputs, apply the monotone net. -/
noncomputable def PartMonoNet.toFun {df dm} (P : PartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)

/-- **Soundness.** A partial-monotone network with a monotone core is monotone in the
monotone block `x`, for every fixed non-monotone input `u`. -/
theorem PartMonoNet.monotone_snd {df dm} (P : PartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u) := by
  intro x y hxy
  refine P.mono.monotone_toFun h ?_
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]
  · simpa only [Fin.append_right] using hxy j
```

- [ ] **Step 2: Build and verify the soundness proof.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.Defs`
Expected: builds, no `sorry`. If `Fin.addCases`/`append_left`/`append_right` names or the `le_refl` closure on the left branch mismatch, inspect with `lean_goal` at the `Fin.addCases` line. The left branch goal is `clamp01 (P.emb u i) ≤ clamp01 (P.emb u i)` (closed by `le_refl`, which `simp only [Fin.append_left]` should discharge; if not, append `exact le_rfl`).

- [ ] **Step 3: Commit.**

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/Defs.lean
git commit -m "feat(runje): PartMonoNet structure + soundness (monotone in x)"
```

---

### Task 3: `PartitionOfUnity.lean` — normalized tent partition of unity

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/PartitionOfUnity.lean`

This is the heaviest analytic task. The **normalization trick** (spec §6, refined): build unnormalized tensor-product tents, then divide by their sum. This makes `∑ ψ = 1` free and replaces the delicate "sum of hats = 1" identity with the easy "sum of tents > 0".

**Interfaces:**
- Consumes: Mathlib (`Finset.prod_univ_sum`, `Finset.sum_div`, `Continuous.div`, `isCompact_Icc`, `dist_pi_le_iff`).
- Produces (all with `variable {df : ℕ}` and a subdivision count `m : ℕ`):
  - `tentNode (m) (k : Fin df → Fin (m+1)) : Fin df → ℝ := fun c => (k c : ℝ) / m`
  - `tent (m) (k : Fin df → Fin (m+1)) (u : Fin df → ℝ) : ℝ` (tensor product of 1-D hats)
  - `tentDenom (m) (u : Fin df → ℝ) : ℝ := ∑ k, tent m k u`
  - `psi (m) (k : Fin df → Fin (m+1)) (u : Fin df → ℝ) : ℝ := tent m k u / tentDenom m u`
  - `tent_nonneg`, `psi_nonneg : 0 ≤ psi m k u`
  - `tentDenom_pos : 1 ≤ m → u ∈ Set.Icc 0 1 → 0 < tentDenom m u`
  - `sum_psi_eq_one : 1 ≤ m → u ∈ Set.Icc 0 1 → (∑ k, psi m k u) = 1`
  - `psi_le_one : 1 ≤ m → u ∈ Set.Icc 0 1 → psi m k u ≤ 1`
  - `tentNode_mem_Icc : tentNode m k ∈ Set.Icc (0 : Fin df → ℝ) 1`
  - `psi_support : psi m k u ≠ 0 → dist (tentNode m k) u ≤ 1 / m`
  - `psi_continuousOn : 1 ≤ m → ContinuousOn (psi m k) (Set.Icc 0 1)`

- [ ] **Step 1: Write the 1-D hat and its lemmas.**

```lean
/-- 1-D hat centred at node `k/m`, width `1/m`. -/
def hat1 (m k : ℕ) (t : ℝ) : ℝ := max 0 (1 - m * |t - k / m|)

lemma hat1_nonneg (m k : ℕ) (t : ℝ) : 0 ≤ hat1 m k t := le_max_left _ _

/-- Off its support the hat is zero. -/
lemma hat1_eq_zero_of_far {m k : ℕ} {t : ℝ} (h : 1 / m ≤ |t - k / m|) :
    hat1 m k t = 0 := by
  sorry  -- 1 - m*|…| ≤ 0, so max 0 _ = 0; needs 0 < m

/-- On its support the argument is close to the node. -/
lemma hat1_support {m k : ℕ} {t : ℝ} (h : hat1 m k t ≠ 0) : |t - k / m| < 1 / m := by
  sorry  -- contrapositive of hat1_eq_zero_of_far

lemma hat1_continuous (m k : ℕ) : Continuous (hat1 m k) := by
  unfold hat1; fun_prop

/-- The rounded node makes the hat strictly positive (used for denominator positivity). -/
lemma hat1_pos_at_round {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ k : Fin (m+1), 0 < hat1 m k t := by
  sorry  -- k = round (m*t) clamped to [0,m]; then |t - k/m| ≤ 1/(2m) < 1/m
```

Proof notes: `hat1_pos_at_round` — take `k = ⌊m*t + 1/2⌋` clamped into `Fin (m+1)`; then `|t − k/m| ≤ 1/(2m)`, so `1 − m*|…| ≥ 1/2 > 0`. Use `Nat.floor`, `Int.fract` bounds, or `round`. Validate the rounding lemma with `lean_leansearch "round distance half"`.

- [ ] **Step 2: Build and verify the 1-D layer sorry-free.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity`
Expected: 1-D lemmas compile (later defs still `sorry` — that is fine *within this task's working state only*; do not commit until Step 5).

- [ ] **Step 3: Write the tensor-product tent and normalized `psi`.**

```lean
def tentNode (m : ℕ) (k : Fin df → Fin (m+1)) : Fin df → ℝ := fun c => (k c : ℝ) / m

def tent (m : ℕ) (k : Fin df → Fin (m+1)) (u : Fin df → ℝ) : ℝ :=
  ∏ c, hat1 m (k c) (u c)

noncomputable def tentDenom (m : ℕ) (u : Fin df → ℝ) : ℝ := ∑ k, tent m k u

noncomputable def psi (m : ℕ) (k : Fin df → Fin (m+1)) (u : Fin df → ℝ) : ℝ :=
  tent m k u / tentDenom m u

lemma tent_nonneg (m) (k) (u) : 0 ≤ tent m k u :=
  Finset.prod_nonneg (fun c _ => hat1_nonneg _ _ _)

lemma psi_nonneg (m) (k) (u) : 0 ≤ psi m k u :=
  div_nonneg (tent_nonneg _ _ _) (Finset.sum_nonneg fun k _ => tent_nonneg _ _ _)
```

- [ ] **Step 4: Prove the remaining tent lemmas.**

Prove, in order (each with `lean_goal`/`lean_multi_attempt` support):

- `tentDenom_pos`: from `hat1_pos_at_round` at each coordinate, the tent at the multi-index of rounded nodes is a product of positives hence `> 0`; it is one summand of `tentDenom`, and all summands are `≥ 0`, so `tentDenom > 0` via `Finset.sum_pos'` / `Finset.single_lt_sum`.
- `sum_psi_eq_one`: `∑ k, tent m k u / tentDenom m u = (∑ k, tent m k u) / tentDenom m u` by `Finset.sum_div`, and `∑ k, tent m k u = tentDenom m u` by definition, so `= tentDenom / tentDenom = 1` using `tentDenom_pos ≠ 0`.
- `psi_le_one`: `psi ≤ ∑ k, psi = 1` since each `psi ≥ 0` (`Finset.single_le_sum` + `sum_psi_eq_one`).
- `tentNode_mem_Icc`: `0 ≤ (k c)/m ≤ 1` since `k c ≤ m` (`Fin.is_le` gives `k c ≤ m`); `Pi` order membership coordinatewise.
- `psi_support`: `psi m k u ≠ 0 → tent m k u ≠ 0 → ∀ c, hat1 m (k c) (u c) ≠ 0` (`Finset.prod_ne_zero_iff`) `→ ∀ c, |u c − k c/m| < 1/m` (`hat1_support`) `→ dist (tentNode m k) u ≤ 1/m` via `dist_pi_le_iff` (sup metric) — note `dist` on `Fin df → ℝ` is the sup of coordinate distances; `|k c/m − u c| = |u c − k c/m|`.
- `psi_continuousOn`: `tent` is continuous (finite product of `hat1_continuous ∘ eval`); `tentDenom` continuous; on the cube `tentDenom > 0` (`tentDenom_pos`), so `ContinuousOn (tent / tentDenom)` by `ContinuousOn.div` with the nonvanishing hypothesis.

```lean
lemma tentDenom_pos {m : ℕ} (hm : 1 ≤ m) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : 0 < tentDenom m u := by
  sorry
lemma sum_psi_eq_one {m : ℕ} (hm : 1 ≤ m) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : (∑ k, psi m k u) = 1 := by
  sorry
lemma psi_le_one {m : ℕ} (hm : 1 ≤ m) (k : Fin df → Fin (m+1)) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : psi m k u ≤ 1 := by
  sorry
lemma tentNode_mem_Icc (m : ℕ) (k : Fin df → Fin (m+1)) :
    tentNode m k ∈ Set.Icc (0 : Fin df → ℝ) 1 := by
  sorry
lemma psi_support {m : ℕ} (k : Fin df → Fin (m+1)) {u : Fin df → ℝ}
    (h : psi m k u ≠ 0) : dist (tentNode m k) u ≤ 1 / m := by
  sorry
lemma psi_continuousOn {m : ℕ} (hm : 1 ≤ m) (k : Fin df → Fin (m+1)) :
    ContinuousOn (psi m k) (Set.Icc (0 : Fin df → ℝ) 1) := by
  sorry
```

- [ ] **Step 5: Build sorry-free and commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity` and confirm no `sorry` via `lean_diagnostic_messages`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/PartitionOfUnity.lean
git commit -m "feat(runje): normalized tent partition of unity on the cube"
```

---

### Task 4: `JointTarget.lean` — the jointly monotone target `F`

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/JointTarget.lean`

**Interfaces:**
- Consumes: Mathlib (`Fin.castAdd`, `Fin.natAdd`, `Finset.sum_le_sum`, `mul_le_mul`, `abs_sum_le`/`Finset.abs_sum_le_sum_abs`, `ContinuousOn`). `variable {N dm : ℕ}`.
- Produces:
  - `zpart (w : Fin (N + dm) → ℝ) : Fin N → ℝ := fun i => w (Fin.castAdd dm i)`
  - `xpart (w : Fin (N + dm) → ℝ) : Fin dm → ℝ := fun j => w (Fin.natAdd N j)`
  - `zpart_append`, `xpart_append` : `zpart (Fin.append z x) = z`, `xpart (Fin.append z x) = x`
  - `jointTarget (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ) (w : Fin (N+dm) → ℝ) : ℝ`
  - `jointTarget_mono` : coordinatewise-monotone (`⦃a b⦄` form) on the cube, given each `g i` nonneg and monotone-on-cube-in-x
  - `jointTarget_continuousOn` : `ContinuousOn (jointTarget g C) (Set.Icc 0 1)` given each `g i` continuous on the `x`-cube
  - `jointTarget_diff_bound` : `|jointTarget g C (Fin.append z x) − jointTarget g C (Fin.append z' x)| ≤ ∑ i, |z i − z' i| * |g i x|`

- [ ] **Step 1: Write definitions and `zpart`/`xpart` computation lemmas.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Compact

/-!
# Joint monotone target for partial-monotone UAP (Runje et al.)

`jointTarget g C w = (∑ i, (z-block of w) i * g i (x-block of w)) − C`. When each `g i` is
nonnegative and monotone in `x`, this is jointly coordinatewise monotone and continuous on the
unit cube — the target approximated by the monotone network in the UAP proof.
-/

namespace UniversalApproximation.Runje

open scoped BigOperators

def zpart {N dm : ℕ} (w : Fin (N + dm) → ℝ) : Fin N → ℝ := fun i => w (Fin.castAdd dm i)
def xpart {N dm : ℕ} (w : Fin (N + dm) → ℝ) : Fin dm → ℝ := fun j => w (Fin.natAdd N j)

@[simp] lemma zpart_append {N dm} (z : Fin N → ℝ) (x : Fin dm → ℝ) :
    zpart (Fin.append z x) = z := by
  funext i; simp [zpart, Fin.append_left]

@[simp] lemma xpart_append {N dm} (z : Fin N → ℝ) (x : Fin dm → ℝ) :
    xpart (Fin.append z x) = x := by
  funext j; simp [xpart, Fin.append_right]

noncomputable def jointTarget {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (w : Fin (N + dm) → ℝ) : ℝ :=
  (∑ i, zpart w i * g i (xpart w)) - C
```

- [ ] **Step 2: Prove `jointTarget_mono`.**

```lean
lemma jointTarget_mono {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (hg_nonneg : ∀ i, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1, 0 ≤ g i x)
    (hg_mono : ∀ i, ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
      y ∈ Set.Icc (0 : Fin dm → ℝ) 1 → x ≤ y → g i x ≤ g i y) :
    ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin (N+dm) → ℝ) 1 → b ∈ Set.Icc (0 : Fin (N+dm) → ℝ) 1 →
      a ≤ b → jointTarget g C a ≤ jointTarget g C b := by
  sorry
```

Strategy: `jointTarget` is `(∑ …) − C`; `gcongr`/`sub_le_sub_right` reduces to `∑ i, zpart a i * g i (xpart a) ≤ ∑ i, zpart b i * g i (xpart b)`. Apply `Finset.sum_le_sum`; per term use `mul_le_mul`:
- `zpart a i ≤ zpart b i` (from `a ≤ b` restricted to `castAdd` coords),
- `g i (xpart a) ≤ g i (xpart b)` (`hg_mono i` with `xpart a ≤ xpart b` from `a ≤ b`, both `xpart` in cube — derive cube membership of `zpart`/`xpart` from `a,b ∈ Icc 0 1` coordinatewise),
- `0 ≤ g i (xpart a)` (`hg_nonneg`), `0 ≤ zpart b i` (from `b ∈ Icc 0 1`).
Add a private helper `zpart_mem_Icc`/`xpart_mem_Icc : w ∈ Icc 0 1 → zpart w ∈ Icc 0 1` (coordinatewise, using `Fin.castAdd`/`natAdd` evaluation).

- [ ] **Step 3: Prove `jointTarget_continuousOn`.**

```lean
lemma jointTarget_continuousOn {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (hg : ∀ i, ContinuousOn (g i) (Set.Icc (0 : Fin dm → ℝ) 1)) :
    ContinuousOn (jointTarget g C) (Set.Icc (0 : Fin (N+dm) → ℝ) 1) := by
  sorry
```

Strategy: `zpart`, `xpart` are continuous (coordinate projections; `continuous_apply` composed, and `Continuous.comp` — they map the `(N+dm)`-cube into the `N`- and `dm`-cubes; use `ContinuousOn.comp` with the mapping-into-cube fact from Step 2's helper). `jointTarget` is `finset.sum` of `zpart i * (g i ∘ xpart)` minus a constant; assemble with `ContinuousOn.sum`, `ContinuousOn.mul`, `ContinuousOn.sub`, `continuousOn_const`.

- [ ] **Step 4: Prove `jointTarget_diff_bound`.**

```lean
lemma jointTarget_diff_bound {N dm : ℕ} (g : Fin N → (Fin dm → ℝ) → ℝ) (C : ℝ)
    (z z' : Fin N → ℝ) (x : Fin dm → ℝ) :
    |jointTarget g C (Fin.append z x) - jointTarget g C (Fin.append z' x)|
      ≤ ∑ i, |z i - z' i| * |g i x| := by
  sorry
```

Strategy: `simp [jointTarget, zpart_append, xpart_append]` collapses both sides; the `−C` cancels, leaving `|∑ i, (z i − z' i) * g i x| ≤ ∑ i, |z i − z' i| * |g i x|`. Rewrite `z i * g i x − z' i * g i x = (z i − z' i) * g i x` (`sub_mul`), then `Finset.abs_sum_le_sum_abs` and `abs_mul`.

- [ ] **Step 5: Build sorry-free and commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.JointTarget`; confirm no `sorry`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/JointTarget.lean
git commit -m "feat(runje): joint monotone target F, monotonicity/continuity/diff bound"
```

---

### Task 5: `Embedding.lean` — Pi-side span and the Leshno bridge

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/Embedding.lean`

The `EuclideanSpace ℝ (Fin df)` ↔ `(Fin df → ℝ)` adaptor (spec §5.1). `genSpanPi` is defined natively on total `(Fin df → ℝ) → ℝ` functions via the explicit dot product (no `InnerProductSpace` instance on the Pi type needed); the bridge transports `DenselyApproximates` through the isometry.

**Interfaces:**
- Consumes: `genFun`, `genSpan`, `DenselyApproximates` (Leshno.Family); `leshno_dense`, `ClassM`, `IsAEPolynomial` (Leshno.Theorem, Leshno.ClassM); `EuclideanSpace.equiv`, `PiLp.inner_apply`/`EuclideanSpace.inner_eq…`, `Homeomorph`, `Submodule.map`, `Submodule.map_span`/`Submodule.mem_map`, `LinearEquiv.funCongrLeft`.
- Produces (`variable {df : ℕ}`):
  - `genFunPi (σ : ℝ → ℝ) (w : Fin df → ℝ) (b : ℝ) : (Fin df → ℝ) → ℝ := fun x => σ ((∑ c, w c * x c) + b)`
  - `genSpanPi (σ : ℝ → ℝ) (df : ℕ) : Submodule ℝ ((Fin df → ℝ) → ℝ)`
  - `leshno_bridge` : `DenselyApproximates σ → ∀ {K : Set (Fin df → ℝ)}, IsCompact K → ∀ ψ : (Fin df → ℝ) → ℝ, ContinuousOn ψ K → ∀ {η}, 0 < η → ∃ g ∈ genSpanPi σ df, ∀ u ∈ K, |ψ u − g u| < η`
  - `exists_vector_embedding` : builds a whole `Fin N → (Fin df → ℝ) → ℝ` family, each `∈ genSpanPi σ df`, approximating a given continuous-on-`K` family to accuracy `η`.

- [ ] **Step 1: Write `genFunPi` / `genSpanPi` and the isometry setup.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Leshno.Family
import NeuralNetworkProofs.UniversalApproximation.Leshno.Theorem

/-!
# Unconstrained Pi-side embedding span + Leshno bridge (Runje et al.)

`genSpanPi σ df` is the single-hidden-layer span on `(Fin df → ℝ) → ℝ`, written with the
explicit dot product so no inner-product instance on the Pi type is needed. `leshno_bridge`
transports Leshno's `DenselyApproximates` (stated on `EuclideanSpace`) to this Pi-side span.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Leshno
open scoped BigOperators RealInnerProductSpace

/-- A single Pi-side hidden unit `x ↦ σ(∑ c, w c * x c + b)`. -/
def genFunPi (σ : ℝ → ℝ) {df : ℕ} (w : Fin df → ℝ) (b : ℝ) : (Fin df → ℝ) → ℝ :=
  fun x => σ ((∑ c, w c * x c) + b)

/-- The Pi-side single-hidden-layer span, on total functions. -/
def genSpanPi (σ : ℝ → ℝ) (df : ℕ) : Submodule ℝ ((Fin df → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : (Fin df → ℝ) × ℝ => genFunPi σ wb.1 wb.2)
```

- [ ] **Step 2: Prove the generator-correspondence lemma.**

The isometry `e := EuclideanSpace.equiv (Fin df) ℝ : EuclideanSpace ℝ (Fin df) ≃L[ℝ] (Fin df → ℝ)` satisfies `⟪w, v⟫ = ∑ c, w c * (e v) c` (real Euclidean inner product = dot product). State and prove:

```lean
lemma inner_eq_dot (w v : EuclideanSpace ℝ (Fin df)) :
    (⟪w, v⟫ : ℝ) = ∑ c, w c * v c := by
  sorry  -- PiLp.inner_apply / EuclideanSpace.inner_eq; real conj is id
```

Verify the exact Mathlib lemma with `lean_leansearch "euclidean space inner product as sum"` (candidates: `EuclideanSpace.inner_eq_star_dotProduct`, `PiLp.inner_apply`).

- [ ] **Step 3: Prove `leshno_bridge`.**

```lean
theorem leshno_bridge {σ : ℝ → ℝ} (hd : DenselyApproximates σ) {df : ℕ}
    {K : Set (Fin df → ℝ)} (hK : IsCompact K) (ψ : (Fin df → ℝ) → ℝ)
    (hψ : ContinuousOn ψ K) {η : ℝ} (hη : 0 < η) :
    ∃ g ∈ genSpanPi σ df, ∀ u ∈ K, |ψ u - g u| < η := by
  sorry
```

Strategy (transport through the isometry `e`, staying on subtypes):
1. `K_e := e ⁻¹' K` is compact (`e` is a homeomorphism; `IsCompact.preimage_continuous` or `Homeomorph.isCompact_preimage`).
2. `he : ↥K_e ≃ₜ ↥K` induced by `e` (`Homeomorph.subtype`/`Set.image` correspondence, using `K_e = e⁻¹' K` and `e` bijective).
3. Package `ψ` as `ψ_e : C(↥K_e, ℝ)` via `ψ_e = (ψ restricted to K, as ContinuousMap) ∘ he` — `hψ.restrict` gives `ContinuousMap` on `↥K`, precompose with the continuous `he`.
4. Apply `hd K_e (hK_e) ψ_e hη` → `g_e ∈ genSpan σ K_e` with `∀ v, |ψ_e v − g_e v| < η`.
5. `g_e ∈ Submodule.span` of Euclidean generators. The linear equiv `Φ := LinearEquiv.funCongrLeft ℝ ℝ he.toEquiv : (↥K → ℝ) ≃ₗ (↥K_e → ℝ)` sends `genFun σ w b` (restricted to `↥K_e`) to the restriction of `genFunPi σ (e w) b` to `↥K` — check on generators via `inner_eq_dot`. Actually build the *total* witness directly: extract a `Finsupp`/finite-combination representation of `g_e` (`Submodule.mem_span_range_iff_exists_fun` or `mem_span_finset`), then define `g := ∑ t, a t • genFunPi σ (e (w t)) (b t)` as a *total* Pi function; `g ∈ genSpanPi` by `Submodule.sum_mem`/`smul_mem`/`subset_span`.
6. For `u ∈ K`, let `v := e.symm u ∈ K_e`; then `g u = g_e ⟨v, _⟩` (by `inner_eq_dot`, each generator matches: `genFunPi σ (e (w t)) (b t) u = σ(∑ (e (w t)) c * u c + b t) = σ(⟪w t, v⟫ + b t) = genFun σ (w t) (b t) ⟨v,_⟩`), and `ψ u = ψ_e ⟨v,_⟩`; the bound transfers.

**Risk flag:** Step 5's span-representation extraction is the fiddliest part. If `mem_span_range_iff_exists_fun` gives an awkward index type, fall back to `Submodule.span_induction` proving the predicate "`∃ total g' ∈ genSpanPi with g' u = g_e ⟨e.symm u,_⟩ ∀ u∈K`" is closed under `+`, `smul`, and holds on generators. If this becomes a research-grade blocker, report `NEEDS_CONTEXT` rather than weakening the theorem.

- [ ] **Step 4: Prove `exists_vector_embedding`.**

```lean
theorem exists_vector_embedding {σ : ℝ → ℝ} (hd : DenselyApproximates σ) {df N : ℕ}
    {K : Set (Fin df → ℝ)} (hK : IsCompact K) (ψ : Fin N → (Fin df → ℝ) → ℝ)
    (hψ : ∀ i, ContinuousOn (ψ i) K) {η : ℝ} (hη : 0 < η) :
    ∃ φ : Fin N → (Fin df → ℝ) → ℝ, (∀ i, φ i ∈ genSpanPi σ df) ∧
      ∀ i, ∀ u ∈ K, |ψ i u - φ i u| < η := by
  choose φ hφmem hφε using fun i => leshno_bridge hd hK (ψ i) (hψ i) hη
  exact ⟨φ, hφmem, hφε⟩
```

- [ ] **Step 5: Build sorry-free and commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.Embedding`; confirm no `sorry`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/Embedding.lean
git commit -m "feat(runje): Pi-side genSpanPi + Leshno bridge + vector embedding"
```

---

### Task 6: `Approximation.lean` — the headline theorem

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/Approximation.lean`

**Interfaces:**
- Consumes: everything from Tasks 1–5, plus `monotone_approximation` (Monotone.Approximation), and Mathlib compactness/boundedness (`IsCompact.exists_isMaxOn`, `isCompact_Icc`, `IsCompact.prod`, `UniformContinuousOn`).
- Produces: `partial_monotone_approximation` (headline, spec §5).

- [ ] **Step 1: Write the header, imports, and headline statement (proof `sorry` for now).**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Approximation
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity
import NeuralNetworkProofs.UniversalApproximation.Runje.JointTarget
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding

/-!
# Partial-monotone universal approximation (Runje et al.)

Every jointly continuous `f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ` that is coordinatewise
monotone in its second (monotone) block on the unit cube is uniformly approximated by a
`PartMonoNet`: an unconstrained single-hidden-layer Leshno embedding of the non-monotone block,
clamped and concatenated with the monotone block, fed to a monotone network.

* `partial_monotone_approximation` — the headline.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.Leshno
open scoped BigOperators

theorem partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2)
            (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1))
    (hmono : ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1,
        ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 → y ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
          x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1,
        |P.toFun u x - f u x| ≤ ε := by
  sorry
```

Note: `hmono` is written in the `⦃x y⦄` explicit-instance-binder form (matching `monotone_approximation`'s style) rather than `MonotoneOn`, so it feeds `jointTarget_mono` directly. `MonotoneOn` is definitionally this; if a caller has `MonotoneOn` they unfold via `monotoneOn_iff…`.

- [ ] **Step 2: Prove the boundedness and uniform-continuity preliminaries as `have`s.**

Inside the proof (or as `private` lemmas above it):
- `hK : IsCompact (Set.Icc (0:Fin df→ℝ) 1 ×ˢ Set.Icc (0:Fin dm→ℝ) 1)` via `(isCompact_Icc).prod isCompact_Icc`.
- Bound `C`: `∃ C, 0 < C ∧ ∀ u ∈ cube_f, ∀ x ∈ cube_m, |f u x| ≤ C − 1`. Get `M0 := sup |f|` on the compact product (`IsCompact.exists_isMaxOn` on `fun p => |f p.1 p.2|`, continuous by `hf.abs`), set `C := M0 + 1`.
- Uniform continuity: `∀ ε'>0, ∃ δ>0, ∀ u u' ∈ cube_f, ∀ x ∈ cube_m, dist u u' ≤ δ → |f u x − f u' x| ≤ ε'`. From `hK.uniformContinuousOn_of_continuous hf` + `Metric.uniformContinuousOn_iff`, applied at points `(u,x)`,`(u',x)` whose product-distance equals `dist u u'` (since the `x`-coordinates coincide; `Prod.dist_eq`/`max` with `dist x x = 0`). Model on `Monotone/Approximation.lean`'s `exists_delta_uniform`.

- [ ] **Step 3: Instantiate the grid and target, apply `monotone_approximation` and `exists_vector_embedding`.**

- Set `ε' := ε/3`. Obtain `δ` from Step 2 for `ε'`. Choose `m : ℕ` with `1 ≤ m` and `1/m < δ` (`exists_nat_one_div_lt`). Let `N := (m+1)^df` — but index `psi`/`tent` by `Fin df → Fin (m+1)` directly (a `Fintype` of card `N`); keep the sum indexed by `k : Fin df → Fin (m+1)` throughout and only convert to `Fin N` at the `MonoNet`/`PartMonoNet` boundary via `Fintype.equivFin`. **Decision:** to avoid reindexing friction, generalize `PartMonoNet.embWidth`-side sums over an arbitrary `Fintype`; since `MonoNet` needs `Fin (embWidth+dm)`, set `embWidth := Fintype.card (Fin df → Fin (m+1))` and transport `psi`/`g` through `Fintype.equivFin` once. Record the equiv `eN : (Fin df → Fin (m+1)) ≃ Fin embWidth`.
- Define `g : Fin embWidth → (Fin dm → ℝ) → ℝ := fun i x => f (tentNode m (eN.symm i)) x + C`. Each `g i` is continuous on the `x`-cube (`hf` section) and `≥ 0` on the cube (`|f| ≤ C−1 ⟹ f + C ≥ 1 ≥ 0`) and monotone in `x` (`hmono` at `u = tentNode … ∈ cube` by `tentNode_mem_Icc`).
- `F := jointTarget g C`. `jointTarget_continuousOn` + `jointTarget_mono` supply the `monotone_approximation` hypotheses. Apply it with `ε/3` → `M : MonoNet (embWidth+dm)`, `hM_mono`, `hM_depth`, `hM_approx`.
- Define `Ψ : Fin embWidth → (Fin df → ℝ) → ℝ := fun i u => psi m (eN.symm i) u`; each `ContinuousOn … cube_f` (`psi_continuousOn`). Set `η := ε / (3 * embWidth * (2*C))` (with `embWidth ≥ 1`, `C > 0`, so `η > 0`). Apply `exists_vector_embedding (leshno_dense hσ hnp) isCompact_Icc Ψ _ η` → `φ`, `hφmem`, `hφε`.

- [ ] **Step 4: Assemble `P` and prove the final bound (the three-term chain).**

- `P := { embWidth := embWidth, emb := fun u i => φ i u, mono := M }`. Then `P.mono.IsMonotone = hM_mono`; the `genSpanPi` clause is `hφmem`.
- Fix `u ∈ cube_f`, `x ∈ cube_m`. Abbreviate `z := fun i => clamp01 (φ i u)` and `zΨ := fun i => psi m (eN.symm i) u`. Show `z, zΨ ∈` the `N`-cube (`clamp01_mem_Icc`; `psi_nonneg`/`psi_le_one`), so `Fin.append z x`, `Fin.append zΨ x ∈` the `(embWidth+dm)`-cube (coordinatewise via `Fin.addCases`).
- **Term A** `|M(append z x) − F(append z x)| ≤ ε/3`: `hM_approx` at `append z x ∈` cube.
- **Term B** `|F(append z x) − F(append zΨ x)| ≤ ε/3`: `jointTarget_diff_bound` gives `≤ ∑ i, |z i − zΨ i| * |g i x|`. Bound `|g i x| ≤ 2*C` (`|f| ≤ C−1 < 2C`). Bound `|z i − zΨ i| = |clamp01(φ i u) − psi …|`; since `psi … ∈ [0,1]` (`clamp01_eq_self` on `psi`), `= |clamp01(φ i u) − clamp01(psi …)| ≤ |φ i u − psi …| < η` (`abs_clamp01_sub_le`, `hφε`). So `∑ ≤ embWidth * (η * (2*C)) = ε/3` by `η` definition.
- **Term C** `|F(append zΨ x) − f u x| ≤ ε/3`: `F(append zΨ x) = (∑ i, psi… * g i x) − C`. Substitute `g i x = f(node_i,x)+C`, distribute, use `sum_psi_eq_one` to cancel the `C·∑psi − C = 0`, leaving `∑ i, psi… * f(node_i,x)`. Also `f u x = (∑ i, psi… ) * f u x` (`sum_psi_eq_one`). So difference `= ∑ i, psi… * (f(node_i,x) − f u x)`; `|·| ≤ ∑ i, psi… * |f(node_i,x) − f u x|` (`psi_nonneg`, `Finset.abs_sum_le_sum_abs` + `abs_mul` + `abs_of_nonneg`). Per `i`: if `psi… = 0` the term is `0`; else `psi… ≠ 0 ⟹ dist(node_i,u) ≤ 1/m < δ` (`psi_support`) `⟹ |f(node_i,x) − f u x| ≤ ε/3` (Step 2 uniform continuity, `node_i, u ∈ cube_f`, `x ∈ cube_m`). So `∑ ≤ (∑ psi…)*(ε/3) = ε/3`.
- Combine `A + B + C` with `abs_sub` triangle (`|P.toFun u x − f u x| ≤ A + B + C ≤ ε`). Recall `P.toFun u x = M(append z x)` by `PartMonoNet.toFun` (with `emb u i = φ i u`).

- [ ] **Step 5: Build sorry-free and commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.Approximation`; confirm no `sorry` (`lean_diagnostic_messages`).

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/Approximation.lean
git commit -m "feat(runje): partial_monotone_approximation headline (UAP)"
```

---

### Task 7: Wire into the build + docs + verification gate

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje.lean`
- Modify: `NeuralNetworkProofs.lean`
- Modify: `README.md`
- Modify: `CLAUDE.md`
- Modify: `scripts/check_sorry_free.lean` (add the two Runje headlines)

**Interfaces:**
- Consumes: all Runje modules.
- Produces: the re-export root; the headline reachable by the default `lake build`.

- [ ] **Step 1: Write the re-export root `Runje.lean`.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.Clamp
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity
import NeuralNetworkProofs.UniversalApproximation.Runje.JointTarget
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation

/-!
# Universal Approximation for Partially Monotone Networks — root module (Runje et al.)

Formalization of partial-monotone universal approximation: a non-monotone feature block is
embedded by an unconstrained single-hidden-layer network (Leshno UAP), clamped, concatenated
with the monotone block, and fed to a monotone network (Mikulincer–Reichman / Sartor line).

* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — soundness (monotone in `x`).
* `UniversalApproximation.Runje.partial_monotone_approximation` — the UAP headline.
-/
```

- [ ] **Step 2: Add the import to `NeuralNetworkProofs.lean`.**

Add `import NeuralNetworkProofs.UniversalApproximation.Runje` after the `Monotone` import, and extend the module docstring's bullet list with:
```
* `UniversalApproximation.Runje.partial_monotone_approximation` — Runje et al., partial-monotone
  universal approximation.
* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — Runje et al., soundness.
```

- [ ] **Step 3: Add the headlines to the sorry-free gate.**

Open `scripts/check_sorry_free.lean`, confirm its pattern (it `#print axioms` / `lean_verify`s the headline names), and add `UniversalApproximation.Runje.partial_monotone_approximation` and `UniversalApproximation.Runje.PartMonoNet.monotone_snd` to the checked list, matching the existing style.

- [ ] **Step 4: Update `README.md` and the `CLAUDE.md` layout table.**

- `README.md`: add a Runje et al. bullet to the developments list (partial-monotone UAP; embed-then-concat architecture).
- `CLAUDE.md`: add a row to the layout table — `UniversalApproximation/Runje/` + `Runje.lean` | `UniversalApproximation.Runje` | the Runje et al. partial-monotone development — and add a "Runje (2026): partially monotone …" line to the "What this is" section.

- [ ] **Step 5: Full build + sorry-free gate.**

Run:
```bash
lake build
lake env lean scripts/check_sorry_free.lean
```
Expected: `lake build` green; the gate prints exactly `[propext, Classical.choice, Quot.sound]` for both new headlines and no `sorryAx` anywhere. If a from-scratch rebuild hits EMFILE, build the Runje modules serially in dependency order (Clamp → Defs → PartitionOfUnity → JointTarget → Embedding → Approximation → Runje → NeuralNetworkProofs) then rerun `lake build`.

- [ ] **Step 6: Commit.**

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje.lean NeuralNetworkProofs.lean \
  README.md CLAUDE.md scripts/check_sorry_free.lean
git commit -m "feat(runje): wire partial-monotone dev into build, docs, sorry-free gate"
```

---

## Self-Review

**Spec coverage:**
- Target class (spec §2) → Task 6 headline hypotheses (`hf`, `hmono`). ✓
- `PartMonoNet` + clamp in `toFun` (§4) → Task 2. ✓
- Soundness (§4) → Task 2 `monotone_snd`. ✓
- UAP headline with `genSpanPi` clause (§5, §5.1) → Task 6 + Task 5. ✓
- Proof error-chain (§6): partition of unity → Task 3; joint target → Task 4; embedding/Leshno → Task 5; chaining → Task 6. ✓
- File layout (§7) → Tasks 1–7 (one file each; `Clamp.lean` is the extra split, justified: reused by both Defs and Approximation). ✓
- Naming: new `UniversalApproximation.Runje` namespace, Runje et al. credited (§8) → Task 7. ✓
- Deferred follow-ups (§10) → documented in spec, not implemented (correct). ✓
- Conventions (§11) → Global Constraints. ✓

**Placeholder scan:** Proof bodies are given as explicit tactic strategies with named lemmas, not "implement later" — the honest form for Lean, where a full pre-written proof term cannot be trusted until it typechecks. Each `sorry` shown in a code block is a scaffolding marker the task's later steps discharge; **no task commits with a `sorry`** (enforced by the build + gate). No `TBD`/`TODO`.

**Type consistency:** `clamp01`, `PartMonoNet.{embWidth,emb,mono,toFun}`, `zpart`/`xpart`, `jointTarget`, `genFunPi`/`genSpanPi`, `leshno_bridge`, `exists_vector_embedding`, `tentNode`/`psi`/`psi_support`/`sum_psi_eq_one` names match across the tasks that produce and consume them. The `⦃a b⦄` monotonicity form is used consistently in `jointTarget_mono`, the headline `hmono`, and matches `monotone_approximation`. `embWidth` indexed by `Fin df → Fin (m+1)` is reconciled to `Fin embWidth` via `eN := Fintype.equivFin` at the `MonoNet` boundary (Task 6 Step 3).

**Known risk (flagged in-line):** Task 5 Step 3 span-representation transport is the fiddliest; Task 3 partition-of-unity is the heaviest. Both have concrete strategies; if either becomes research-grade, report `NEEDS_CONTEXT` rather than weaken a statement or hide a `sorry`.
