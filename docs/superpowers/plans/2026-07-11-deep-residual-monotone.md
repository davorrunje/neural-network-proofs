# Deep Residual Monotone Networks Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize, sorry-free, skip-connections for deep constrained monotone networks in
`UniversalApproximation.Runje`: the Runje–Shankaranarayana dense layer as a monotone map, an
abstract residual combinator (+ concrete `mononet` instances), any-depth soundness of a residual
stack, deep UAP by exact subsumption of the shallow depth-4 net, and the deep-core PartMonoNet
integration — **and** reframe all Runje documentation (docstrings, README, CLAUDE.md, blueprint) to
present this as the centerpiece of the development.

**Framing (see spec §1 / the `runje-development-framing` memory):** `UniversalApproximation.Runje`
is Runje et al., **"Deep Constrained Monotonic Neural Networks"** (forthcoming), extending
Runje–Shankaranarayana 2023. This deep-skip work is the paper's **main** result (soundness + UAP);
partial monotonicity is *secondary*. Existing docs mis-cast Runje as "the partial-monotone
development" — correcting that is part of this PR (Tasks 5–6).

**Architecture:** Reuse the existing monotone abstraction (`Monotone.Layer`/`ActStack`/`MonoNet`,
`Sartor.reflect`, `MikulincerReichman.monotone_approximation`, `Runje.partial_monotone_approximation`).
The residual block is a positive-scalar-gated sum of monotone maps; a deep stack composes them
(soundness); UAP is inherited because a `MonoNet` embeds denotationally as a single-block
`DeepMonoNet`.

**Tech Stack:** Lean 4, Mathlib, Lake 5.0.0. LSP tools (`lean_goal`, `lean_leansearch`,
`lean_loogle`, `lean_multi_attempt`, `lean_diagnostic_messages`) for proof development.

**Spec:** `docs/superpowers/specs/2026-07-11-deep-residual-monotone-design.md`.

**Note (file-layout refinement of spec §4):** the spec's `Runje/Residual.lean` is split into
`Runje/Residual.lean` (combinator + instances + `ResBlock`/`ResNet` + soundness) and
`Runje/DeepMono.lean` (`DeepMonoNet` + `MonoNet.toDeep` + deep UAP), for focused files. Benign
organizational refinement; no design change.

## Global Constraints

- **No `sorry`/`admit`.** Every commit sorry-free; a clean headline reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- **No changes to existing developments** (Monotone/MikulincerReichman/Sartor/Runje existing files)
  beyond the Task 5 wiring (re-export, aggregator, docstring, gate).
- **Line length ≤ 100 codepoints** (measure codepoints:
  `python3 -c "import sys; print(max(len(l.rstrip(chr(10))) for l in open(sys.argv[1])))" <file>`).
- **Minimal, precise imports** — no blanket `import Mathlib` (except `import Mathlib.Tactic` where a
  headline proof needs broad tactics, matching sibling files). Clean build is the gate.
- **File header** (each file): Apache-2.0 block + `Authors: Davor Runje` + a `/-! … -/` module doc.
- **Namespace** `UniversalApproximation.Runje`; module prefix
  `NeuralNetworkProofs.UniversalApproximation.Runje.<File>`.
- **Build a module:** `lake build NeuralNetworkProofs.UniversalApproximation.Runje.<File>`. If a
  from-scratch rebuild hits `Too many open files` (EMFILE), build serially per module.
- **Sorry-free gate:** `lake env lean scripts/check_sorry_free.lean`.

## Reused external signatures (verbatim, post-unification)

```lean
-- NeuralNetwork/Network.lean
structure Layer (a b : ℕ) where W : Matrix (Fin b) (Fin a) ℝ ; c : Fin b → ℝ
def Layer.toFun (σ : ℝ → ℝ) {a b} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ
  -- = fun i => σ ((L.W.mulVec x) i + L.c i)

-- Monotone/Defs.lean  (namespace UniversalApproximation.Monotone)
theorem layer_toFun_monotone {a b} (L : NeuralNetwork.Layer a b) {σ : ℝ → ℝ}
    (hσ : Monotone σ) (hW : ∀ i j, 0 ≤ L.W i j) : Monotone (L.toFun σ)
noncomputable def ActStack.toFun : {a b : ℕ} → ActStack a b → (Fin a → ℝ) → (Fin b → ℝ)
theorem ActStack.monotone_toFun {a b} (S : ActStack a b) (h : S.IsMonotone) : Monotone S.toFun
structure MonoNet (d : ℕ) where
  width : ℕ ; stack : ActStack d width ; readW : Fin width → ℝ ; readBias : ℝ
noncomputable def MonoNet.toFun {d} (N : MonoNet d) (x) : ℝ :=
  (∑ i, N.readW i * N.stack.toFun x i) + N.readBias
def MonoNet.IsMonotone {d} (N : MonoNet d) : Prop := N.stack.IsMonotone ∧ ∀ i, 0 ≤ N.readW i

-- Sartor/Saturating.lean  (namespace UniversalApproximation.Sartor)
def RightSaturating (σ : ℝ → ℝ) : Prop  -- ∃ L, Tendsto σ atTop (nhds L)
def LeftSaturating (σ : ℝ → ℝ) : Prop   -- ∃ L, Tendsto σ atBot (nhds L)
def reflect (σ : ℝ → ℝ) : ℝ → ℝ := fun x => -σ (-x)
theorem reflect_monotone {σ} (hσ : Monotone σ) : Monotone (reflect σ)
theorem reflect_rightSaturating {σ} (h : LeftSaturating σ) : RightSaturating (reflect σ)

-- MikulincerReichman/Approximation.lean
theorem monotone_approximation {d} (f : (Fin d → ℝ) → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0:Fin d→ℝ) 1 → b ∈ Set.Icc (0:Fin d→ℝ) 1 → a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧ ∀ x ∈ Set.Icc (0:Fin d→ℝ) 1, |N.toFun x - f x| ≤ ε

-- Runje/Clamp.lean, Runje/Defs.lean, Runje/Embedding.lean, Runje/Approximation.lean
def clamp01 (t : ℝ) : ℝ
def genSpanPi (σ : ℝ → ℝ) (df : ℕ) : Submodule ℝ ((Fin df → ℝ) → ℝ)
theorem partial_monotone_approximation {df dm} (σ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f) (hf …) (hmono …) {ε} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0:Fin df→ℝ) 1, ∀ x ∈ Set.Icc (0:Fin dm→ℝ) 1, |P.toFun u x - f u x| ≤ ε
```

---

### Task 1: `RunjeShankaranarayana.lean` — R–S dense layer is monotone

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/RunjeShankaranarayana.lean`

**Interfaces:**
- Consumes: `Monotone.layer_toFun_monotone`, `NeuralNetwork.Layer`; `Sartor.reflect`,
  `reflect_monotone`, `LeftSaturating`, `reflect_rightSaturating`; Mathlib (`Real.exp`, `Real.log`,
  `Matrix.map`, `Fin.append`, `Fin.addCases`).
- Produces: `rsDense`, `rsDense_monotone`, `elu`, `elu_monotone`, `elu_leftSaturating`,
  `softplus`, `softplus_monotone`, `softplus_leftSaturating`.

- [ ] **Step 1: Write the file skeleton + `rsDense`.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Runje–Shankaranarayana dense layer is monotone (Runje et al.)

The `mononet` "absolute-mode" dense layer (Runje–Shankaranarayana 2023): nonnegative effective
weights `|W|`, convex neurons using base activation `ρ`, concave neurons using `Sartor.reflect ρ`.
Modeled as the `Fin.append` of two single-activation monotone sublayers, hence a monotone map — an
instance of the shared monotone abstraction. Its base activations (`elu`, `softplus`) are monotone
and one-sided-saturating, so their reflections meet the Sartor UAP hypotheses.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.Sartor

/-- R–S absolute-mode dense map: convex block (`ρ`, weights `|Wc|`) on the first `c` outputs,
concave block (`reflect ρ`, weights `|Wk|`) on the rest, appended. -/
noncomputable def rsDense {a c k : ℕ} (ρ : ℝ → ℝ)
    (Wc : Matrix (Fin c) (Fin a) ℝ) (bc : Fin c → ℝ)
    (Wk : Matrix (Fin k) (Fin a) ℝ) (bk : Fin k → ℝ) : (Fin a → ℝ) → (Fin (c + k) → ℝ) :=
  fun x => Fin.append
    (({ W := Wc.map (fun t => |t|), c := bc } : NeuralNetwork.Layer a c).toFun ρ x)
    (({ W := Wk.map (fun t => |t|), c := bk } : NeuralNetwork.Layer a k).toFun (reflect ρ) x)
```

- [ ] **Step 2: Prove `rsDense_monotone`.**

```lean
theorem rsDense_monotone {a c k : ℕ} {ρ : ℝ → ℝ} (hρ : Monotone ρ)
    (Wc : Matrix (Fin c) (Fin a) ℝ) (bc : Fin c → ℝ)
    (Wk : Matrix (Fin k) (Fin a) ℝ) (bk : Fin k → ℝ) :
    Monotone (rsDense ρ Wc bc Wk bk) := by
  sorry
```

Strategy: let `hconv : Monotone (({W := Wc.map (|·|), c := bc}).toFun ρ)` from
`layer_toFun_monotone` with `hW := fun i j => abs_nonneg _` (since `(Wc.map (|·|)) i j = |Wc i j|`,
use `Matrix.map_apply`); `hconc` similarly with `reflect_monotone hρ`. Then `intro x y hxy i`;
`refine Fin.addCases (fun i => ?_) (fun j => ?_) i`; on `Fin.append_left` use `hconv hxy i`, on
`Fin.append_right` use `hconc hxy j` (mirror `PartMonoNet.monotone_snd`'s `Fin.addCases` pattern,
but here both branches are genuine `≤`, not `le_rfl`). Confirm `Matrix.map_apply` name via
`lean_loogle`.

- [ ] **Step 3: Define + prove the concrete activations.**

```lean
/-- Exponential linear unit. -/
noncomputable def elu (x : ℝ) : ℝ := if 0 < x then x else Real.exp x - 1
/-- Softplus. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem elu_monotone : Monotone elu := by sorry
theorem elu_leftSaturating : LeftSaturating elu := by sorry          -- limit -1 at atBot
theorem softplus_monotone : Monotone softplus := by sorry
theorem softplus_leftSaturating : LeftSaturating softplus := by sorry -- limit 0 at atBot
```

Strategy:
- `elu_monotone`: `intro x y hxy`; case on `0 < x`/`0 < y` (`rcases`/`split_ifs`); the four cases use
  `hxy`, `Real.exp_le_exp.mpr hxy`, and continuity at 0 (`Real.exp` value `exp 0 - 1 = 0 ≤ y` when
  `0 < y`, `x ≤ 0`). Use `Real.add_one_le_exp` / `Real.exp_le_exp`; validate names with
  `lean_leansearch "exp monotone"`.
- `elu_leftSaturating`: `refine ⟨-1, ?_⟩`; `Tendsto elu atBot (nhds (-1))`. Since `elu` eventually
  (`x < 0`) equals `Real.exp x - 1`, use `Tendsto.congr'` with `eventually_atBot` and
  `Real.tendsto_exp_atBot` (`exp → 0`) then `.sub_const 1` giving `0 - 1 = -1`.
- `softplus_monotone`: `Real.log` is monotone on `(0,∞)` and `1 + exp x > 0`; compose
  `Real.exp_le_exp`, `add_le_add_left`, `Real.log_le_log` (with positivity). Search
  `Real.log_le_log` signature via `lean_leansearch`.
- `softplus_leftSaturating`: `refine ⟨0, ?_⟩`; `1 + exp x → 1` at atBot (`Real.tendsto_exp_atBot`,
  `const_add`), then `Real.continuous_log.continuousAt`/`Real.log_one` gives `log → log 1 = 0`
  (`Tendsto.comp` / `Real.tendsto_log_...`).

- [ ] **Step 4: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.RunjeShankaranarayana`;
confirm no `sorry` via `lean_diagnostic_messages`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/RunjeShankaranarayana.lean
git commit -m "feat(runje): R–S dense layer is monotone (convex/concave sublayer split)"
```

---

### Task 2: `Residual.lean` — residual combinator + deep stack soundness

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/Residual.lean`

**Interfaces:**
- Consumes: Mathlib only (`Matrix.mulVec`, `Monotone`, `Monotone.comp`, `monotone_const`,
  `monotone_id`, `Real.exp`, `dotProduct_le_dotProduct_of_nonneg_left`, `Finset.sum_le_sum`).
- Produces: `residual`, `residual_monotone`; `shiftedElu`, `shiftedElu_pos`, `scaledElu`,
  `scaledElu_pos`, `expSkip`, `expSkip_monotone`; `ResBlock` (fields `gα gβ skip F`),
  `ResBlock.IsMonotone`, `ResBlock.toFun`, `ResBlock.monotone_toFun`; `ResNet` (`nil`/`cons`),
  `ResNet.toFun`, `ResNet.IsMonotone`, `ResNet.monotone_toFun`.

- [ ] **Step 1: Write the combinator + its monotonicity.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Residual monotone blocks and deep stacks (Runje et al.)

A residual block `x ↦ g_α · skip(x) + g_β · F(x)` with nonnegative scalar gates and monotone
`skip`, `F` is monotone; a `ResNet` (composition of such blocks, any depth) is monotone. The
`mononet` gates (`shiftedElu`, `scaledElu`) are strictly positive and the `exp`-projected skip is
monotone, so the concrete block satisfies the hypotheses.
-/

namespace UniversalApproximation.Runje

/-- Residual block map: positive-gated sum of a skip and a sublayer `F`. -/
def residual {a b : ℕ} (gα gβ : ℝ) (skip F : (Fin a → ℝ) → (Fin b → ℝ)) :
    (Fin a → ℝ) → (Fin b → ℝ) := fun x i => gα * skip x i + gβ * F x i

theorem residual_monotone {a b : ℕ} {gα gβ : ℝ} {skip F : (Fin a → ℝ) → (Fin b → ℝ)}
    (hgα : 0 ≤ gα) (hgβ : 0 ≤ gβ) (hskip : Monotone skip) (hF : Monotone F) :
    Monotone (residual gα gβ skip F) := by
  intro x y hxy i
  have h1 := hskip hxy i
  have h2 := hF hxy i
  simp only [residual]
  gcongr
```

(If `gcongr` needs the nonneg side-goals discharged explicitly, supply `hgα`, `hgβ`, `h1`, `h2`.)

- [ ] **Step 2: Concrete `mononet` gate/skip instances.**

```lean
open scoped Real

noncomputable def shiftedElu (r : ℝ) : ℝ := (if 0 < r then r else Real.exp r - 1) + 1
noncomputable def scaledElu (ε r : ℝ) : ℝ := max r 0 + ε * Real.exp (min r 0 / ε)
noncomputable def expSkip {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) := fun x => (W.map Real.exp).mulVec x

theorem shiftedElu_pos (r : ℝ) : 0 < shiftedElu r := by sorry
theorem scaledElu_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 < scaledElu ε r := by sorry
theorem expSkip_monotone {a b : ℕ} (W : Matrix (Fin b) (Fin a) ℝ) : Monotone (expSkip W) := by sorry
```

Strategy:
- `shiftedElu_pos`: `split_ifs`; if `0 < r` then `r + 1 > 0` by `linarith`; else `exp r - 1 + 1 =
  exp r > 0` by `Real.exp_pos`.
- `scaledElu_pos`: `max r 0 ≥ 0` (`le_max_right`), `ε * exp(..) > 0` (`mul_pos hε (Real.exp_pos _)`);
  sum of `≥0` and `>0` is `>0` (`add_pos_of_nonneg_of_pos`).
- `expSkip_monotone`: `intro x y hxy i`; `expSkip W _ i = (W.map exp).mulVec _ i = ∑ j, exp(W i j) *
  _ j` (`Matrix.mulVec`, `Matrix.map_apply`); apply `dotProduct_le_dotProduct_of_nonneg_left hxy
  (fun j => (Real.exp_pos _).le)` (the lemma used in `layer_toFun_monotone`), or `Finset.sum_le_sum`
  with `mul_le_mul_of_nonneg_left (hxy j) (Real.exp_pos _).le`.

- [ ] **Step 3: `ResBlock` + monotonicity.**

```lean
/-- A residual block: gates and the skip/sublayer maps. -/
structure ResBlock (a b : ℕ) where
  gα : ℝ
  gβ : ℝ
  skip : (Fin a → ℝ) → (Fin b → ℝ)
  F : (Fin a → ℝ) → (Fin b → ℝ)

def ResBlock.IsMonotone {a b} (B : ResBlock a b) : Prop :=
  0 ≤ B.gα ∧ 0 ≤ B.gβ ∧ Monotone B.skip ∧ Monotone B.F

def ResBlock.toFun {a b} (B : ResBlock a b) : (Fin a → ℝ) → (Fin b → ℝ) :=
  residual B.gα B.gβ B.skip B.F

theorem ResBlock.monotone_toFun {a b} (B : ResBlock a b) (h : B.IsMonotone) :
    Monotone B.toFun :=
  residual_monotone h.1 h.2.1 h.2.2.1 h.2.2.2
```

- [ ] **Step 4: `ResNet` + any-depth soundness.**

```lean
/-- A deep residual network: a chain of residual blocks from arity `a` to `c`. -/
inductive ResNet : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ResNet a a
  | cons : {a b c : ℕ} → ResBlock a b → ResNet b c → ResNet a c

def ResNet.toFun : {a c : ℕ} → ResNet a c → (Fin a → ℝ) → (Fin c → ℝ)
  | _, _, .nil, x => x
  | _, _, .cons B rest, x => rest.toFun (B.toFun x)

def ResNet.IsMonotone : {a c : ℕ} → ResNet a c → Prop
  | _, _, .nil => True
  | _, _, .cons B rest => B.IsMonotone ∧ rest.IsMonotone

/-- **Soundness: a residual stack of any depth is monotone.** -/
theorem ResNet.monotone_toFun : {a c : ℕ} → (N : ResNet a c) → N.IsMonotone → Monotone N.toFun
  | _, _, .nil, _ => monotone_id
  | _, _, .cons B rest, h => (rest.monotone_toFun h.2).comp (B.monotone_toFun h.1)
```

(`ResNet.toFun (.cons B rest) x = rest.toFun (B.toFun x) = (rest.toFun ∘ B.toFun) x`, so the
`Monotone.comp` gives monotonicity; adjust with `by intro …; simpa [ResNet.toFun] using …` if the
definitional unfolding needs a nudge.)

- [ ] **Step 5: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.Residual`; confirm no `sorry`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/Residual.lean
git commit -m "feat(runje): residual combinator + concrete instances + ResNet soundness"
```

---

### Task 3: `DeepMono.lean` — `DeepMonoNet` + deep UAP by subsumption

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/DeepMono.lean`

**Interfaces:**
- Consumes: Task 2 (`ResBlock`, `ResNet`, `ResNet.monotone_toFun`, `residual`); `Monotone.MonoNet`,
  `MonoNet.toFun`, `MonoNet.IsMonotone`, `ActStack.monotone_toFun`;
  `MikulincerReichman.monotone_approximation`; Mathlib (`monotone_const`, `Finset.sum_congr`).
- Produces: `DeepMonoNet` (fields `width net readW readBias`), `DeepMonoNet.toFun`,
  `DeepMonoNet.IsMonotone`, `DeepMonoNet.monotone_toFun`, `MonoNet.toDeep`, `MonoNet.toDeep_toFun`,
  `MonoNet.toDeep_isMonotone`, `MonoNet.toDeep_single_block`, `deep_monotone_approximation`.

- [ ] **Step 1: `DeepMonoNet` + monotonicity.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.Residual
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Approximation

/-!
# Deep monotone networks + UAP by subsumption (Runje et al.)

A `DeepMonoNet` is a `ResNet` (deep residual body) plus a nonnegative-weight scalar read-out. It is
monotone (soundness). A shallow `MonoNet` embeds as a single-block `DeepMonoNet` preserving the
denotation exactly, so the depth-4 monotone UAP lifts verbatim: deep-residual monotone nets retain
universality, and no depth beyond 4 is required.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.MikulincerReichman

structure DeepMonoNet (d : ℕ) where
  width : ℕ
  net : ResNet d width
  readW : Fin width → ℝ
  readBias : ℝ

noncomputable def DeepMonoNet.toFun {d} (D : DeepMonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, D.readW i * D.net.toFun x i) + D.readBias

def DeepMonoNet.IsMonotone {d} (D : DeepMonoNet d) : Prop :=
  D.net.IsMonotone ∧ ∀ i, 0 ≤ D.readW i

theorem DeepMonoNet.monotone_toFun {d} (D : DeepMonoNet d) (h : D.IsMonotone) :
    Monotone D.toFun := by
  intro x y hxy
  have hnet : Monotone D.net.toFun := D.net.monotone_toFun h.1
  simp only [DeepMonoNet.toFun]
  gcongr with i _
  · exact h.2 i
  · exact hnet hxy i
```

(Mirror `MonoNet.monotone_toFun`; if `gcongr` needs the sum shape, use `by gcongr with i` and
supply `h.2 i` / `hnet hxy i`.)

- [ ] **Step 2: `MonoNet.toDeep` + exact denotation.**

```lean
/-- Embed a `MonoNet` as a single-block `DeepMonoNet`: one block with `gα = 0, gβ = 1`,
`skip = 0`, `F = the stack's monotone map`; the block computes the stack exactly. -/
noncomputable def MonoNet.toDeep {d} (N : MonoNet d) : DeepMonoNet d where
  width := N.width
  net := ResNet.cons { gα := 0, gβ := 1, skip := fun _ => 0, F := N.stack.toFun } ResNet.nil
  readW := N.readW
  readBias := N.readBias

theorem MonoNet.toDeep_toFun {d} (N : MonoNet d) : N.toDeep.toFun = N.toFun := by
  funext x
  simp only [MonoNet.toDeep, DeepMonoNet.toFun, MonoNet.toFun, ResNet.toFun, ResBlock.toFun,
    residual, Pi.zero_apply, mul_zero, zero_mul, zero_add, one_mul]

theorem MonoNet.toDeep_single_block {d} (N : MonoNet d) :
    ∃ B : ResBlock d N.width, N.toDeep.net = ResNet.cons B ResNet.nil :=
  ⟨_, rfl⟩
```

(If `simp` doesn't fully close `toDeep_toFun`, inspect the residual reduction with `lean_goal`:
the block's `toFun x i = 0 * 0 + 1 * N.stack.toFun x i`, which `simp` reduces to
`N.stack.toFun x i`; then both sides are the same read-out sum.)

- [ ] **Step 3: `MonoNet.toDeep_isMonotone`.**

```lean
theorem MonoNet.toDeep_isMonotone {d} (N : MonoNet d) (h : N.IsMonotone) :
    N.toDeep.IsMonotone := by
  refine ⟨⟨⟨le_refl 0, zero_le_one, monotone_const, N.stack.monotone_toFun h.1⟩, trivial⟩, ?_⟩
  · exact h.2
```

(The `net.IsMonotone` for a `cons _ nil` is `ResBlock.IsMonotone ∧ True`; the block's `IsMonotone`
is `0 ≤ 0 ∧ 0 ≤ 1 ∧ Monotone (fun _ => 0) ∧ Monotone N.stack.toFun`. Confirm the exact tuple
nesting with `lean_goal` and adjust the anonymous constructor.)

- [ ] **Step 4: `deep_monotone_approximation`.**

```lean
/-- **Deep UAP (retains UAP).** Every continuous, coordinatewise-monotone `f` on the unit cube is
uniformly `ε`-approximated by a monotone `DeepMonoNet`. The witness is a single residual block over
the existing depth-4 core (`MonoNet.toDeep_single_block`), so no depth beyond 4 is required. -/
theorem deep_monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : DeepMonoNet d, D.IsMonotone ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |D.toFun x - f x| ≤ ε := by
  obtain ⟨N, hNmono, _hdepth, hNapprox⟩ := monotone_approximation f hf hmono hε
  refine ⟨N.toDeep, N.toDeep_isMonotone hNmono, ?_⟩
  intro x hx
  rw [MonoNet.toDeep_toFun]
  exact hNapprox x hx
```

- [ ] **Step 5: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.DeepMono`; confirm no `sorry`;
axiom-check `deep_monotone_approximation` via `lean_verify`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/DeepMono.lean
git commit -m "feat(runje): DeepMonoNet + deep UAP by exact MonoNet subsumption"
```

---

### Task 4: `DeepPartMono.lean` — deep-core partial-monotone soundness + UAP

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/DeepPartMono.lean`

**Interfaces:**
- Consumes: Task 3 (`DeepMonoNet`, `DeepMonoNet.monotone_toFun`, `MonoNet.toDeep`,
  `toDeep_toFun`, `toDeep_isMonotone`); `Runje.clamp01`, `clamp01_mem_Icc`;
  `Runje.partial_monotone_approximation`, `Runje.genSpanPi`, `PartMonoNet`;
  `Monotone.ClassM`/`IsAEPolynomial` (via Leshno, re-exported); `Fin.append`, `Fin.addCases`.
- Produces: `DeepPartMonoNet` (fields `embWidth emb mono`), `DeepPartMonoNet.toFun`,
  `DeepPartMonoNet.monotone_snd`, `deep_partial_monotone_approximation`.

- [ ] **Step 1: Structure + `toFun` + soundness.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepMono
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation

/-!
# Deep-core partial-monotone networks (Runje et al.)

`DeepPartMonoNet` swaps the monotone core of `PartMonoNet` for a deep-residual `DeepMonoNet`.
Soundness (monotone in the monotone block) mirrors `PartMonoNet.monotone_snd`; partial-monotone UAP
is inherited from `partial_monotone_approximation` by embedding its `MonoNet` core via
`MonoNet.toDeep`.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Leshno

structure DeepPartMonoNet (df dm : ℕ) where
  embWidth : ℕ
  emb : (Fin df → ℝ) → (Fin embWidth → ℝ)
  mono : DeepMonoNet (embWidth + dm)

noncomputable def DeepPartMonoNet.toFun {df dm} (P : DeepPartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)

theorem DeepPartMonoNet.monotone_snd {df dm} (P : DeepPartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u) := by
  intro x y hxy
  refine P.mono.monotone_toFun h ?_
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]
  · simpa only [Fin.append_right] using hxy j
```

(This is `PartMonoNet.monotone_snd` verbatim with `DeepMonoNet.monotone_toFun` in place of
`MonoNet.monotone_toFun`; the left branch may need `exact le_rfl` after the `simp only`.)

- [ ] **Step 2: `deep_partial_monotone_approximation`.**

```lean
theorem deep_partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2)
            (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1))
    (hmono : ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1,
        ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 → y ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
          x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : DeepPartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1,
        |P.toFun u x - f u x| ≤ ε := by
  obtain ⟨P₀, hmono0, hemb, hbound⟩ :=
    partial_monotone_approximation σ hσ hnp f hf hmono hε
  refine ⟨⟨P₀.embWidth, P₀.emb, P₀.mono.toDeep⟩,
    P₀.mono.toDeep_isMonotone hmono0, hemb, ?_⟩
  intro u hu x hx
  have hEq : (⟨P₀.embWidth, P₀.emb, P₀.mono.toDeep⟩ : DeepPartMonoNet df dm).toFun u x
      = P₀.toFun u x := by
    simp only [DeepPartMonoNet.toFun, PartMonoNet.toFun, MonoNet.toDeep_toFun]
  rw [hEq]
  exact hbound u hu x hx
```

(Key step: `DeepPartMonoNet.toFun` unfolds to `(P₀.mono.toDeep).toFun (Fin.append …)` and
`PartMonoNet.toFun` to `P₀.mono.toFun (Fin.append …)`; `MonoNet.toDeep_toFun` rewrites the former's
head to the latter — the `Fin.append` argument is identical since `emb` is shared. Confirm
`PartMonoNet.toFun`'s exact unfolding with `lean_hover_info`; adjust the `simp` set if needed.)

- [ ] **Step 3: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.DeepPartMono`; confirm no `sorry`;
axiom-check both headlines via `lean_verify`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/DeepPartMono.lean
git commit -m "feat(runje): DeepPartMonoNet soundness + deep-core partial-monotone UAP"
```

---

### Task 5: Wire in + reframe prose documentation

Reframe every prose description of the Runje development to lead with **deep constrained monotone
networks via skip connections** (soundness + UAP), with partial monotonicity as *secondary* — the
existing docs mis-cast Runje as "the partial-monotone development." (The leanblueprint chapter is
Task 6.)

**Files:**
- Modify: `NeuralNetworkProofs/UniversalApproximation/Runje.lean` (imports + reframed docstring)
- Modify: `NeuralNetworkProofs/UniversalApproximation.lean` (aggregator docstring: reframe + bullets)
- Modify: `NeuralNetworkProofs.lean` (root docstring: reframe + bullets)
- Modify: `scripts/check_sorry_free.lean`
- Modify: `README.md` (reframe the Runje developments entry)
- Modify: `CLAUDE.md` ("What this is" Runje bullet + layout-table description)
- Modify (docstrings only, no proof changes): `Runje/Clamp.lean`, `Runje/Defs.lean`,
  `Runje/Approximation.lean`, `Runje/Embedding.lean`, `Runje/PartitionOfUnity.lean`,
  `Runje/JointTarget.lean` — wherever the module doc calls the development "partial-monotone" as if
  it were the headline, reframe (partial monotonicity is one part of the deep-constrained-monotonic
  development).

**Interfaces:**
- Consumes: all four new Runje modules (Tasks 1–4).
- Produces: the new headlines reachable by the default `lake build` and checked by the gate; a
  consistent "Deep Constrained Monotonic Neural Networks" framing across all Runje prose.

**Reframing wording (reuse consistently):** *"`UniversalApproximation.Runje` — Runje et al., Deep
Constrained Monotonic Neural Networks (forthcoming; extends Runje–Shankaranarayana 2023). Skip
connections make deep constrained monotone networks trainable; formalized soundness (monotone at
any depth) + UAP. Includes partial monotonicity as a secondary result."*

- [ ] **Step 1: Extend the Runje re-export root.**

In `NeuralNetworkProofs/UniversalApproximation/Runje.lean`, add after the existing imports:

```lean
import NeuralNetworkProofs.UniversalApproximation.Runje.RunjeShankaranarayana
import NeuralNetworkProofs.UniversalApproximation.Runje.Residual
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepMono
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepPartMono
```

Extend its module docstring's headline list with:
```
* `UniversalApproximation.Runje.rsDense_monotone` — R–S dense layer is monotone.
* `UniversalApproximation.Runje.ResNet.monotone_toFun` — deep residual stack is monotone (soundness).
* `UniversalApproximation.Runje.deep_monotone_approximation` — deep monotone UAP (retains UAP).
* `UniversalApproximation.Runje.DeepPartMonoNet.monotone_snd` — deep-core partial-monotone soundness.
* `UniversalApproximation.Runje.deep_partial_monotone_approximation` — deep-core partial UAP.
```

- [ ] **Step 2: Reframe + extend the aggregator + top root docstrings.**

In `NeuralNetworkProofs/UniversalApproximation.lean` and `NeuralNetworkProofs.lean`, (a) reframe the
Runje entry to the "Deep Constrained Monotonic Neural Networks" wording above, and (b) add the five
new headline bullets to the Runje section, listing the deep-monotone headlines
(`deep_monotone_approximation`, `ResNet.monotone_toFun`, `rsDense_monotone`) *first* and
`partial_monotone_approximation` / `PartMonoNet.monotone_snd` as secondary. No import changes needed
(they already import `…Runje` / the aggregator transitively).

- [ ] **Step 3: Extend the sorry-free gate.**

In `scripts/check_sorry_free.lean` (which already `open`s `UniversalApproximation.Runje`), append:

```lean
#print axioms rsDense_monotone
#print axioms ResNet.monotone_toFun
#print axioms deep_monotone_approximation
#print axioms DeepPartMonoNet.monotone_snd
#print axioms deep_partial_monotone_approximation
```

- [ ] **Step 4: Reframe `README.md`, `CLAUDE.md`, and existing Runje docstrings.**

Read each file first; edit prose only; do not churn unrelated lines.
- `README.md`: change the Runje developments entry from a partial-monotone headline to the
  reframing wording (deep constrained monotone networks via skip connections; soundness + UAP;
  partial monotonicity secondary).
- `CLAUDE.md`: update the Runje bullet in "What this is" and the `Runje/` layout-table description
  to the same framing.
- Existing Runje module docstrings (`Runje/Clamp.lean`, `Defs.lean`, `Approximation.lean`,
  `Embedding.lean`, `PartitionOfUnity.lean`, `JointTarget.lean`): where a module doc frames the
  development as "partial-monotone" as if that were the headline, adjust so partial monotonicity
  reads as one part of the deep-constrained-monotonic development. **Docstrings/comments only — no
  code, statement, or proof changes** (the sorry-free axioms must be unchanged).

- [ ] **Step 5: Full build + gate + commit.**

Run:
```bash
lake build
lake env lean scripts/check_sorry_free.lean
```
Expected: `lake build` green; the gate prints the five new headlines with exactly
`[propext, Classical.choice, Quot.sound]` and no `sorryAx` anywhere. If a from-scratch rebuild hits
EMFILE, build the new Runje modules serially (RunjeShankaranarayana → Residual → DeepMono →
DeepPartMono → Runje → UniversalApproximation → NeuralNetworkProofs) then rerun `lake build`.

```bash
git add -A
git commit -m "feat(runje): wire deep-residual headlines + reframe Runje as deep constrained monotone nets"
```

---

### Task 6: Reframe + extend the leanblueprint Runje chapter

**Files:**
- Modify: `blueprint/src/chapter/runje.tex`

**Interfaces:**
- Consumes: the renamed/added Runje declarations (Tasks 1–4) for `\lean{}` refs.
- Produces: a Runje chapter that leads with the deep-constrained-monotone results and passes
  `checkdecls`.

- [ ] **Step 1: Reframe the chapter + add the deep-residual nodes.**

Rewrite `blueprint/src/chapter/runje.tex` so it presents the development as **"Deep Constrained
Monotonic Neural Networks"** (extends R–S 2023; skip connections → trainable deep monotone nets;
soundness + UAP), with the existing partial-monotone material as a *secondary* section. Add
environments (each `\lean{}` verified in Step 2) for the new results, e.g.:

```tex
\chapter{Deep constrained monotonic networks --- Runje et al.}

\section{Constrained monotone dense layers}
\begin{lemma}[R--S dense layer is monotone]\label{lem:rs-dense}
  \lean{UniversalApproximation.Runje.rsDense_monotone}\leanok
  \uses{def:mononet}
  The Runje--Shankaranarayana absolute-mode dense layer (nonneg weights $|W|$, convex neurons with
  $\rho$ and concave neurons with $\mathrm{reflect}\,\rho$) is monotone.
\end{lemma}

\section{Skip connections and deep monotone networks}
\begin{definition}[Residual block]\label{def:residual}
  \lean{UniversalApproximation.Runje.residual}\leanok
  $x \mapsto g_\alpha\,\mathrm{skip}(x) + g_\beta\,F(x)$, gates $g_\alpha,g_\beta \ge 0$.
\end{definition}
\begin{theorem}[Deep soundness: any-depth residual stack is monotone]\label{thm:resnet-mono}
  \lean{UniversalApproximation.Runje.ResNet.monotone_toFun}\leanok
  \uses{def:residual}
  A composition of monotone residual blocks (a \texttt{ResNet}) of any depth is monotone.
\end{theorem}
\begin{theorem}[Deep monotone UAP (retains UAP)]\label{thm:deep-mono-uap}
  \lean{UniversalApproximation.Runje.deep_monotone_approximation}\leanok
  \uses{thm:resnet-mono, thm:mono-approx}
  Every continuous monotone $f$ on the cube is uniformly $\varepsilon$-approximated by a monotone
  \texttt{DeepMonoNet}; the witness is a single residual block over the depth-4 core, so no depth
  beyond 4 is needed to retain UAP.
\end{theorem}

\section{Partial monotonicity (secondary)}
% keep the existing partial-monotone definitions/theorems here, re-titled as a secondary section:
% def:genspanpi, def:partmononet, thm:runje-sound, lem:leshno-bridge, thm:runje-uap,
% plus the deep-core variant:
\begin{theorem}[Deep-core partial-monotone UAP]\label{thm:deep-part-uap}
  \lean{UniversalApproximation.Runje.deep_partial_monotone_approximation}\leanok
  \uses{thm:deep-mono-uap, def:partmononet}
  The partial-monotone architecture with a deep-residual monotone core retains partial UAP.
\end{theorem}
```

Preserve the existing partial-monotone environments (`def:genspanpi`, `def:partmononet`,
`thm:runje-sound`, `lem:leshno-bridge`, `thm:runje-uap`) — just move them under the "secondary"
section and keep their `\lean`/`\uses`. `def:mononet`, `thm:mono-approx`, `thm:leshno-dense` are
cross-chapter labels defined in the Mikulincer–Reichman / Leshno chapters.

- [ ] **Step 2: Verify (blueprint build + checkdecls).**

```bash
export PATH="$HOME/.local/bin:$PATH"    # leanblueprint installed via scripts/setup-dev.sh
leanblueprint web
lake exe checkdecls blueprint/lean_decls
```
Expected: `leanblueprint web` succeeds; `checkdecls` exit 0 (every `\lean{}` ref — including the new
`rsDense_monotone`, `residual`, `ResNet.monotone_toFun`, `deep_monotone_approximation`,
`deep_partial_monotone_approximation` — resolves). If `leanblueprint` is unavailable, fall back to
`#check @UniversalApproximation.Runje.<name>` for each new ref and note CI will run the full build.

- [ ] **Step 3: Commit.**

```bash
git add blueprint/src/chapter/runje.tex
git commit -m "docs(blueprint): reframe Runje chapter as deep constrained monotone nets + add results"
```

---

## Self-Review

**Spec coverage:**
- §5 R–S dense monotone instance + activation instances → Task 1. ✓
- §6 residual combinator + concrete gate/skip instances → Task 2 Steps 1–2. ✓
- §7 deep stack (`ResBlock`/`ResNet`) + any-depth soundness → Task 2 Steps 3–4. ✓
- §8 `DeepMonoNet` + `MonoNet.toDeep` (exact) + single-block witness + `deep_monotone_approximation`
  → Task 3. ✓
- §9 `DeepPartMonoNet` soundness + `deep_partial_monotone_approximation` → Task 4. ✓
- §10 wiring + gate → Task 5 (Steps 1–3, 5). ✓
- §11 in-scope docs reframing (module docstrings + `README`/`CLAUDE` + aggregator/root) → Task 5
  (Steps 2, 4); blueprint Runje chapter reframe + extend + `checkdecls` → Task 6. ✓
- §11 non-goals (no trainability claim, no heavy depth arithmetic, no re-derived R–S UAP) →
  respected: no task adds those. ✓

**Placeholder scan:** Definitions/statements are given in full; each `sorry` in a code block is
scaffolding discharged by that step's proof strategy (named Mathlib lemmas), and **no task commits
with a `sorry`** (build + gate enforce it). No `TBD`/`TODO`.

**Type/name consistency:** `rsDense`/`rsDense_monotone`, `residual`/`residual_monotone`,
`shiftedElu`/`scaledElu`/`expSkip`, `ResBlock`/`ResNet`/`ResNet.monotone_toFun`,
`DeepMonoNet`/`MonoNet.toDeep`/`toDeep_toFun`/`toDeep_isMonotone`/`deep_monotone_approximation`,
`DeepPartMonoNet`/`monotone_snd`/`deep_partial_monotone_approximation` are used consistently across
producing and consuming tasks. The `⦃a b⦄`/`⦃x y⦄` monotonicity binder form matches
`monotone_approximation` and `partial_monotone_approximation`. `MonoNet` field names
(`width`/`stack`/`readW`/`readBias`) and `MonoNet.toFun`/`IsMonotone` match the verbatim signatures.

**Known risk (flagged):** Task 1's `elu`/`softplus` saturating limits and Task 3's `toDeep_toFun`
`simp` reduction are the fiddliest; both have concrete lemma-level strategies. If any becomes
research-grade, report `NEEDS_CONTEXT` rather than weakening a statement or hiding a `sorry`.
