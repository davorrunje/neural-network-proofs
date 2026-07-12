# Amos ICNN Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize, sorry-free, the fully-input-convex neural network (FICNN, Amos–Xu–Kolter 2017)
in `UniversalApproximation.Amos` and prove soundness — an ICNN denotes a convex function
(`ConvexOn ℝ Set.univ`) — with all living docs updated to a sixth development.

**Architecture:** New structure `ICNNLayer` (two weight matrices per layer + an activation) chained
in an inductive `ICNN` that threads the original input `y` into every layer; convexity of the
denotation is proved by a `ConvexOn` induction over the chain, reusing Mathlib's
`ConvexOn.smul/.add`, `LinearMap.convexOn`, and `ConvexOn.comp`.

**Tech Stack:** Lean 4, Mathlib, Lake 5.0.0, leanblueprint + checkdecls. LSP tools (`lean_goal`,
`lean_leansearch`, `lean_loogle`, `lean_multi_attempt`, `lean_diagnostic_messages`).

**Spec:** `docs/superpowers/specs/2026-07-12-amos-icnn-soundness-design.md`.

## Global Constraints

- **No `sorry`/`admit`.** Every commit sorry-free; clean headline reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Line length ≤ 100 codepoints** (measure codepoints:
  `python3 -c "import sys; print(max(len(l.rstrip(chr(10))) for l in open(sys.argv[1])))" <file>`).
- **Minimal, precise imports** — no blanket `import Mathlib` (`import Mathlib.Tactic` acceptable for
  proof-heavy files, matching sibling headline files). Clean build is the gate.
- **File header** (each file): Apache-2.0 + `Authors: Davor Runje` + a `/-! … -/` module doc.
- **Namespace** `UniversalApproximation.Amos`; module prefix
  `NeuralNetworkProofs.UniversalApproximation.Amos.<File>`.
- **Sorry-free gate:** `lake env lean scripts/check_sorry_free.lean`.
- **Docs framing:** Amos is the **sixth** development, *soundness now, convex UAP forthcoming (dev 2)*.

## Confirmed Mathlib tools (verbatim, verified via loogle/leansearch)

```lean
ConvexOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s (fun x => c • f x)
ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g)
ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
  (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f)
LinearMap.convexOn (f : E →ₗ[𝕜] β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s ⇑f
ConvexOn.continuousOn [FiniteDimensional ℝ E] (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
  ContinuousOn f C
-- also: convex_univ : Convex 𝕜 Set.univ ; ConvexOn.sup ; convexOn_const ; convexOn_id
-- (confirm ConvexOn.sup / convexOn_id / convexOn_const shapes with lean_loogle during impl)
```

---

### Task 1: `Amos/Defs.lean` — FICNN structure + denotation

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Amos/Defs.lean`

**Interfaces:**
- Consumes: Mathlib (`Matrix.mulVec`, `Fin`).
- Produces: `ICNNLayer` (fields `Wz Wy bias act`), `ICNNLayer.toFun`, `ICNNLayer.IsConvex`;
  `ICNN` (`nil`/`cons`), `ICNN.eval`, `ICNN.IsConvex`, `ICNN.toFun`.

- [ ] **Step 1: Write the file.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul

/-!
# Fully input-convex neural networks — definitions (Amos et al.)

The fully-input-convex network (FICNN) of Amos–Xu–Kolter (2017): each layer propagates a hidden
vector `z` with nonnegative weights and re-injects the original input `y` through an unconstrained
skip, `z ↦ act (Wz z + Wy y + b)`. With `Wz ≥ 0` and a convex, nondecreasing activation the
denotation is convex in `y` (proved in `Amos/Convex.lean`). The convex sibling of the constrained-
monotone developments.
-/

namespace UniversalApproximation.Amos

/-- One FICNN layer, input dim `d`, hidden `a → b`: `z ↦ act (Wz z + Wy y + b)` componentwise. -/
structure ICNNLayer (d a b : ℕ) where
  /-- Propagation weights (nonnegative for convexity). -/
  Wz : Matrix (Fin b) (Fin a) ℝ
  /-- Input-skip weights (unconstrained). -/
  Wy : Matrix (Fin b) (Fin d) ℝ
  /-- Layer bias. -/
  bias : Fin b → ℝ
  /-- Activation (convex + nondecreasing for convexity). -/
  act : ℝ → ℝ

/-- Layer denotation on hidden `z` and original input `y`. -/
noncomputable def ICNNLayer.toFun {d a b} (L : ICNNLayer d a b)
    (z : Fin a → ℝ) (y : Fin d → ℝ) : Fin b → ℝ :=
  fun j => L.act ((L.Wz.mulVec z) j + (L.Wy.mulVec y) j + L.bias j)

/-- The convexity-inducing constraints: `Wz` nonnegative, `act` convex and nondecreasing. -/
def ICNNLayer.IsConvex {d a b} (L : ICNNLayer d a b) : Prop :=
  (∀ i j, 0 ≤ L.Wz i j) ∧ Monotone L.act ∧ ConvexOn ℝ Set.univ L.act

/-- A FICNN: a chain of layers threading the original input `y`. -/
inductive ICNN (d : ℕ) : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ICNN d a a
  | cons : {a b c : ℕ} → ICNNLayer d a b → ICNN d b c → ICNN d a c

/-- Evaluate the chain: `y` fed to every layer, `z` threaded. -/
noncomputable def ICNN.eval {d} :
    {a b : ℕ} → ICNN d a b → (Fin d → ℝ) → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil, _, z => z
  | _, _, .cons L rest, y, z => rest.eval y (L.toFun z y)

/-- Every layer satisfies the convexity constraints. -/
def ICNN.IsConvex {d} : {a b : ℕ} → ICNN d a b → Prop
  | _, _, .nil => True
  | _, _, .cons L rest => L.IsConvex ∧ rest.IsConvex

/-- Scalar FICNN denotation: start from a width-0 hidden vector (so the first layer is the
input-affine `act (Wy y + b)`), end at width 1. -/
noncomputable def ICNN.toFun {d} (N : ICNN d 0 1) (y : Fin d → ℝ) : ℝ :=
  N.eval y (0 : Fin 0 → ℝ) 0
```

- [ ] **Step 2: Build + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Defs`; confirm no `sorry` via
`lean_diagnostic_messages`. (If `Data.Matrix.Mul` / `Matrix.mulVec` needs a different import, confirm
with `lean_hover_info` on `Matrix.mulVec` and adjust.)

```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Defs.lean
git commit -m "feat(amos): FICNN structure (ICNNLayer, ICNN, eval, IsConvex, toFun)"
```

---

### Task 2: `Amos/Activation.lean` — convex + monotone activations

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Amos/Activation.lean`

**Interfaces:**
- Consumes: Mathlib (`ConvexOn.sup`, `convexOn_const`, `convexOn_id`, `Real.exp`, `Real.log`).
- Produces: `relu`, `relu_convexOn`, `relu_monotone`, `softplus`, `softplus_convexOn`,
  `softplus_monotone`, `id_convexOn`, `id_monotone` (all in `UniversalApproximation.Amos`).

- [ ] **Step 1: Write definitions + statements.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Convex, nondecreasing activations for FICNNs (Amos et al.)

Concrete activations usable in a convex ICNN layer (`ConvexOn ℝ univ` + `Monotone`): `relu`,
`softplus`, and the identity (for a linear final layer). `softplus` is defined independently here
(the `Runje` development has its own copy; not shared, to keep developments self-contained).
-/

namespace UniversalApproximation.Amos

/-- Rectified linear unit. -/
def relu (x : ℝ) : ℝ := max 0 x
/-- Softplus. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem relu_convexOn : ConvexOn ℝ Set.univ relu := by sorry
theorem relu_monotone : Monotone relu := by sorry
theorem softplus_convexOn : ConvexOn ℝ Set.univ softplus := by sorry
theorem softplus_monotone : Monotone softplus := by sorry
theorem id_convexOn : ConvexOn ℝ Set.univ (id : ℝ → ℝ) := by sorry
theorem id_monotone : Monotone (id : ℝ → ℝ) := by sorry
```

- [ ] **Step 2: Prove them.**

Strategy (verify exact names with `lean_leansearch`/`lean_loogle`):
- `relu_convexOn`: `relu = fun x => max 0 x`; `(convexOn_const).sup convexOn_id` (via `ConvexOn.sup`),
  or `convexOn_const.sup (convexOn_id)` — confirm `ConvexOn.sup` signature.
- `relu_monotone`: `fun x y h => max_le_max le_rfl h` / `monotone_const.max monotone_id`.
- `softplus_convexOn`: `log(1+exp x)` is convex — search `Real.convexOn_log`? more directly
  `convexOn` of `log∘(1+exp)`; likely provable via `StrictConvexOn`/second-derivative or a Mathlib
  `convexOn` lemma for `logAddExp`/`Real.add_pow_le`… use `lean_leansearch "softplus convex"` /
  "log sum exp convex". If no direct lemma, prove via `ConvexOn` of `Real.exp` (`convexOn_exp`) plus
  a log-sum-exp convexity lemma; if genuinely hard, this activation may be dropped (relu + id
  suffice for a nonempty instance set — see fallback).
- `softplus_monotone`: `Real.log` monotone on `(0,∞)`, `1+exp` positive + monotone; compose
  (`Real.exp_le_exp`, `add_le_add_left`, `Real.log_le_log`).
- `id_convexOn`: `convexOn_id convex_univ` (or `LinearMap.id.convexOn convex_univ`).
- `id_monotone`: `monotone_id`.

**Fallback:** if `softplus_convexOn` proves research-grade, drop `softplus` (keep `relu` + `id`; the
abstract ICNN only needs *some* convex+monotone instance). Note it in the report.

- [ ] **Step 3: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Activation`; confirm no `sorry`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Activation.lean
git commit -m "feat(amos): convex + monotone activations (relu, softplus, id)"
```

---

### Task 3: `Amos/Convex.lean` — helpers + soundness headline

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Amos/Convex.lean`

**Interfaces:**
- Consumes: Task 1 (`ICNNLayer`, `ICNN`, `eval`, `IsConvex`, `toFun`); Mathlib `ConvexOn.*`,
  `LinearMap.convexOn`, `ConvexOn.continuousOn`.
- Produces: `linear_coord_convexOn`, `convexOn_finset_sum` (if needed), `convexOn_comp_univ`,
  `ICNN.eval_convexOn`, `icnn_convex`.

- [ ] **Step 1: Helper — a coordinate of a matrix-vector product is convex (linear).**

```lean
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs

namespace UniversalApproximation.Amos

open scoped BigOperators

/-- The `j`-th coordinate of `W.mulVec ·` is a convex (indeed linear) functional. -/
theorem linear_coord_convexOn {d b : ℕ} (W : Matrix (Fin b) (Fin d) ℝ) (j : Fin b) :
    ConvexOn ℝ Set.univ (fun y : Fin d → ℝ => (W.mulVec y) j) := by
  sorry
```

Strategy: `(W.mulVec y) j = (Matrix.mulVecLin W y) j = (proj j ∘ₗ Matrix.mulVecLin W) y`, a
`LinearMap`; apply `LinearMap.convexOn _ convex_univ`. Build the LinearMap as
`(LinearMap.proj j).comp (Matrix.mulVecLin W)` (confirm `Matrix.mulVecLin` and `LinearMap.proj`
names via `lean_loogle`); then `simp`/`rfl` to match `(W.mulVec y) j`.

- [ ] **Step 2: Helper — the convex-nondecreasing ∘ convex composition on `univ`.**

```lean
/-- If `g` is convex and monotone on all of `ℝ` and `f : (Fin d → ℝ) → ℝ` is convex on `univ`,
then `g ∘ f` is convex on `univ`. -/
theorem convexOn_comp_univ {d : ℕ} {g : ℝ → ℝ} {f : (Fin d → ℝ) → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hgm : Monotone g) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun y => g (f y)) := by
  sorry
```

Strategy: apply `ConvexOn.comp (g := g) (f := f)`, which needs `ConvexOn ℝ (f '' univ) g`,
`ConvexOn ℝ univ f` (= `hf`), and `MonotoneOn g (f '' univ)` (= `hgm.monotoneOn _`). Get the first
from `hg.subset (Set.subset_univ _) hrange` where `hrange : Convex ℝ (f '' Set.univ)`. Prove
`hrange`: `f` is continuous (`hf.continuousOn isOpen_univ` needs `[FiniteDimensional ℝ (Fin d → ℝ)]`
— available; then `continuousOn_univ.mp`), so `Set.range f` is connected
(`isConnected_range`/`IsPreconnected`), hence an interval in `ℝ`, hence `Convex ℝ (Set.range f)`
(`IsPreconnected` on `ℝ` ↔ `OrdConnected` ↔ `Convex`; search `Convex ℝ`/`IsPreconnected.ordConnected`
/ `Set.OrdConnected.convex`). Note `f '' Set.univ = Set.range f`. **This is the one non-mechanical
lemma** — use `lean_leansearch`/`lean_state_search` for the connected-⇒-convex-in-ℝ step; if it
turns research-grade, report `NEEDS_CONTEXT` (do NOT weaken).

- [ ] **Step 3: Helper — finite sum of convex functions is convex (if no direct Mathlib lemma).**

```lean
/-- A finite sum of convex functions on `univ` is convex. -/
theorem convexOn_univ_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin d → ℝ) → ℝ) (h : ∀ i ∈ s, ConvexOn ℝ Set.univ (F i)) :
    ConvexOn ℝ Set.univ (fun y => ∑ i ∈ s, F i y) := by
  sorry
```

Strategy: `Finset.induction_on s` — base `convexOn_const` (empty sum `= 0`); step
`ConvexOn.add` with the new summand (rewrite `Finset.sum_insert`). First check whether Mathlib
already has this (`lean_loogle "ConvexOn"` / `lean_leansearch "sum of convex functions convex"`); if
a packaged lemma exists, use it and drop this helper.

- [ ] **Step 4: The induction lemma.**

```lean
theorem ICNN.eval_convexOn {d : ℕ} : {a b : ℕ} → (N : ICNN d a b) → N.IsConvex →
    (zf : (Fin d → ℝ) → (Fin a → ℝ)) → (∀ i, ConvexOn ℝ Set.univ (fun y => zf y i)) →
    ∀ j, ConvexOn ℝ Set.univ (fun y => N.eval y (zf y) j)
  | _, _, .nil, _, _, hz, j => by simpa [ICNN.eval] using hz j
  | _, _, .cons L rest, h, zf, hz, j => by
      sorry
```

Strategy for `cons`: let `zf' y := L.toFun (zf y) y`. Show `∀ k, ConvexOn ℝ univ (fun y => zf' y k)`:
each `zf' y k = L.act ((L.Wz.mulVec (zf y)) k + (L.Wy.mulVec y) k + L.bias k)`. The inner argument is
`(∑ m, L.Wz k m * zf y m) + (L.Wy.mulVec y) k + L.bias k`:
- `∑ m, L.Wz k m * zf y m` convex: `convexOn_univ_finset_sum` with each summand
  `ConvexOn.smul (h.1.1 k m) (hz m)` (note `L.Wz k m • (zf y m) = L.Wz k m * (zf y m)`; unfold
  `Matrix.mulVec`/`dotProduct` to this sum form);
- `(L.Wy.mulVec y) k` convex: `linear_coord_convexOn L.Wy k`;
- `L.bias k` const: `convexOn_const`;
- combine with `ConvexOn.add` (twice); then `convexOn_comp_univ h.act-convex h.act-monotone <arg>`
  using `h.1` (the layer `IsConvex` gives `Monotone L.act` and `ConvexOn ℝ univ L.act`).
Then `rest.eval_convexOn h.2 zf' <this>` and `simpa [ICNN.eval]`. Use `lean_goal` throughout; the
`Matrix.mulVec`→`∑` unfolding is the fiddly bookkeeping.

- [ ] **Step 5: The headline.**

```lean
/-- **Soundness.** A fully input-convex network with nonnegative propagation weights and convex,
nondecreasing activations denotes a convex function. -/
theorem icnn_convex {d : ℕ} (N : ICNN d 0 1) (h : N.IsConvex) :
    ConvexOn ℝ Set.univ N.toFun := by
  have := N.eval_convexOn h (fun _ => (0 : Fin 0 → ℝ)) (fun i => i.elim0) 0
  simpa [ICNN.toFun] using this
```

(The initial `z` has type `Fin 0 → ℝ`; the coord hypothesis `∀ i : Fin 0, …` is discharged by
`fun i => i.elim0`.)

- [ ] **Step 6: Build sorry-free + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Convex`; confirm no `sorry`;
`lean_verify UniversalApproximation.Amos.icnn_convex` = `[propext, Classical.choice, Quot.sound]`.

```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Convex.lean
git commit -m "feat(amos): ICNN soundness — icnn_convex (ConvexOn denotation)"
```

---

### Task 4: Re-export root, aggregator/root wiring, gate, README + CLAUDE

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Amos.lean`; modify
`NeuralNetworkProofs/UniversalApproximation.lean`, `NeuralNetworkProofs.lean`,
`scripts/check_sorry_free.lean`, `README.md`, `CLAUDE.md`.

**Interfaces:** Consumes Tasks 1–3. Produces the `…Amos` module reachable by the default build +
gate.

- [ ] **Step 1: Re-export root `Amos.lean`.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs
import NeuralNetworkProofs.UniversalApproximation.Amos.Activation
import NeuralNetworkProofs.UniversalApproximation.Amos.Convex

/-!
# Input-Convex Neural Networks — Amos et al. (2017)

The fully-input-convex network (FICNN) and its soundness: an ICNN with nonnegative propagation
weights and convex, nondecreasing activations denotes a convex function. Universal approximation of
convex functions is a forthcoming development.

* `UniversalApproximation.Amos.icnn_convex` — soundness (convex denotation).
-/
```

- [ ] **Step 2: Aggregator + top-root docstrings.**

In `NeuralNetworkProofs/UniversalApproximation.lean`: add
`import NeuralNetworkProofs.UniversalApproximation.Amos` (after `…Runje`) and a bullet
`* UniversalApproximation.Amos.icnn_convex — Amos et al. (2017), ICNN soundness (convex UAP forthcoming).`
to its docstring. In `NeuralNetworkProofs.lean`: add the same bullet to its headline list (no import
change — transitive via the aggregator).

- [ ] **Step 3: Sorry-free gate.**

In `scripts/check_sorry_free.lean`, add `UniversalApproximation.Amos` to the `open` line(s) (split
to keep ≤ 100 codepoints) and append `#print axioms icnn_convex`.

- [ ] **Step 4: README + CLAUDE (sixth development).**

- `README.md`: add an Amos entry to the developments list (Input-Convex Neural Networks, Amos–Xu–
  Kolter 2017; headline `…Amos.icnn_convex`; convex UAP forthcoming). Read first; match voice.
- `CLAUDE.md`: change "Five developments" → "Six developments"; add an Amos bullet in "What this is"
  and a layout-table row: `NeuralNetworkProofs/UniversalApproximation/Amos/` + `Amos.lean` |
  `UniversalApproximation.Amos` | Input-Convex Neural Networks — soundness (convex UAP forthcoming).
  Update the aggregator note ("re-exports all … UAT roots") count if it names one.

- [ ] **Step 5: Full build + gate + commit.**

```bash
lake build
lake env lean scripts/check_sorry_free.lean
```
Expected: green; `icnn_convex` reports `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
anywhere. (Serial-build fallback if EMFILE.)

```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos.lean \
  NeuralNetworkProofs/UniversalApproximation.lean NeuralNetworkProofs.lean \
  scripts/check_sorry_free.lean README.md CLAUDE.md
git commit -m "feat(amos): wire ICNN soundness into build, aggregator, gate, README/CLAUDE"
```

---

### Task 5: Blueprint chapter + intro + site card

**Files:** Create `blueprint/src/chapter/amos.tex`; modify `blueprint/src/content.tex`,
`blueprint/src/chapter/intro.tex`, `site/index.html`.

**Interfaces:** Consumes `icnn_convex` (Task 3). Produces the Amos blueprint chapter + updated
landing page.

- [ ] **Step 1: Blueprint chapter `amos.tex`.**

Create `blueprint/src/chapter/amos.tex` with a short chapter presenting the FICNN and the soundness
theorem, with a `\lean{}` node for the headline:

```tex
\chapter{Input-convex networks --- Amos et al.}

\begin{definition}[Fully input-convex network]\label{def:icnn}
  A FICNN threads the input $y$ into every layer, $z_{i+1}=\rho_i(W^z_i z_i + W^y_i y + b_i)$, with
  nonnegative propagation weights $W^z_i\ge 0$, unconstrained input skip $W^y_i$, and convex
  nondecreasing activations $\rho_i$.
\end{definition}

\begin{theorem}[ICNN soundness]\label{thm:icnn-convex}
  \lean{UniversalApproximation.Amos.icnn_convex}\leanok
  \uses{def:icnn}
  Such a network denotes a convex function of its input.
\end{theorem}
\begin{proof}\leanok
  \uses{def:icnn}
  By induction over the layer chain: each layer maps convex coordinates to convex coordinates ---
  a nonnegative combination of convex functions plus the affine input skip is convex, and a convex
  nondecreasing activation composed with a convex function is convex.
\end{proof}
```

- [ ] **Step 2: `content.tex` + `intro.tex`.**

- `blueprint/src/content.tex`: add `\input{chapter/amos}` after `\input{chapter/runje}`.
- `blueprint/src/chapter/intro.tex`: add a sixth `\item` for Amos (Input-Convex Neural Networks;
  ICNN soundness — convex UAP forthcoming) to the developments `itemize`, and update the count
  sentence ("across five developments" → "six").

- [ ] **Step 3: `site/index.html`.**

Add a sixth `<div class="card">` for the Amos ICNN development (title "Amos et al. (2017)", a short
description — Input-Convex Neural Networks; ICNN soundness formalized, convex UAP forthcoming — and a
link to the paper, arXiv:1609.07152). Match the existing card markup.

- [ ] **Step 4: Verify + commit.**

```bash
export PATH="$HOME/.local/bin:$PATH"
leanblueprint web
lake exe checkdecls blueprint/lean_decls
```
Expected: `leanblueprint web` succeeds; `checkdecls` exit 0 (the new `\lean{…Amos.icnn_convex}` ref
resolves). (Fallback if `leanblueprint` unavailable: `#check @UniversalApproximation.Amos.icnn_convex`
and note CI will run the full build.) Then confirm the docs say "six developments" and list Amos.

```bash
git add blueprint/src/chapter/amos.tex blueprint/src/content.tex \
  blueprint/src/chapter/intro.tex site/index.html
git commit -m "docs(amos): blueprint chapter + intro + site card (sixth development)"
```

---

## Self-Review

**Spec coverage:**
- §3 FICNN structure → Task 1. ✓
- §4 soundness (`icnn_convex` + `eval_convexOn`) → Task 3 Steps 4–5. ✓
- §5 activations + abstraction → Task 2. ✓
- §7 helpers (`linear_coord_convexOn` [= §7 `linear_convexOn`], `convexOn_comp_univ`, finite-sum) →
  Task 3 Steps 1–3. ✓
- §6 file layout → Tasks 1–3 + Task 4 (`Amos.lean`). ✓
- §8 docs (README, CLAUDE six-dev, aggregator/root docstrings, blueprint chapter + intro +
  content.tex, site card) → Tasks 4–5. ✓
- §9 gate → Task 4 Step 3/5. ✓
- §10 non-goals (UAP dev2, partial-monotone dev3, PICNN, training) → not implemented (correct). ✓

**Placeholder scan:** Definitions/statements are given in full; each `sorry` in a code block is
scaffolding discharged by that step's strategy (named Mathlib lemmas) — no task commits with a
`sorry` (build + gate enforce it). The `softplus` and `convexOn_comp_univ` fallbacks are explicit
decision points, not vague placeholders. No `TBD`/`TODO`.

**Type/name consistency:** `ICNNLayer`/`ICNN`/`eval`/`IsConvex`/`toFun`, `relu`/`softplus`/`id_*`,
`linear_coord_convexOn`/`convexOn_comp_univ`/`convexOn_univ_finset_sum`, `ICNN.eval_convexOn`,
`icnn_convex` are used consistently across producing and consuming tasks. Headline
`UniversalApproximation.Amos.icnn_convex` matches the gate (Task 4) and blueprint (Task 5).

**Known risks (flagged):** `convexOn_comp_univ`'s range-is-convex step (Task 3 Step 2) and
`softplus_convexOn` (Task 2) are the non-mechanical spots; both have concrete strategies + explicit
fallbacks (`NEEDS_CONTEXT` / drop softplus). The `Matrix.mulVec`→`∑` unfolding in Task 3 Step 4 is
bookkeeping.
