# ICNN Universal Approximation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that a fully-input-convex ICNN uniformly approximates any convex, differentiable
function on a compact set — the headline `UniversalApproximation.Amos.icnn_approximation`.

**Architecture:** Three pillars. (A) A finite max of affine functions is realized by a nonnegative-
`Wz` ReLU/id ICNN via a running-max recursion. (B) A convex differentiable function lies above its
tangent plane, derived from Mathlib's 1-D convex-derivative lemmas by restricting to lines. (C) On a
compact set, a finite max of tangent planes over an ε-net approximates the function uniformly; compose
A + C.

**Tech Stack:** Lean 4 + Mathlib. Builds on dev 1 (`UniversalApproximation.Amos`, merged): the
`ICNNLayer`/`ICNN`/`eval`/`IsConvex`/`toFun` structure, `icnn_convex`, and the `relu`/`id`/`softplus`
convex+monotone activations in `Amos/Activation.lean`.

## Global Constraints

- Line length ≤ 100 codepoints (Mathlib glyphs count as 1 cp; measure with `python3 -c "print(len(line))"`).
- No `sorry` / `admit`. A research-grade blocker is reported as `NEEDS_CONTEXT` — never hidden, never
  worked around by weakening a theorem statement.
- Minimal precise imports (no blanket `import Mathlib`); confirm any import set by a clean build.
- Frozen (must NOT change statement/signature): all dev-1 decls (`ICNNLayer`, `ICNN`, `ICNNLayer.toFun`,
  `ICNNLayer.IsConvex`, `ICNN.eval`, `ICNN.IsConvex`, `ICNN.toFun`, `icnn_convex`) and every other
  development's headline.
- Sorry-free gate: every headline must report exactly `[propext, Classical.choice, Quot.sound]`.
- `#print axioms` reads the compiled olean — rebuild (`lake build`) before trusting it.
- Namespace: everything new lives in `namespace UniversalApproximation.Amos`.
- Branch: `feat/amos-icnn-uap` (already created off `main`).
- The "test" for a Lean task = the target decls elaborate, `lake build` is green, and the sorry-free
  gate reports the headline axiom-clean (no `sorryAx`). This repo has no unit-test framework and does
  not use `example`s as tests (Mathlib convention) — do not add them.

### Dev-1 interfaces (verbatim, from `Amos/Defs.lean` — consume, do not modify)

```lean
structure ICNNLayer (d a b : ℕ) where
  Wz : Matrix (Fin b) (Fin a) ℝ
  Wy : Matrix (Fin b) (Fin d) ℝ
  bias : Fin b → ℝ
  act : ℝ → ℝ
noncomputable def ICNNLayer.toFun {d a b} (L : ICNNLayer d a b) (z : Fin a → ℝ) (y : Fin d → ℝ) :
    Fin b → ℝ := fun j => L.act ((L.Wz.mulVec z) j + (L.Wy.mulVec y) j + L.bias j)
def ICNNLayer.IsConvex {d a b} (L : ICNNLayer d a b) : Prop :=
  (∀ i j, 0 ≤ L.Wz i j) ∧ Monotone L.act ∧ ConvexOn ℝ Set.univ L.act
inductive ICNN (d : ℕ) : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ICNN d a a
  | cons : {a b c : ℕ} → ICNNLayer d a b → ICNN d b c → ICNN d a c
noncomputable def ICNN.eval {d} : {a b : ℕ} → ICNN d a b → (Fin d → ℝ) → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil, _, z => z
  | _, _, .cons L rest, y, z => rest.eval y (L.toFun z y)
def ICNN.IsConvex {d} : {a b : ℕ} → ICNN d a b → Prop
  | _, _, .nil => True
  | _, _, .cons L rest => L.IsConvex ∧ rest.IsConvex
noncomputable def ICNN.toFun {d} (N : ICNN d 0 1) (y : Fin d → ℝ) : ℝ := N.eval y (0 : Fin 0 → ℝ) 0
```

From `Amos/Activation.lean`: `relu (x) = max 0 x`, `relu_convexOn : ConvexOn ℝ Set.univ relu`,
`relu_monotone : Monotone relu`, `id_convexOn : ConvexOn ℝ Set.univ (id : ℝ → ℝ)`,
`id_monotone : Monotone (id : ℝ → ℝ)`.

---

## File Structure

- `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/MaxAffine.lean` — `dotAffine`, `maxAffine`,
  its order lemmas, the layer constructors, `maxNet`, `maxNet_isConvex` (T1); `maxNet_toFun` /
  `maxAffine_isICNN` (T2).
- `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Tangent.lean` — `gradVec`,
  `gradVec_dotProduct`, `convex_diff_tangent_le` (T3).
- `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Density.lean` — `maxTangent_approx` (T4);
  `icnn_approximation` headline (T5).
- Modify `NeuralNetworkProofs/UniversalApproximation/Amos.lean` (re-export), `UniversalApproximation.lean`
  + `NeuralNetworkProofs.lean` (docstrings), `scripts/check_sorry_free.lean` (T5).
- Modify `README.md`, `CLAUDE.md`, `blueprint/src/chapter/amos.tex`, `blueprint/src/chapter/intro.tex`,
  `site/index.html` (T6).

Common index/notation decision (all tasks): affine pieces are indexed by `Fin (n + 1)` (never empty),
`n : ℕ`. An affine functional is a coefficient vector `a : Fin d → ℝ` plus constant `c : ℝ`, evaluated
as `dotAffine a c y = a ⬝ᵥ y + c` (`⬝ᵥ` = `Matrix.dotProduct`, `open scoped Matrix`). A matrix row is
`Matrix.of (fun _ : Fin 1 => a) : Matrix (Fin 1) (Fin d) ℝ`, whose `mulVec y 0 = a ⬝ᵥ y`.

---

## Task 1: MaxAffine — definitions, order lemmas, network, convexity

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/MaxAffine.lean`

**Interfaces:**
- Consumes: dev-1 `ICNNLayer`/`ICNN`/`IsConvex`, `relu`/`id` (+`_convexOn`/`_monotone`).
- Produces:
  - `dotAffine {d} (a : Fin d → ℝ) (c : ℝ) (y : Fin d → ℝ) : ℝ := a ⬝ᵥ y + c`
  - `maxAffine {d} : (n : ℕ) → (Fin (n+1) → (Fin d → ℝ)) → (Fin (n+1) → ℝ) → (Fin d → ℝ) → ℝ`
  - `le_maxAffine {d n a b y} (i) : dotAffine (a i) (b i) y ≤ maxAffine n a b y`
  - `maxAffine_le {d n a b y c} (h : ∀ i, dotAffine (a i) (b i) y ≤ c) : maxAffine n a b y ≤ c`
  - `maxNet {d} (n) (a : Fin (n+1) → (Fin d → ℝ)) (b : Fin (n+1) → ℝ) : ICNN d 0 1`
  - `maxNet_isConvex {d n a b} : (maxNet n a b).IsConvex`

- [ ] **Step 1: File header + imports + namespace.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs
import NeuralNetworkProofs.UniversalApproximation.Amos.Activation

/-!
# Max of affine functions as a convex ICNN (Amos et al.)

A finite max of affine functions `y ↦ max_i (aᵢ ⬝ᵥ y + bᵢ)` is realized by a fully input-convex
network with nonnegative propagation weights and `relu`/`id` activations, via the running-max
recursion `hₖ = max (hₖ₋₁) gₖ = gₖ + relu (hₖ₋₁ - gₖ)`. Each max-step is two width-1 layers (a
`relu` layer then an `id` layer); every `Wz` entry is `0` or `1`, and all affine data rides the
unconstrained input skip `Wy`/`bias`. Used by `Approx/Density.lean` for the UAP headline.
-/

namespace UniversalApproximation.Amos

open scoped Matrix
```

- [ ] **Step 2: `dotAffine` and `maxAffine`.** Define the recursion so it matches the network exactly
  (running max, folding in `Fin.last`).

```lean
/-- An affine functional `y ↦ a ⬝ᵥ y + c`. -/
def dotAffine {d : ℕ} (a : Fin d → ℝ) (c : ℝ) (y : Fin d → ℝ) : ℝ := a ⬝ᵥ y + c

/-- The max of the `n+1` affine functions `dotAffine (a i) (b i)`. -/
def maxAffine {d : ℕ} :
    (n : ℕ) → (Fin (n + 1) → (Fin d → ℝ)) → (Fin (n + 1) → ℝ) → (Fin d → ℝ) → ℝ
  | 0, a, b, y => dotAffine (a 0) (b 0) y
  | n + 1, a, b, y =>
      max (maxAffine n (fun i => a i.castSucc) (fun i => b i.castSucc) y)
        (dotAffine (a (Fin.last (n + 1))) (b (Fin.last (n + 1))) y)
```

- [ ] **Step 3: Order lemmas.** Both by induction on `n`; use `Fin.lastCases` to split an index into
  `castSucc`/`last`, and `le_max_left`/`le_max_right`/`max_le`.

```lean
theorem le_maxAffine {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (y : Fin d → ℝ) → (i : Fin (n + 1)) → dotAffine (a i) (b i) y ≤ maxAffine n a b y
theorem maxAffine_le {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) → (b : Fin (n + 1) → ℝ) →
    (y : Fin d → ℝ) → (c : ℝ) → (∀ i, dotAffine (a i) (b i) y ≤ c) → maxAffine n a b y ≤ c
```

Strategy for `le_maxAffine`: induction on `n`. Base `n=0`: `i = 0`, `le_refl`. Step: `Fin.lastCases i`
— if `last`, `le_max_right`; if `castSucc j`, chain the IH with `le_max_left`. `maxAffine_le`: base
`le_refl`-style from the single hypothesis; step `max_le` of (IH on the restricted family) and (`h` at
`last`).

- [ ] **Step 4: Layer constructors.** Three width-≤1 layers. `!![1]` is the `1×1` matrix with entry 1;
  the init `Wz` is the empty `1×0` matrix `Matrix.of (fun _ (j : Fin 0) => j.elim0)`.

```lean
/-- Initial layer `0 → 1`: `id (a ⬝ᵥ y + c)` (no hidden input). -/
def initLayer {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 0 1 where
  Wz := Matrix.of (fun _ (j : Fin 0) => j.elim0)
  Wy := Matrix.of (fun _ => a)
  bias := fun _ => c
  act := id
/-- `relu` step `1 → 1`: `relu (h - (a ⬝ᵥ y + c))`. -/
def reluStep {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 1 1 where
  Wz := !![1]
  Wy := Matrix.of (fun _ => -a)
  bias := fun _ => -c
  act := relu
/-- `id` step `1 → 1`: `u + (a ⬝ᵥ y + c)`. -/
def idStep {d : ℕ} (a : Fin d → ℝ) (c : ℝ) : ICNNLayer d 1 1 where
  Wz := !![1]
  Wy := Matrix.of (fun _ => a)
  bias := fun _ => c
  act := id
```

- [ ] **Step 5: Single-layer `toFun` evaluation lemmas.** These unfold `ICNNLayer.toFun` +
  `Matrix.mulVec`/`dotProduct` on `Fin 1`. Prove by `simp [ICNNLayer.toFun, dotAffine, …]`; pin the
  exact simp set during implementation (`Matrix.mulVec_single`, `Matrix.of_apply`,
  `Matrix.cons_val`, `Matrix.mulVec`, `Finset.sum_fin_eq_sum_range` as needed).

```lean
theorem initLayer_toFun {d} (a : Fin d → ℝ) (c : ℝ) (z : Fin 0 → ℝ) (y : Fin d → ℝ) :
    (initLayer a c).toFun z y 0 = dotAffine a c y
theorem reluStep_toFun {d} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (reluStep a c).toFun z y 0 = relu (z 0 - dotAffine a c y)
theorem idStep_toFun {d} (a : Fin d → ℝ) (c : ℝ) (z : Fin 1 → ℝ) (y : Fin d → ℝ) :
    (idStep a c).toFun z y 0 = z 0 + dotAffine a c y
```

- [ ] **Step 6: `maxNet` construction + tail.** Build init then `n` max-steps. Define a width-1 tail
  first (folds max-steps for the `castSucc`-restricted family, front to back), then prepend init.

```lean
/-- `n` max-steps folded onto a running hidden max (width 1 → 1). -/
def maxNetTail {d : ℕ} :
    (n : ℕ) → (Fin (n + 1) → (Fin d → ℝ)) → (Fin (n + 1) → ℝ) → ICNN d 1 1
  | 0, _, _ => ICNN.nil
  | n + 1, a, b =>
      .cons (reluStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1))))
        (.cons (idStep (a (Fin.last (n + 1))) (b (Fin.last (n + 1))))
          (maxNetTail n (fun i => a i.castSucc) (fun i => b i.castSucc)))
```

Wait — the running max must fold pieces `1 … n` after starting from piece `0`. Order matters for the
identity proof (T2), not for correctness of `maxAffine` (max is commutative/associative). Implement
`maxNetTail` to fold the SAME family order as `maxAffine`'s recursion (peel `Fin.last`, recurse on
`castSucc`), and let T2's identity proof mirror it. If the front-to-back cons order fights the
`eval` (which threads left-to-right) during T2, refactor `maxNetTail` to peel index `0` via
`Fin.cases` instead — decide in T2 and update this def accordingly (this is the one structural degree
of freedom; the reviewer should accept either peeling direction as long as T2's identity holds).

```lean
/-- The full max-of-affine network `0 → 1`. -/
def maxNet {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) : ICNN d 0 1 :=
  .cons (initLayer (a 0) (b 0)) (maxNetTail n a b)  -- adjust base index to match T2's peel direction
```

- [ ] **Step 7: `IsConvex` of every layer and the whole net.** Each `Wz` is `!![1]` or the empty
  matrix — entries `0`/`1`, all `≥ 0`. `act` is `relu` or `id`, both convex+monotone.

```lean
theorem initLayer_isConvex {d} (a : Fin d → ℝ) (c : ℝ) : (initLayer a c).IsConvex
theorem reluStep_isConvex {d} (a : Fin d → ℝ) (c : ℝ) : (reluStep a c).IsConvex
theorem idStep_isConvex {d} (a : Fin d → ℝ) (c : ℝ) : (idStep a c).IsConvex
theorem maxNetTail_isConvex {d} (n) (a) (b) : (maxNetTail (d := d) n a b).IsConvex
theorem maxNet_isConvex {d} (n) (a) (b) : (maxNet (d := d) n a b).IsConvex
```

Layer proofs: `refine ⟨?_, ?_, ?_⟩`; nonneg by `Fin.forall_fin_one`/`decide`-style on the `!![1]`
entry (`Matrix.cons_val`, `Matrix.of_apply`; `zero_le_one`) or vacuous for the empty `Wz`;
`Monotone`/`ConvexOn` from `relu_monotone`/`relu_convexOn`/`id_monotone`/`id_convexOn`.
`maxNetTail_isConvex` by induction on `n` unfolding `ICNN.IsConvex` on the two conses;
`maxNet_isConvex` = `⟨initLayer_isConvex …, maxNetTail_isConvex …⟩`.

- [ ] **Step 8: Build + verify.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine`
Expected: green. Then confirm no `sorry` remained: `grep -n "sorry\|admit" <file>` → no matches.

- [ ] **Step 9: Commit.**

```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Approx/MaxAffine.lean
git commit -m "feat(amos): maxAffine + convex max-of-affine ICNN construction (UAP T1)"
```

---

## Task 2: MaxAffine — the functional identity `maxNet.toFun = maxAffine`

**Files:**
- Modify: `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/MaxAffine.lean`

**Interfaces:**
- Consumes: everything from T1.
- Produces:
  - `maxNet_toFun {d n a b} (y) : (maxNet n a b).toFun y = maxAffine n a b y`
  - `maxAffine_isICNN {d n} (a : Fin (n+1) → (Fin d → ℝ)) (b : Fin (n+1) → ℝ) :`
    `∃ N : ICNN d 0 1, N.IsConvex ∧ N.toFun = fun y => maxAffine n a b y`

- [ ] **Step 1: Tail evaluation lemma.** The crux: `maxNetTail` starting from a running hidden value
  `r` computes the running max of `r` with the folded affine pieces. State it so induction closes.

```lean
theorem maxNetTail_eval {d : ℕ} : (n : ℕ) → (a : Fin (n + 1) → (Fin d → ℝ)) →
    (b : Fin (n + 1) → ℝ) → (y : Fin d → ℝ) → (r : ℝ) →
    (maxNetTail n a b).eval y (fun _ => r) 0 =
      /- running max of r with the pieces, matching maxAffine's fold -/ ...
```

Strategy: induction on `n`. Unfold `ICNN.eval` on the two conses (`reluStep`, `idStep`) using
`reluStep_toFun`/`idStep_toFun` from T1 to get, after one max-step, hidden value
`r + relu (… ) = max r (dotAffine …)` via `max_eq_add_relu` (see Step 2). Then apply the IH. The RHS
must be written to make base and step defeq to `maxAffine`'s recursion when `r` is the piece-0 value;
pin the exact RHS while proving (it is the running max, i.e. `maxAffine` folded onto `r`). If the
peel direction fights `eval`, adjust `maxNetTail`/`maxNet` in T1 (Step 6 note) and re-review T1.

- [ ] **Step 2: The max-relu identity.** A `_root_`-level real-arithmetic helper (used in Step 1).

```lean
theorem max_eq_add_relu (u v : ℝ) : max u v = v + relu (u - v) := by
  rw [relu]  -- relu (u - v) = max 0 (u - v)
  rcases le_total u v with h | h <;> simp [max_eq_left, max_eq_right, h] <;> ring
```
(Pin the exact tactic during implementation; the fact is `max u v = v + max 0 (u - v)`.)

- [ ] **Step 3: `maxNet_toFun`.** Unfold `ICNN.toFun` (= `eval … (0 : Fin 0 → ℝ) 0`) and the leading
  `initLayer` cons via `initLayer_toFun` (giving running start `r = dotAffine (a 0) (b 0) y`), then
  `maxNetTail_eval`. Reconcile with `maxAffine` by `Nat`/`Fin` reindexing (`Fin.lastCases` /
  `Fin.cases`), matching the peel direction chosen in T1.

```lean
theorem maxNet_toFun {d : ℕ} (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ)
    (y : Fin d → ℝ) : (maxNet n a b).toFun y = maxAffine n a b y
```

- [ ] **Step 4: `maxAffine_isICNN`.** Package.

```lean
theorem maxAffine_isICNN {d n : ℕ} (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ N.toFun = fun y => maxAffine n a b y :=
  ⟨maxNet n a b, maxNet_isConvex n a b, funext (maxNet_toFun n a b)⟩
```

- [ ] **Step 5: Build + verify + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Approx/MaxAffine.lean
git commit -m "feat(amos): maxNet.toFun = maxAffine functional identity (UAP T2)"
```

---

## Task 3: Tangent — the tangent-plane minorant

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Tangent.lean`

**Interfaces:**
- Consumes: `dotAffine` (T1); Mathlib convex-derivative + fderiv API.
- Produces:
  - `gradVec {d} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ`
    `:= fun j => fderiv ℝ f x (Pi.single j 1)`
  - `gradVec_dotProduct {d f x} (hx : DifferentiableAt ℝ f x) (v) :`
    `gradVec f x ⬝ᵥ v = fderiv ℝ f x v`
  - `convex_diff_tangent_le {d f} (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y) :`
    `f x + fderiv ℝ f x (y - x) ≤ f y`
  - `tangent_le {d f} (hf) (hd) (x y) :`
    `dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x) y ≤ f y`

- [ ] **Step 1: Header + imports + namespace.**

```lean
/- (Apache header as in Defs.lean) -/
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine

/-!
# Tangent-plane minorant for convex differentiable functions (Amos et al.)

A convex, differentiable `f : (Fin d → ℝ) → ℝ` lies above each of its tangent planes:
`f x + fderiv ℝ f x (y - x) ≤ f y`. Proved by restricting `f` to the line through `x` and `y` and
applying Mathlib's one-dimensional convex-derivative inequality (no supporting-hyperplane / Hahn–
Banach machinery). `gradVec` expresses the derivative functional as a dot product so the tangent
plane is an affine `dotAffine`, feeding `Approx/Density.lean`.
-/

namespace UniversalApproximation.Amos

open scoped Matrix
```

- [ ] **Step 2: `gradVec` + dot-product identity.** The functional `fderiv ℝ f x : (Fin d → ℝ) →L[ℝ] ℝ`
  equals the dot product with `gradVec f x`. Decompose `v = ∑ j, v j • Pi.single j 1` and use the
  functional's linearity (`map_sum`, `map_smul`).

```lean
def gradVec {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => fderiv ℝ f x (Pi.single j 1)
theorem gradVec_dotProduct {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (v : Fin d → ℝ) : gradVec f x ⬝ᵥ v = fderiv ℝ f x v
```

Strategy: `have : v = ∑ j, v j • Pi.single j (1 : ℝ) := by ext k; simp [Pi.single_apply,
Finset.sum_ite_eq]`. Then `rw [this, map_sum]`; `simp only [map_smul, gradVec, dotProduct, smul_eq_mul,
mul_comm]`. Pin exact lemmas (`Pi.single`, `Finset.univ_sum_single`/`Finset.sum_pi_single`,
`ContinuousLinearMap.map_smul`) while proving. Note: `fderiv` is `ℝ`-linear unconditionally (it is the
zero map when not differentiable), so `gradVec_dotProduct` needs no differentiability hypothesis.

- [ ] **Step 3: `convex_diff_tangent_le` via line restriction.** Let `φ t := f (x + t • (y - x))`.

```lean
theorem convex_diff_tangent_le {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : Fin d → ℝ) :
    f x + fderiv ℝ f x (y - x) ≤ f y
```

Strategy:
1. Affine map `g : ℝ →ᵃ[ℝ] (Fin d → ℝ)`, `g t = x + t • (y - x)` (`AffineMap.lineMap x y`, for which
   `AffineMap.lineMap x y t = x + t • (y - x)` up to the `lineMap` normal form; `g 0 = x`, `g 1 = y`).
2. `φ := f ∘ g` is `ConvexOn ℝ Set.univ` by `hf.comp_affineMap g` (preimage of `univ` is `univ`).
3. `φ` differentiable with `deriv φ 0 = fderiv ℝ f x (y - x)`: `HasDerivAt` of `g` at `0` is
   `y - x` (`(AffineMap.lineMap x y).hasDerivAt` / compute), compose with `hd.differentiableAt` via
   `HasFDerivAt.comp_hasDerivAt`.
4. Apply the 1-D tangent inequality `ConvexOn.le_slope_of_hasDerivAt`
   (`ConvexOn ℝ S φ → 0 ∈ S → 1 ∈ S → 0 < 1 → HasDerivAt φ φ' 0 → φ' ≤ slope φ 0 1`), with
   `slope φ 0 1 = (φ 1 - φ 0) / (1 - 0) = f y - f x`. Rearrange `φ' ≤ f y - f x` to the goal.
   Pin the exact 1-D lemma (`le_slope_of_hasDerivAt` vs `Convex.mul_sub_le_image_sub_of_le_deriv`)
   during implementation; `slope` unfolds via `slope_def_field`.

- [ ] **Step 4: `tangent_le` in `dotAffine` form.** Combine Steps 2–3: rewrite
  `fderiv ℝ f x (y - x) = gradVec f x ⬝ᵥ (y - x) = gradVec f x ⬝ᵥ y - gradVec f x ⬝ᵥ x`
  (`gradVec_dotProduct` + `Matrix.dotProduct_sub`), so
  `f x + fderiv ℝ f x (y - x) = dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x) y`.

```lean
theorem tangent_le {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : Fin d → ℝ) :
    dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x) y ≤ f y
```

- [ ] **Step 5: Build + verify + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Tangent`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Tangent.lean
git commit -m "feat(amos): tangent-plane minorant for convex differentiable f (UAP T3)"
```

---

## Task 4: Density — uniform approximation by a max of tangent planes

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Density.lean`

**Interfaces:**
- Consumes: `dotAffine`, `maxAffine`, `le_maxAffine`, `maxAffine_le` (T1); `gradVec`, `tangent_le`,
  `convex_diff_tangent_le`, `gradVec_dotProduct` (T3); Mathlib Lipschitz + compactness.
- Produces:
  - `maxTangent_approx {d} {f} (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)`
    `{K} (hK : IsCompact K) {ε} (hε : 0 < ε) :`
    `∃ (n : ℕ) (a : Fin (n+1) → (Fin d → ℝ)) (b : Fin (n+1) → ℝ),`
    `(∀ y, maxAffine n a b y ≤ f y) ∧ ∀ y ∈ K, f y - maxAffine n a b y ≤ ε`

- [ ] **Step 1: Header + imports + namespace.**

```lean
/- (Apache header) -/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Tangent

/-!
# ICNN universal approximation for convex differentiable functions (Amos et al.)

`maxTangent_approx`: on a compact set, a finite max of tangent planes of a convex differentiable `f`
approximates `f` uniformly to within any `ε`. The headline `icnn_approximation` combines this with
the `maxAffine`-is-a-convex-ICNN construction (`Approx/MaxAffine.lean`).
-/

namespace UniversalApproximation.Amos

open scoped Matrix
```

Trim imports to what actually builds (the `ThickenedIndicator`/covering import is a placeholder for
the finite-subcover API — replace with the module that actually provides `IsCompact.elim_finite_subcover`
/ `Metric.finite_cover_balls_of_compact`, confirmed by build).

- [ ] **Step 2: Lipschitz constant + gradient bound on a compact neighborhood.** Obtain `L ≥ 0` and a
  region containing `K` on which `f` is `L`-Lipschitz and `‖fderiv ℝ f x‖ ≤ L`.

Strategy: `f` is `LocallyLipschitz` (`ConvexOn.locallyLipschitz hf`, finite-dim). From `hK` +
local-Lipschitz, extract a single `L` and a bound valid on (a compact neighborhood of) `K`
(`IsCompact` + `LocallyLipschitz` ⇒ `∃ L, LipschitzOnWith L f U` for an open `U ⊇ K`; use
`IsCompact.exists_...`/covering). For the gradient bound, `‖fderiv ℝ f x‖ ≤ L` for `x ∈ K` follows
from `LipschitzOnWith` on a neighborhood of `x` via `norm_fderiv_le_of_lipschitzOn`-type reasoning;
pin the exact Mathlib lemma. FALLBACK if the operator-norm bound is awkward: avoid it entirely via the
reflection estimate `-fderiv ℝ f x (y - x) ≤ L‖y - x‖`, obtained from `convex_diff_tangent_le` at the
reflected point `2•x - y` plus Lipschitz `f (2•x - y) - f x ≤ L‖y - x‖` (needs the reflected point in
the Lipschitz region — enlarge the net radius bookkeeping). Choose whichever builds; the reviewer
accepts either as long as the `2Lδ` estimate in Step 4 holds.

- [ ] **Step 3: Finite δ-net of `K`.** With `δ := ε / (2 * L)` when `L > 0` (and the trivial single-
  piece net when `L = 0`, where `f` is constant on `K`'s component / the estimate is immediate), cover
  `K` by finitely many open `δ`-balls centred at points of `K`.

Strategy: `Metric.finite_cover_balls_of_compact hK` (or `IsCompact.elim_finite_subcover` on
`⋃ x ∈ K, Metric.ball x δ`) gives a `Finset` `t ⊆ K` with `K ⊆ ⋃ x ∈ t, Metric.ball x δ`. Reindex `t`
(nonempty — handle empty `K` as a degenerate base with any single affine piece, e.g. `a = 0`,
`b = 0`, both bounds trivial since `∀ y ∈ (∅)` is vacuous and `maxAffine ≤ f` is one tangent plane)
as `Fin (n + 1)` via `Finset.equivFin` / list enumeration, defining `x : Fin (n+1) → (Fin d → ℝ)`.

- [ ] **Step 4: Assemble the two bounds.** Set `a i := gradVec f (x i)`,
  `b i := f (x i) - gradVec f (x i) ⬝ᵥ x i`, so `dotAffine (a i) (b i)` is the tangent plane at `x i`.

  - Minorant `∀ y, maxAffine n a b y ≤ f y`: `maxAffine_le` + `tangent_le` at each `x i` (T3).
  - Uniform `∀ y ∈ K, f y - maxAffine n a b y ≤ ε`: given `y ∈ K`, get a net index `i` with
    `y ∈ Metric.ball (x i) δ` (`‖y - x i‖ < δ`). Then
    `f y - maxAffine n a b y ≤ f y - dotAffine (a i) (b i) y` (`le_maxAffine`, T1)
    `= (f y - f (x i)) - fderiv ℝ f (x i) (y - x i)` (unfold `dotAffine`, `gradVec_dotProduct`,
    `Matrix.dotProduct_sub`)
    `≤ L‖y - x i‖ + L‖y - x i‖` (Lipschitz upper + the gradient/reflection bound from Step 2)
    `≤ 2 * L * δ = ε`. Close with `nlinarith`/`linarith` + the ball bound.

```lean
theorem maxTangent_approx {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ),
      (∀ y, maxAffine n a b y ≤ f y) ∧ ∀ y ∈ K, f y - maxAffine n a b y ≤ ε
```

- [ ] **Step 5: Build + verify + commit.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Density`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Density.lean
git commit -m "feat(amos): uniform max-of-tangent-plane approximation (UAP T4)"
```

> If Step 2's Lipschitz/gradient bound or Step 3's finite-net extraction turns out research-grade
> (e.g. an operator-norm bound genuinely missing and the reflection fallback also blocked), STOP and
> report `NEEDS_CONTEXT` with the precise missing fact — do NOT `sorry` or weaken the statement.

---

## Task 5: Headline `icnn_approximation` + wire (re-export, gate)

**Files:**
- Modify: `NeuralNetworkProofs/UniversalApproximation/Amos/Approx/Density.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation/Amos.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation.lean`
- Modify: `NeuralNetworkProofs.lean`
- Modify: `scripts/check_sorry_free.lean`

**Interfaces:**
- Consumes: `maxAffine_isICNN` (T2), `maxTangent_approx` (T4).
- Produces: `icnn_approximation` (headline, signature below).

- [ ] **Step 1: The headline (append to Density.lean).**

```lean
/-- **Universal approximation.** A convex, differentiable function is uniformly approximated on any
compact set by a fully input-convex network (with nonnegative propagation weights and convex
nondecreasing activations). -/
theorem icnn_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ ∀ y ∈ K, |N.toFun y - f y| ≤ ε := by
  obtain ⟨n, a, b, hle, hunif⟩ := maxTangent_approx hf hd hK hε
  obtain ⟨N, hNconv, hNeq⟩ := maxAffine_isICNN a b
  refine ⟨N, hNconv, fun y hy => ?_⟩
  rw [hNeq]
  -- N.toFun y = maxAffine n a b y; |maxAffine - f| ≤ ε from hle (≤ 0 side) and hunif (≥ -ε side)
  have h1 : maxAffine n a b y - f y ≤ 0 := sub_nonpos.mpr (hle y)
  have h2 : f y - maxAffine n a b y ≤ ε := hunif y hy
  rw [abs_le]; constructor <;> [linarith; linarith]
```

- [ ] **Step 2: Build Density.**

Run: `lake build NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Density`
Expected: green.

- [ ] **Step 3: Re-export in `Amos.lean`.** Add imports for the three new `Approx.*` files alongside
  the existing `Amos.Defs`/`Activation`/`Convex` imports (read the file; match its style).

```lean
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Tangent
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Density
```
Update the module docstring to mention the UAP headline `icnn_approximation` (soundness + UAP).

- [ ] **Step 4: Aggregator + root docstrings.** In `UniversalApproximation.lean` and
  `NeuralNetworkProofs.lean`, add a bullet for `icnn_approximation` to the Amos description (no new
  aggregator import needed — `Amos.lean` re-exports the new files). Match existing bullet style; keep
  ≤ 100 cp.

- [ ] **Step 5: Sorry-free gate.** In `scripts/check_sorry_free.lean`, add
  `#print axioms UniversalApproximation.Amos.icnn_approximation` next to the existing `icnn_convex`
  line (match the file's existing pattern; ensure the file `open`s or fully-qualifies the name as the
  neighbors do).

- [ ] **Step 6: Full build + gate.**

Run: `lake build`
Expected: green (serialize per CLAUDE.md if EMFILE).
Run: `lake env lean scripts/check_sorry_free.lean`
Expected: `icnn_approximation` line reports `[propext, Classical.choice, Quot.sound]`; grep the output
for `sorryAx` → none.

- [ ] **Step 7: Commit.**

```bash
git add NeuralNetworkProofs/ scripts/check_sorry_free.lean
git commit -m "feat(amos): icnn_approximation headline + wire into aggregator/gate (UAP T5)"
```

---

## Task 6: Docs — README, CLAUDE, blueprint, site

**Files:**
- Modify: `README.md`
- Modify: `CLAUDE.md`
- Modify: `blueprint/src/chapter/amos.tex`
- Modify: `blueprint/src/chapter/intro.tex`
- Modify: `site/index.html`

**Interfaces:** none (docs only). Frame: Amos now has **soundness and UAP** (for differentiable
convex functions); the general non-differentiable case remains forthcoming.

- [ ] **Step 1: README.** In the Amos development entry, state the convex UAP is now proved
  (`…Amos.icnn_approximation`: convex differentiable functions are uniformly approximable on compacts),
  soundness `icnn_convex` retained; note general non-differentiable case forthcoming. Match the phrasing
  of the other six entries.

- [ ] **Step 2: CLAUDE.md.** Update the Amos bullet under "What this is" and the layout-table row to
  say soundness **and** UAP (differentiable convex; general case forthcoming). Update the headline
  list to include `…Amos.icnn_approximation`. Keep the "six developments" count (unchanged — this
  extends Amos, does not add a development).

- [ ] **Step 3: Blueprint `amos.tex`.** Add a theorem node for the UAP with
  `\lean{UniversalApproximation.Amos.icnn_approximation}` + `\leanok` + `\uses{}` referencing the
  existing `def:icnn` node and (optionally, if nodes are added) the max-affine / tangent lemmas. Read
  the existing chapter to match its `\begin{theorem}\label{…}` style. Prose: convex differentiable `f`,
  max of tangent planes over an ε-net, realized as a nonneg-weight ReLU ICNN.

- [ ] **Step 4: Blueprint `intro.tex`.** Update the Amos bullet: soundness and universal approximation
  (differentiable convex) formalized; general case forthcoming. Keep "six developments".

- [ ] **Step 5: Site card.** In `site/index.html`, update the "Amos et al. (2017)" card text to:
  ICNN soundness **and** convex universal approximation formalized (differentiable convex; general
  case forthcoming). Keep the arXiv link.

- [ ] **Step 6: Blueprint build check.**

Run (from repo root, if the blueprint toolchain is set up per CONTRIBUTING): `leanblueprint web`
then `lake exe checkdecls blueprint/lean_decls`
Expected: the new `\lean{…icnn_approximation}` node resolves; checkdecls exits 0. If the blueprint
toolchain is unavailable in the environment, verify the `\lean{}` name matches the exact theorem path
by grep and note that CI runs the faithfulness gate.

- [ ] **Step 7: Consistency grep + commit.**

Run: `grep -rn "forthcoming" README.md CLAUDE.md blueprint/ site/ | grep -i amos` — confirm no stale
"convex UAP forthcoming" claim remains for Amos (only the general non-differentiable case is forthcoming).
```bash
git add README.md CLAUDE.md blueprint/ site/
git commit -m "docs(amos): document ICNN convex UAP across README/CLAUDE/blueprint/site (UAP T6)"
```

---

## Self-Review

**Spec coverage:** §3 headline → T5. §4 Pillar A → T1+T2; Pillar B → T3; Pillar C → T4; compose → T5.
§5 file layout → T1–T4 files + T5 re-export. §6 docs → T5 (aggregator/root/gate) + T6 (README/CLAUDE/
blueprint/site). §7 verification → T5 Step 6, T6 Step 6. §8 feasibility (NEEDS_CONTEXT escape) → T4
callout. §9 non-goals → not implemented by design (recorded). All covered.

**Type consistency:** `dotAffine`/`maxAffine`/`maxNet`/`maxNet_isConvex` (T1) consumed with identical
signatures in T2/T4. `maxAffine_isICNN` returns `N.toFun = fun y => maxAffine n a b y` (T2) and T5
`rw [hNeq]` matches. `gradVec`/`tangent_le` (T3) consumed in T4 Step 4. `maxTangent_approx` return
tuple `(n, a, b, hle, hunif)` (T4) destructured identically in T5 Step 1. `icnn_approximation`
signature identical in T5 Step 1 and spec §3.

**Placeholder scan:** No "TBD/TODO". Proof strategies name concrete Mathlib lemmas; a few exact lemma
*forms* are explicitly "pinned during implementation" (`le_slope_of_hasDerivAt` vs mean-value variant;
the operator-norm-vs-reflection choice in T4 Step 2; the finite-cover lemma) — these are genuine
proof-search choices with named candidates and a stated fallback, not hidden work. The one structural
degree of freedom (peel direction of `maxNetTail`, T1 Step 6 / T2 Step 1) is called out with the
resolution rule.
