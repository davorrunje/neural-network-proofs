# Partial-monotone UAP on general box domains — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize `UniversalApproximation.Runje.partial_monotone_approximation` from the unit cube
to an arbitrary non-degenerate box, via an affine change of variables — the new headline
`partial_monotone_approximation_box`.

**Architecture:** An affine coordinatewise rescaling `cubeOfBox`/`boxOfCube` between a box `[a,b]` and
the unit cube. Two structural closure lemmas — `genSpanPi` is closed under affine input precomposition
(feature block), and a `MonoNet` gains a coordinatewise-suffix rescaling by prepending an
identity-activation positive-diagonal layer (monotone block). The headline pulls `f` back to the unit
cube, applies the existing theorem, and folds the rescalings into the resulting network.

**Tech Stack:** Lean 4 + Mathlib. Builds on the merged Runje development (`partial_monotone_approximation`,
`PartMonoNet`, `MonoNet`, `ActStack`, `NeuralNetwork.Layer`, `genSpanPi`).

## Global Constraints

- Line length ≤ 100 codepoints (Mathlib glyphs = 1 cp; measure with `python3 -c "print(len(line))"`).
- No `sorry`/`admit`. A research-grade blocker is reported `NEEDS_CONTEXT` — never hidden, never
  worked around by weakening a theorem statement.
- Minimal precise imports (no blanket `import Mathlib`); confirm any import set by a clean build.
- Frozen (must NOT change statement/signature): `partial_monotone_approximation` (the cube version —
  it is the special case `a=0,b=1`), and every other development's headline (Cybenko, Leshno, M-R,
  Sartor, Runje deep-mono/deep-partmono, Amos `icnn_convex`/`icnn_approximation`).
- Sorry-free gate: every headline reports exactly `[propext, Classical.choice, Quot.sound]`.
- `#print axioms` reads the compiled olean — rebuild (`lake build`) before trusting it.
- Namespace: everything new lives in `namespace UniversalApproximation.Runje`.
- Branch: `feat/runje-partmono-box-domain` (already created off `main`).
- The "test" for a Lean task = the target decls elaborate, `lake build <module>` is green, and (where
  a headline is added) the sorry-free gate reports it axiom-clean. This repo has no unit-test
  framework and does not use `example`s as tests (Mathlib convention) — do not add them.

### Consumed API (verbatim — consume, do not modify)

```lean
-- NeuralNetworkProofs/NeuralNetwork/Network.lean
structure NeuralNetwork.Layer (a b : ℕ) where
  W : Matrix (Fin b) (Fin a) ℝ
  c : Fin b → ℝ
def NeuralNetwork.Layer.toFun (σ : ℝ → ℝ) {a b} (L : Layer a b) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun i => σ ((L.W.mulVec x) i + L.c i)
-- Monotone/Defs.lean
inductive ActStack : ℕ → ℕ → Type
  | nil (n : ℕ) : ActStack n n
  | cons {a b c} (L : NeuralNetwork.Layer a b) (σ : ℝ → ℝ) (rest : ActStack b c) : ActStack a c
def ActStack.toFun … | .cons L σ rest, x => rest.toFun (L.toFun σ x)
def ActStack.IsMonotone … | .cons L σ rest => (Monotone σ ∧ ∀ i j, 0 ≤ L.W i j) ∧ rest.IsMonotone
structure MonoNet (d : ℕ) where
  width : ℕ ; stack : ActStack d width ; readW : Fin width → ℝ ; readBias : ℝ
def MonoNet.toFun {d} (N : MonoNet d) (x) : ℝ := (∑ i, N.readW i * N.stack.toFun x i) + N.readBias
def MonoNet.IsMonotone {d} (N : MonoNet d) : Prop := N.stack.IsMonotone ∧ ∀ i, 0 ≤ N.readW i
-- Runje/Embedding.lean
def genFunPi (σ : ℝ → ℝ) {df} (w : Fin df → ℝ) (b : ℝ) : (Fin df → ℝ) → ℝ :=
  fun x => σ ((∑ c, w c * x c) + b)
def genSpanPi (σ : ℝ → ℝ) (df : ℕ) : Submodule ℝ ((Fin df → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : (Fin df → ℝ) × ℝ => genFunPi σ wb.1 wb.2)
-- Runje/Defs.lean
structure PartMonoNet (df dm : ℕ) where
  embWidth : ℕ ; emb : (Fin df → ℝ) → (Fin embWidth → ℝ) ; mono : MonoNet (embWidth + dm)
def PartMonoNet.toFun {df dm} (P) (u) (x) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)
-- Runje/Approximation.lean : the frozen cube headline (special case a=0,b=1)
theorem partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2) (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
    (hmono : ∀ u ∈ Set.Icc (0:Fin df→ℝ) 1, ∀ ⦃x y⦄, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
        x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0:Fin df→ℝ) 1, ∀ x ∈ Set.Icc (0:Fin dm→ℝ) 1, |P.toFun u x - f u x| ≤ ε
```

---

## File Structure

- `NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean` — `cubeOfBox`/`boxOfCube` + their
  lemmas (T1); `genSpanPi_comp_cubeOfBox` (T2); `MonoNet.rescaleSuffix` + `_isMonotone` + `_toFun`
  (T3).
- `NeuralNetworkProofs/UniversalApproximation/Runje/PartMonoBox.lean` — headline
  `partial_monotone_approximation_box` (T4).
- Modify `NeuralNetworkProofs/UniversalApproximation/Runje.lean` (re-export),
  `NeuralNetworkProofs/UniversalApproximation.lean` + `NeuralNetworkProofs.lean` (docstrings),
  `scripts/check_sorry_free.lean` (gate) (T4).
- Modify `README.md`, `CLAUDE.md`, `blueprint/src/chapter/runje.tex` (T5).

Notation: `open scoped Matrix` for `Matrix.mulVec`/`Matrix.diagonal`. Boxes are `Set.Icc a b` for
`a b : Fin d → ℝ` under the coordinatewise (Pi) order.

---

## Task 1: BoxDomain — affine box↔cube rescaling maps

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean`

**Interfaces:**
- Produces:
  - `cubeOfBox {d} (a b : Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun j => (x j - a j)/(b j - a j)`
  - `boxOfCube {d} (a b : Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun j => a j + (b j - a j) * x j`
  - `boxOfCube_cubeOfBox`, `cubeOfBox_boxOfCube` (mutual inverses, given `∀ j, a j < b j`)
  - `cubeOfBox_mem` (`x ∈ Icc a b → cubeOfBox a b x ∈ Icc 0 1`), `boxOfCube_mem`
  - `continuous_boxOfCube`, `monotone_boxOfCube`

- [ ] **Step 1: Header + imports + namespace.**

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs

/-!
# Affine box↔cube rescaling and the closure lemmas for the general-box partial-monotone UAP

`cubeOfBox a b` sends the box `Set.Icc a b` (non-degenerate: `a j < b j`) coordinatewise-affinely
onto the unit cube `Set.Icc 0 1`; `boxOfCube a b` is its inverse. Both are increasing and
continuous. This file also proves the two structural closure lemmas used by `PartMonoBox.lean`:
`genSpanPi` is closed under affine input precomposition, and a `MonoNet` gains a coordinatewise
suffix rescaling by prepending an identity-activation positive-diagonal layer.
-/

namespace UniversalApproximation.Runje

open scoped Matrix
```

- [ ] **Step 2: The two maps.**

```lean
/-- Affine map sending the box `Set.Icc a b` onto the unit cube, coordinatewise. -/
def cubeOfBox {d : ℕ} (a b x : Fin d → ℝ) : Fin d → ℝ := fun j => (x j - a j) / (b j - a j)

/-- Inverse affine map sending the unit cube onto the box `Set.Icc a b`, coordinatewise. -/
def boxOfCube {d : ℕ} (a b x : Fin d → ℝ) : Fin d → ℝ := fun j => a j + (b j - a j) * x j
```

- [ ] **Step 3: Inverses.** Use `sub_pos.mpr (hab j)` to get `b j - a j ≠ 0`, then `field_simp`/`ring`.

```lean
theorem boxOfCube_cubeOfBox {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) (x) :
    boxOfCube a b (cubeOfBox a b x) = x := by
  funext j; simp only [boxOfCube, cubeOfBox]
  have : b j - a j ≠ 0 := ne_of_gt (sub_pos.mpr (hab j))
  field_simp
theorem cubeOfBox_boxOfCube {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) (x) :
    cubeOfBox a b (boxOfCube a b x) = x := by
  funext j; simp only [boxOfCube, cubeOfBox]
  have : b j - a j ≠ 0 := ne_of_gt (sub_pos.mpr (hab j))
  field_simp
```

- [ ] **Step 4: Icc membership.** Use `Set.mem_Icc`, `Pi.le_def`, and per-coordinate bounds. For
  `cubeOfBox_mem`: `0 ≤ (x j - a j)/(b j - a j)` by `div_nonneg` (`sub_nonneg`), and `… ≤ 1` by
  `div_le_one (sub_pos.mpr (hab j))` from `x j - a j ≤ b j - a j`. For `boxOfCube_mem`: from
  `x̃ j ∈ [0,1]`, `a j ≤ a j + (b j - a j) * x̃ j` (`mul_nonneg`) and `… ≤ b j` (`(b j-a j)*x̃ j ≤
  (b j-a j)*1`).

```lean
theorem cubeOfBox_mem {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) {x}
    (hx : x ∈ Set.Icc a b) : cubeOfBox a b x ∈ Set.Icc (0 : Fin d → ℝ) 1
theorem boxOfCube_mem {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) {x}
    (hx : x ∈ Set.Icc (0 : Fin d → ℝ) 1) : boxOfCube a b x ∈ Set.Icc a b
```

- [ ] **Step 5: Continuity + monotonicity.** `boxOfCube` is continuous (`continuity`/`fun_prop`, or
  `continuous_pi` + each coord `Continuous.add`/`Continuous.mul` of `continuous_const`/`continuous_apply`).
  `monotone_boxOfCube`: `x̃ ≤ ỹ` (Pi order) ⇒ each coord `a j + (b j-a j) x̃ j ≤ a j + (b j-a j) ỹ j`
  by `add_le_add_left`/`mul_le_mul_of_nonneg_left` with `0 ≤ b j - a j` from `(hab j).le`.

```lean
theorem continuous_boxOfCube {d} (a b : Fin d → ℝ) : Continuous (boxOfCube a b)
theorem monotone_boxOfCube {d} {a b : Fin d → ℝ} (hab : ∀ j, a j < b j) :
    Monotone (boxOfCube a b)
```

- [ ] **Step 6: Build + verify + commit.**
Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean
git commit -m "feat(runje): affine box<->cube rescaling maps (box-domain T1)"
```

---

## Task 2: BoxDomain — `genSpanPi` closed under affine precomposition

**Files:**
- Modify: `NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean`

**Interfaces:**
- Consumes: `cubeOfBox` (T1); `genSpanPi`, `genFunPi` (Embedding.lean).
- Produces:
  - `genSpanPi_comp_cubeOfBox {σ df} {aF bF : Fin df → ℝ} (hab : ∀ j, aF j < bF j)`
    `{g} (hg : g ∈ genSpanPi σ df) : (fun u => g (cubeOfBox aF bF u)) ∈ genSpanPi σ df`

- [ ] **Step 1: Generator-image lemma.** A single ridge unit precomposed with `cubeOfBox` is another
  ridge unit. With `w' c := w c / (bF c - aF c)` and `b' := b - ∑ c, w c * aF c / (bF c - aF c)`:

```lean
theorem genFunPi_comp_cubeOfBox {σ : ℝ → ℝ} {df} {aF bF : Fin df → ℝ}
    (w : Fin df → ℝ) (b : ℝ) :
    (fun u => genFunPi σ w b (cubeOfBox aF bF u))
      = genFunPi σ (fun c => w c / (bF c - aF c))
          (b - ∑ c, w c * aF c / (bF c - aF c))
```

Strategy: `funext u`; unfold `genFunPi`, `cubeOfBox`. The argument of `σ` on the left is
`∑ c, w c * ((u c - aF c)/(bF c - aF c)) + b`; distribute
`w c * ((u c - aF c)/(bF c - aF c)) = (w c/(bF c - aF c)) * u c - w c * aF c/(bF c - aF c)`
(`mul_div_assoc`, `sub_div`, `mul_sub`), then `Finset.sum_sub_distrib` and rearrange to
`∑ c, (w c/(bF c-aF c)) * u c + (b - ∑ c, w c*aF c/(bF c-aF c))`. Close with `ring`/`Finset.sum_congr`
+ `linarith`-free algebra. (No `hab` needed — pure algebra, division by zero is harmless here since
we only need the functional identity, but you MAY assume nothing about `bF c - aF c`.)

- [ ] **Step 2: The closure lemma via the pullback linear map.** Precomposition
  `LinearMap.funLeft ℝ ℝ (cubeOfBox aF bF) : ((Fin df→ℝ)→ℝ) →ₗ[ℝ] ((Fin df→ℝ)→ℝ)` satisfies
  `funLeft _ _ φ g = fun u => g (φ u)` (`LinearMap.funLeft_apply`).

```lean
theorem genSpanPi_comp_cubeOfBox {σ : ℝ → ℝ} {df} {aF bF : Fin df → ℝ}
    (hab : ∀ j, aF j < bF j) {g : (Fin df → ℝ) → ℝ} (hg : g ∈ genSpanPi σ df) :
    (fun u => g (cubeOfBox aF bF u)) ∈ genSpanPi σ df := by
  have hmap : Submodule.map (LinearMap.funLeft ℝ ℝ (cubeOfBox aF bF)) (genSpanPi σ df)
      ≤ genSpanPi σ df := by
    rw [genSpanPi, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨wb, rfl⟩, rfl⟩
    -- image of a generator is genFunPi σ w' b', a generator, hence in the span
    rw [show (LinearMap.funLeft ℝ ℝ (cubeOfBox aF bF)) (genFunPi σ wb.1 wb.2)
          = (fun u => genFunPi σ wb.1 wb.2 (cubeOfBox aF bF u)) from rfl,
        genFunPi_comp_cubeOfBox wb.1 wb.2]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  exact hmap ⟨g, hg, rfl⟩
```
Pin the exact `LinearMap.funLeft` name/argument order and `Submodule.map_span`/`Submodule.span_le`
forms during implementation with the lean tools; the `Submodule.subset_span` witness is the pair
`(fun c => wb.1 c/(bF c-aF c), wb.2 - ∑ …)`. If `funLeft` is awkward, an equivalent route is
`Submodule.span_induction hg` closing the generator/zero/add/smul cases (comp distributes over
`+`/`•` pointwise).

- [ ] **Step 3: Build + verify + commit.**
Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean
git commit -m "feat(runje): genSpanPi closed under affine precomposition (box-domain T2)"
```

---

## Task 3: BoxDomain — `MonoNet.rescaleSuffix`

**Files:**
- Modify: `NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean`

**Interfaces:**
- Consumes: `MonoNet`, `ActStack`, `NeuralNetwork.Layer`, `Matrix.diagonal`, `Fin.addCases`/`Fin.append`.
- Produces:
  - `MonoNet.rescaleSuffix {p q} (N : MonoNet (p + q)) (s t : Fin q → ℝ) : MonoNet (p + q)`
  - `MonoNet.rescaleSuffix_isMonotone {p q N s t} (hN : N.IsMonotone) (hs : ∀ j, 0 ≤ s j) :`
    `(N.rescaleSuffix s t).IsMonotone`
  - `MonoNet.rescaleSuffix_toFun {p q} (N : MonoNet (p + q)) (s t) (z : Fin p → ℝ) (x : Fin q → ℝ) :`
    `(N.rescaleSuffix s t).toFun (Fin.append z x) = N.toFun (Fin.append z (fun j => s j * x j + t j))`

- [ ] **Step 1: The construction.** Prepend an identity-activation, positive-diagonal layer.

```lean
/-- The layer `(z, x) ↦ (z, s ⊙ x + t)`: identity on the `p` prefix, affine on the `q` suffix. -/
def rescaleSuffixLayer {p q : ℕ} (s t : Fin q → ℝ) : NeuralNetwork.Layer (p + q) (p + q) where
  W := Matrix.diagonal (Fin.addCases (fun _ : Fin p => (1 : ℝ)) s)
  c := Fin.addCases (fun _ : Fin p => (0 : ℝ)) t

/-- Rescale a monotone network's last `q` (monotone-block) inputs by the coordinatewise increasing
affine map `x ↦ s ⊙ x + t`, by prepending an identity-activation positive-diagonal layer. -/
def MonoNet.rescaleSuffix {p q : ℕ} (N : MonoNet (p + q)) (s t : Fin q → ℝ) : MonoNet (p + q) where
  width := N.width
  stack := .cons (rescaleSuffixLayer s t) id N.stack
  readW := N.readW
  readBias := N.readBias
```

- [ ] **Step 2: The layer evaluation lemma.** `Matrix.mulVec_diagonal` +
  `Fin.append`/`Fin.addCases` split.

```lean
theorem rescaleSuffixLayer_toFun {p q} (s t : Fin q → ℝ) (z : Fin p → ℝ) (x : Fin q → ℝ) :
    (rescaleSuffixLayer s t).toFun id (Fin.append z x)
      = Fin.append z (fun j => s j * x j + t j)
```
Strategy: `funext k`; `simp only [NeuralNetwork.Layer.toFun, rescaleSuffixLayer, id_eq]`; rewrite
`Matrix.mulVec_diagonal` (`(diagonal d).mulVec v k = d k * v k`); then `refine Fin.addCases ?_ ?_ k`.
Left `i : Fin p`: `Fin.addCases_left`, `Fin.append_left` give `1 * z i + 0 = z i` (`Fin.append_left`
on the RHS). Right `j : Fin q`: `Fin.addCases_right`, `Fin.append_right` give
`s j * x j + t j`. Pin exact `Matrix.mulVec_diagonal` and `Fin.addCases_left/right`,
`Fin.append_left/right` names during implementation.

- [ ] **Step 3: `rescaleSuffix_toFun`.** Unfold `MonoNet.toFun` + `MonoNet.rescaleSuffix` +
  `ActStack.toFun` on the prepended `cons`, then rewrite `rescaleSuffixLayer_toFun`; the read-out is
  unchanged.

```lean
theorem MonoNet.rescaleSuffix_toFun {p q} (N : MonoNet (p + q)) (s t : Fin q → ℝ)
    (z : Fin p → ℝ) (x : Fin q → ℝ) :
    (N.rescaleSuffix s t).toFun (Fin.append z x)
      = N.toFun (Fin.append z (fun j => s j * x j + t j)) := by
  simp only [MonoNet.toFun, MonoNet.rescaleSuffix, ActStack.toFun, rescaleSuffixLayer_toFun]
```

- [ ] **Step 4: `rescaleSuffix_isMonotone`.** The prepended layer: `Monotone id` (`monotone_id`) and
  `0 ≤ (diagonal dvec) i j` for all `i j` (`Matrix.diagonal_apply`; `split_ifs`; off-diagonal `0`,
  diagonal `Fin.addCases (fun _ => 1) s i ≥ 0` — `1 ≥ 0` on the prefix, `s j ≥ 0` via `hs` on the
  suffix, discharged with `Fin.addCases`). `N.stack.IsMonotone` from `hN.1`, `readW ≥ 0` from `hN.2`.

```lean
theorem MonoNet.rescaleSuffix_isMonotone {p q} {N : MonoNet (p + q)} {s t : Fin q → ℝ}
    (hN : N.IsMonotone) (hs : ∀ j, 0 ≤ s j) : (N.rescaleSuffix s t).IsMonotone := by
  refine ⟨⟨⟨monotone_id, ?_⟩, hN.1⟩, hN.2⟩
  intro i j
  rw [rescaleSuffixLayer, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; refine Fin.addCases (fun _ => ?_) (fun k => ?_) i <;> simp [hs]
  · exact le_refl 0
```
(Pin the exact nesting of `MonoNet.IsMonotone`/`ActStack.IsMonotone` and the `Fin.addCases` simp set
against the live goal.)

- [ ] **Step 5: Build + verify + commit.**
Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain`; `grep sorry` → none.
```bash
git add NeuralNetworkProofs/UniversalApproximation/Runje/BoxDomain.lean
git commit -m "feat(runje): MonoNet suffix-block affine rescaling combinator (box-domain T3)"
```

---

## Task 4: PartMonoBox — the headline + wiring

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation/Runje/PartMonoBox.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation/Runje.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation.lean`
- Modify: `NeuralNetworkProofs.lean`
- Modify: `scripts/check_sorry_free.lean`

**Interfaces:**
- Consumes: `partial_monotone_approximation` (Approximation.lean); `cubeOfBox`/`boxOfCube` + lemmas
  (T1); `genSpanPi_comp_cubeOfBox` (T2); `MonoNet.rescaleSuffix` + `_isMonotone` + `_toFun` (T3);
  `PartMonoNet`, `clamp01`.
- Produces: `partial_monotone_approximation_box` (headline, signature in Step 2).

- [ ] **Step 1: Header + imports + namespace.**
```lean
/- (Apache header) -/
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation
import NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain

/-!
# Partial-monotone universal approximation on general box domains (Runje et al.)

`partial_monotone_approximation_box` generalizes the unit-cube `partial_monotone_approximation`
(a secondary result of the Deep Constrained Monotonic Neural Networks development) to an arbitrary
non-degenerate box `[aF, bF] × [aM, bM]`, by an affine change of variables: pull `f` back to the
unit cube, apply the cube theorem, and fold the rescalings into the network (the feature embedding
via `genSpanPi_comp_cubeOfBox`, the monotone block via `MonoNet.rescaleSuffix`).
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Leshno
```

- [ ] **Step 2: The headline.**
```lean
theorem partial_monotone_approximation_box {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (aF bF : Fin df → ℝ) (haF : ∀ j, aF j < bF j)
    (aM bM : Fin dm → ℝ) (haM : ∀ j, aM j < bM j)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2) (Set.Icc aF bF ×ˢ Set.Icc aM bM))
    (hmono : ∀ u ∈ Set.Icc aF bF, ∀ ⦃x y⦄, x ∈ Set.Icc aM bM → y ∈ Set.Icc aM bM →
        x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc aF bF, ∀ x ∈ Set.Icc aM bM, |P.toFun u x - f u x| ≤ ε
```

- [ ] **Step 3: Proof — the pulled-back target `f̃` and its hypotheses.**
```lean
  set ftil : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ :=
    fun u x => f (boxOfCube aF bF u) (boxOfCube aM bM x) with hftil
```
  - Continuity: `fun p => ftil p.1 p.2 = (fun q => f q.1 q.2) ∘ (fun p => (boxOfCube aF bF p.1,
    boxOfCube aM bM p.2))`. The inner map is continuous (`continuous_boxOfCube` on each factor,
    `Continuous.prodMk`), and maps the unit-cube product into `Icc aF bF ×ˢ Icc aM bM`
    (`boxOfCube_mem` on each factor, `Set.MapsTo`). Conclude `ContinuousOn (fun p => ftil p.1 p.2)
    (Set.Icc 0 1 ×ˢ Set.Icc 0 1)` by `hf.comp hcont hmaps`.
  - Monotone in the monotone block: for `u ∈ Icc 0 1`, `x y ∈ Icc 0 1`, `x ≤ y`:
    `boxOfCube aF bF u ∈ Icc aF bF` and `boxOfCube aM bM x, y ∈ Icc aM bM` (`boxOfCube_mem`), and
    `boxOfCube aM bM x ≤ boxOfCube aM bM y` (`monotone_boxOfCube haM`); apply `hmono`.

- [ ] **Step 4: Proof — apply the cube theorem and build `P`.**
```lean
  obtain ⟨Pt, hPtmono, hPtemb, hPtapprox⟩ :=
    partial_monotone_approximation σ hσ hnp ftil hftil_cont hftil_mono hε
  set s : Fin dm → ℝ := fun j => 1 / (bM j - aM j) with hs
  set t : Fin dm → ℝ := fun j => - aM j / (bM j - aM j) with ht
  refine ⟨⟨Pt.embWidth, fun u => Pt.emb (cubeOfBox aF bF u), Pt.mono.rescaleSuffix s t⟩,
    Pt.mono.rescaleSuffix_isMonotone hPtmono (fun j => ?_), fun i => ?_, ?_⟩
```
  - `0 ≤ s j`: `s j = 1/(bM j - aM j)`, denominator `> 0` from `haM j`; `le_of_lt (by positivity)`
    / `div_nonneg`.
  - emb membership: `(fun u => (⟨…⟩ : PartMonoNet df dm).emb u i)` reduces to
    `fun u => Pt.emb (cubeOfBox aF bF u) i = (fun u' => Pt.emb u' i) ∘ cubeOfBox aF bF`; apply
    `genSpanPi_comp_cubeOfBox haF (hPtemb i)`.

- [ ] **Step 5: Proof — the uniform bound (the `toFun` identity + transport).**
```lean
  intro u hu x hx
```
  Key facts:
  - `s ⊙ x + t = cubeOfBox aM bM x`: pointwise `1/(bM j-aM j) * x j + (-aM j/(bM j-aM j))
    = (x j - aM j)/(bM j-aM j)` (`field_simp`/`ring`, denom ≠ 0 from `haM`). Call it `hst`.
  - `(⟨…⟩ : PartMonoNet df dm).toFun u x = Pt.toFun (cubeOfBox aF bF u) (cubeOfBox aM bM x)`:
    unfold `PartMonoNet.toFun`; the mono field is `Pt.mono.rescaleSuffix s t`; apply
    `MonoNet.rescaleSuffix_toFun` with `z = fun i => clamp01 (Pt.emb (cubeOfBox aF bF u) i)` and this
    `x`; rewrite `hst` to turn `s ⊙ x + t` into `cubeOfBox aM bM x`; the result is exactly
    `Pt.toFun (cubeOfBox aF bF u) (cubeOfBox aM bM x)` (defeq unfold of `Pt.toFun`).
  - `ftil (cubeOfBox aF bF u) (cubeOfBox aM bM x) = f u x`: `boxOfCube_cubeOfBox haF`,
    `boxOfCube_cubeOfBox haM` (round-trip is identity).
  - `cubeOfBox aF bF u ∈ Icc 0 1`, `cubeOfBox aM bM x ∈ Icc 0 1` (`cubeOfBox_mem haF hu`,
    `cubeOfBox_mem haM hx`).
  Combine: `hPtapprox (cubeOfBox aF bF u) (cubeOfBox_mem haF hu) (cubeOfBox aM bM x)
  (cubeOfBox_mem haM hx)` gives `|Pt.toFun … − ftil …| ≤ ε`; rewrite the two identities above to reach
  `|P.toFun u x − f u x| ≤ ε`.

- [ ] **Step 6: Build PartMonoBox.**
Run: `lake build NeuralNetworkProofs.UniversalApproximation.Runje.PartMonoBox`
Expected: green.

- [ ] **Step 7: Wire re-export + docstrings + gate.**
  - `Runje.lean`: add `import NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain` and
    `import …Runje.PartMonoBox` (read the file, match style); add a docstring line for
    `partial_monotone_approximation_box`.
  - `UniversalApproximation.lean` + `NeuralNetworkProofs.lean`: add a one-line bullet under the Runje
    entry for the general-box partial-monotone result (match style, ≤ 100 cp).
  - `scripts/check_sorry_free.lean`: it already `open`s `UniversalApproximation.Runje`; add
    `#print axioms partial_monotone_approximation_box` next to the existing Runje headline lines.

- [ ] **Step 8: Full build + gate.**
Run: `lake build` (serialize per CLAUDE.md if EMFILE).
Run: `lake env lean scripts/check_sorry_free.lean` — confirm `partial_monotone_approximation_box`
reports `[propext, Classical.choice, Quot.sound]`; grep output for `sorryAx` → none; existing
headlines still clean.

- [ ] **Step 9: Commit.**
```bash
git add NeuralNetworkProofs/ scripts/check_sorry_free.lean
git commit -m "feat(runje): partial_monotone_approximation_box headline + wire (box-domain T4)"
```

> If Step 4/5's `toFun` reconciliation or a Mathlib lemma (`LinearMap.funLeft`, `Matrix.mulVec_diagonal`,
> `Submodule.map_span`) genuinely resists after real effort, report `NEEDS_CONTEXT` with the exact goal
> state — do NOT `sorry` or weaken the statement.

---

## Task 5: Docs — README, CLAUDE, blueprint

**Files:**
- Modify: `README.md`, `CLAUDE.md`, `blueprint/src/chapter/runje.tex`

**Interfaces:** none (docs only). Framing: this extends the **secondary** partial-monotone result of
the Runje "Deep Constrained Monotonic Neural Networks" development to general box domains; keep the
primary framing (deep constrained monotone via skip connections) intact. Six developments unchanged.

- [ ] **Step 1: README.** In the Runje entry, note the partial-monotone secondary result now holds on
  general box domains (`…Runje.partial_monotone_approximation_box`), alongside the existing headlines.
  Match the phrasing of the other entries; keep partial monotonicity described as secondary.

- [ ] **Step 2: CLAUDE.md.** In the Runje bullet, add that partial monotonicity is proven on general
  boxes (secondary). Do NOT change the "six developments" count or the primary framing.

- [ ] **Step 3: Blueprint `runje.tex`.** Add a theorem node with
  `\lean{UniversalApproximation.Runje.partial_monotone_approximation_box}` + `\leanok` +
  `\uses{}` referencing the cube partial-monotone node (read the chapter to find its label and match
  the `\begin{theorem}\label{…}`/`\lean`/`\uses` style). Prose: the cube partial-monotone UAP extends
  to any non-degenerate box by an affine change of variables.

- [ ] **Step 4: Blueprint build check.**
Run (if the toolchain is set up): `leanblueprint web` then `lake exe checkdecls blueprint/lean_decls`
Expected: the new node resolves; exit 0. If unavailable, grep-confirm the `\lean{}` name matches the
theorem path and note CI runs the gate.

- [ ] **Step 5: Consistency grep + commit.**
Run: `grep -rn "partial_monotone_approximation_box" README.md CLAUDE.md blueprint/` — confirm present
and consistent.
```bash
git add README.md CLAUDE.md blueprint/
git commit -m "docs(runje): document partial-monotone UAP on general box domains (box-domain T5)"
```

---

## Self-Review

**Spec coverage:** §3 rescaling maps → T1. §4a `genSpanPi_comp_cubeOfBox` → T2. §4b `MonoNet.rescaleSuffix`
→ T3. §5 headline → T4. §6 file layout → T1/T4 files. §7 gate+docstrings → T4 (gate/aggregator/root) +
T5 (README/CLAUDE/blueprint). §9 verification → T4 Step 8. §8 non-goals → not implemented (recorded).
All covered.

**Type consistency:** `cubeOfBox`/`boxOfCube` (T1) reused in T2/T4 with the same
`(a b x : Fin d → ℝ)` signature. `genSpanPi_comp_cubeOfBox` (T2) consumed in T4 Step 4 with `hg :=
hPtemb i`. `MonoNet.rescaleSuffix`/`_isMonotone`/`_toFun` (T3) consumed in T4 Steps 4–5 with `p =
Pt.embWidth`, `q = dm`, the `s,t` defined in T4 Step 4 (`s j = 1/(bM j−aM j)`, `t j =
−aM j/(bM j−aM j)`), and `hst : (fun j => s j * x j + t j) = cubeOfBox aM bM x`. The built `P` has
`embWidth = Pt.embWidth`, `emb = fun u => Pt.emb (cubeOfBox aF bF u)`, `mono = Pt.mono.rescaleSuffix s t`
— matching `PartMonoNet`'s fields. Headline signature identical in T4 Step 2 and spec §5.

**Placeholder scan:** No "TBD/TODO". Proof strategies name concrete Mathlib lemmas; the few "pin the
exact form" notes (`LinearMap.funLeft`, `Matrix.mulVec_diagonal`, `Fin.addCases_left/right`,
`Submodule.map_span`) are genuine proof-search confirmations with named candidates and, where
relevant, a stated fallback (`Submodule.span_induction` for T2) — not hidden work.
