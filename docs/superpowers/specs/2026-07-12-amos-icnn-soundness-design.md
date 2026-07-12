# Input-Convex Neural Networks — soundness (design)

**Date:** 2026-07-12
**Status:** design approved, pending spec review → implementation plan
**Namespace:** `UniversalApproximation.Amos` (new; Amos–Xu–Kolter 2017)

## 1. Goal

Formalize the **fully input-convex neural network (FICNN)** of Amos–Xu–Kolter (2017) and prove
**soundness**: an ICNN with the convexity-inducing constraints denotes a **convex** function of its
input. This is the convex sibling of the constrained-monotone line (`MikulincerReichman`/`Sartor`/
`Runje`): where those constrain weight *signs* + monotone activations to get a *monotone* map, ICNN
constrains the propagation weights nonnegative + **convex, nondecreasing** activations (with an
unconstrained input skip) to get a *convex* map.

## 2. Program context (3 developments, this is #1)

1. **ICNN soundness** — this spec. Fixes the architecture + the "denotes a convex function" theorem.
2. **ICNN UAP** — convex functions are approximable by ICNNs (separate spec/plan; depends on #1's
   structure; carries bespoke convex-analysis density not yet in Mathlib — max-of-affine minorants).
3. **General-compact-domain partial-monotone** — independent monotone-line loop-closer (separate
   cycle).

Getting the architecture faithful now matters because #2 reuses it.

## 3. The FICNN architecture

Input `y ∈ ℝ^d` (`Fin d → ℝ`). Each layer propagates a hidden vector `z` and re-injects the
original input `y`:

```lean
namespace UniversalApproximation.Amos

/-- One FICNN layer `d`-input, `a`→`b` hidden: `z ↦ act (Wz z + Wy y + b)` componentwise, with a
direct (unconstrained) skip `Wy` from the original input `y`. -/
structure ICNNLayer (d a b : ℕ) where
  Wz : Matrix (Fin b) (Fin a) ℝ
  Wy : Matrix (Fin b) (Fin d) ℝ
  bias : Fin b → ℝ
  act : ℝ → ℝ

noncomputable def ICNNLayer.toFun {d a b} (L : ICNNLayer d a b)
    (z : Fin a → ℝ) (y : Fin d → ℝ) : Fin b → ℝ :=
  fun j => L.act ((L.Wz.mulVec z) j + (L.Wy.mulVec y) j + L.bias j)

/-- Convexity constraints: nonnegative propagation weights, convex + nondecreasing activation.
`Wy` (input skip) is unconstrained. -/
def ICNNLayer.IsConvex {d a b} (L : ICNNLayer d a b) : Prop :=
  (∀ i j, 0 ≤ L.Wz i j) ∧ Monotone L.act ∧ ConvexOn ℝ Set.univ L.act

/-- A FICNN as a chain of layers threading the original input `y`. -/
inductive ICNN (d : ℕ) : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ICNN d a a
  | cons : {a b c : ℕ} → ICNNLayer d a b → ICNN d b c → ICNN d a c

/-- Evaluate the chain: `y` is fed to every layer; `z` is threaded. -/
noncomputable def ICNN.eval {d} : {a b : ℕ} → ICNN d a b → (Fin d → ℝ) → (Fin a → ℝ) → (Fin b → ℝ)
  | _, _, .nil, _, z => z
  | _, _, .cons L rest, y, z => rest.eval y (L.toFun z y)

def ICNN.IsConvex {d} : {a b : ℕ} → ICNN d a b → Prop
  | _, _, .nil => True
  | _, _, .cons L rest => L.IsConvex ∧ rest.IsConvex

/-- Scalar FICNN denotation: start from a width-0 hidden vector (so `z₀` contributes nothing — the
first layer is the purely input-affine `act (Wy y + b)`), end at width 1. -/
noncomputable def ICNN.toFun {d} (N : ICNN d 0 1) (y : Fin d → ℝ) : ℝ :=
  N.eval y Fin.elim0 0
```

The width-0 start encodes `z₀ = ∅` faithfully (the first `Wz` is `b×0`, contributing `0`); threading
`y` into *every* layer is the ICNN hallmark and is what makes the UAP (dev 2) reachable.

## 4. Soundness theorem

```lean
theorem icnn_convex {d : ℕ} (N : ICNN d 0 1) (h : N.IsConvex) :
    ConvexOn ℝ Set.univ N.toFun
```

Proof via an induction lemma over the chain:

```lean
theorem ICNN.eval_convexOn {d} : {a b : ℕ} → (N : ICNN d a b) → N.IsConvex →
    (zf : (Fin d → ℝ) → (Fin a → ℝ)) → (∀ i, ConvexOn ℝ Set.univ (fun y => zf y i)) →
    ∀ j, ConvexOn ℝ Set.univ (fun y => N.eval y (zf y) j)
```

- **nil:** `eval y (zf y) = zf y`; coords convex by hypothesis.
- **cons L rest:** the new hidden vector is `zf' y := L.toFun (zf y) y`. Each coordinate
  `L.act ((Wz (zf y))ⱼ + (Wy y)ⱼ + bⱼ)`:
  - `(Wz (zf y))ⱼ = ∑ₖ Wz j k · zf y k` — nonneg (`Wz ≥ 0`) combination of convex coords →
    `ConvexOn.smul` (nonneg scalar) + `ConvexOn.sum`;
  - `(Wy y)ⱼ = ∑ₖ Wy j k · y k` — a linear functional → convex (helper `linear_convexOn`, §7);
    `+ bⱼ` const → `ConvexOn.add`;
  - `L.act ∘ (that)` → `convexOn_comp_univ` (helper, §7): `ConvexOn univ act` + `Monotone act` +
    `ConvexOn univ arg` ⇒ `ConvexOn univ (act ∘ arg)`.
  So each coord of `zf'` is convex; apply the IH to `rest` with `zf'`.

Top level: `N.toFun = fun y => N.eval y Fin.elim0 0`; the width-0 initial `z` has no coordinates, so
the coord-convexity hypothesis is vacuous; `eval_convexOn` at `j = 0` gives `ConvexOn ℝ univ N.toFun`.

## 5. Activations + abstraction

`act` is abstract per layer (`ConvexOn ℝ univ` + `Monotone`); concrete instances proven convex +
monotone (mirrors the Runje abstract-combinator + concrete-instance pattern):

```lean
def relu (x : ℝ) : ℝ := max 0 x
theorem relu_convexOn : ConvexOn ℝ Set.univ relu        -- via convexOn_const.sup convexOn_id / ConvexOn.sup
theorem relu_monotone : Monotone relu
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)
theorem softplus_convexOn : ConvexOn ℝ Set.univ softplus
theorem softplus_monotone : Monotone softplus
theorem id_convexOn : ConvexOn ℝ Set.univ (id : ℝ → ℝ)   -- linear final layer
theorem id_monotone : Monotone (id : ℝ → ℝ)
```

(`softplus` also exists in `Runje/RunjeShankaranarayana.lean`; NOT reused across developments to
avoid cross-dependency — this is a fresh, self-contained instance. Note in the module doc.)

## 6. File layout (`UniversalApproximation/Amos/`)

- `Amos/Defs.lean` — `ICNNLayer`, `ICNN`, `eval`, `IsConvex`, `toFun`.
- `Amos/Activation.lean` — `relu`/`softplus`/`id` convex + monotone.
- `Amos/Convex.lean` — helpers `linear_convexOn`, `convexOn_comp_univ`; `ICNN.eval_convexOn`; the
  headline `icnn_convex`.
- `Amos.lean` — re-export root (docstring credits Amos–Xu–Kolter 2017; headline `icnn_convex`;
  notes ICNN UAP is forthcoming, dev 2).

## 7. Key helper lemmas (the fiddly bits)

- `linear_convexOn (w : Fin d → ℝ) : ConvexOn ℝ Set.univ (fun y => ∑ k, w k * y k)` — a linear
  functional is convex (Jensen with equality; or via `AffineMap`/`ConvexOn.comp_affineMap` on
  `convexOn_id`). Used for the `Wy` input-skip term.
- `convexOn_comp_univ {g : ℝ → ℝ} {f : (Fin d → ℝ) → ℝ}
   (hg : ConvexOn ℝ Set.univ g) (hgm : Monotone g) (hf : ConvexOn ℝ Set.univ f) :
   ConvexOn ℝ Set.univ (g ∘ f)` — wraps Mathlib's `ConvexOn.comp`, which needs `ConvexOn (f '' univ)
   g` + `MonotoneOn g (f '' univ)`: derive the former from `hg` via `ConvexOn.subset` using that the
   range of a convex function is convex (convex ⇒ continuous on `ℝ^d` ⇒ range is an interval), and
   the latter from `hgm.monotoneOn`. This is the one genuinely fiddly lemma; if the range-is-convex
   step is heavy, an acceptable alternative is to require activations `ConvexOn ℝ Set.univ` (already
   assumed) and prove the composite midpoint-convexity directly. Report `NEEDS_CONTEXT` rather than
   weaken if it turns research-grade.

Mathlib support confirmed present: `ConvexOn.comp`, `ConvexOn.comp_affineMap`, `ConvexOn.smul`,
`ConvexOn.add`, `ConvexOn.sum`, `ConvexOn.sup`, `convexOn_id`, `convex_univ`.

## 8. Docs updates (IN SCOPE — not deferred)

Every living-docs surface updated to a **sixth development** (Amos ICNN), framed honestly as
*soundness now, convex UAP forthcoming (dev 2)*:

- **`README.md`** — add an Amos entry to the developments list; note headline
  `…Amos.icnn_convex` and that convex UAP is forthcoming.
- **`CLAUDE.md`** — "Five developments" → "Six developments"; add an Amos bullet ("What this is")
  and a layout-table row (`UniversalApproximation/Amos/` + `Amos.lean` | `…Amos` | Input-Convex
  Neural Networks — soundness; convex UAP forthcoming).
- **`NeuralNetworkProofs.lean` + `UniversalApproximation.lean` (aggregator)** — add the `…Amos`
  import to the aggregator, and the `icnn_convex` headline bullet to both docstrings.
- **Blueprint** — new `blueprint/src/chapter/amos.tex` (ICNN definition + the soundness theorem with
  a `\lean{UniversalApproximation.Amos.icnn_convex}` node + `\uses` for the convex activations),
  `\input` it from `content.tex`, and update `intro.tex`'s development list to **six** (Amos entry).
- **`site/index.html`** — add a sixth card for the Amos ICNN development (the surface that drifted
  before; explicitly updated here).

## 9. Verification (acceptance gate)

`lake build` green; `lake env lean scripts/check_sorry_free.lean` extended with
`UniversalApproximation.Amos.icnn_convex` reporting exactly `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`; blueprint `leanblueprint web` + `lake exe checkdecls blueprint/lean_decls` pass (the new
`\lean{}` node resolves); grep confirms the docs consistently say "six developments" / list Amos.

## 10. Non-goals (recorded follow-ups)

- **ICNN UAP** (dev 2) — the convex-approximation result; needs max-of-affine / convex-minorant
  density (bespoke; not in Mathlib).
- **General-compact-domain partial-monotone** (dev 3).
- Any *training/optimization* claim (empirical; not formalized).
- Partially-input-convex (PICNN) variants — out of scope; FICNN only.

## 11. Risks

- **`convexOn_comp_univ`** (§7) — the range-is-convex step is the one non-mechanical spot; feasible
  (convex ⇒ continuous ⇒ range is an interval), flagged.
- **`ConvexOn` over `Fin d → ℝ`** (the `Pi` normed/ordered instances) — confirm the `ConvexOn ℝ`
  API applies to `Fin d → ℝ` inputs; it should (it's an `AddCommGroup`/`Module ℝ`). Build-confirm.
- **`ICNN` dependent-index induction** (`{a b c}` chain) — mirror `Runje.ResNet`'s inductive style.

## 12. Conventions

Follow CLAUDE.md: line length ≤ 100 codepoints, no `sorry`/`admit`, minimal precise imports,
sorry-free gate. Build serially if a from-scratch rebuild hits EMFILE.
