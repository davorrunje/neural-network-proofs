# Input-Convex Neural Networks — universal approximation (design)

**Date:** 2026-07-12
**Status:** design approved, pending spec review → implementation plan
**Namespace:** `UniversalApproximation.Amos` (extends dev 1; Amos–Xu–Kolter 2017)
**Branch:** `feat/amos-icnn-uap`

## 1. Goal

Formalize **universal approximation** for the fully-input-convex network (FICNN) of dev 1: an ICNN
with the convexity-inducing constraints (`Wz ≥ 0`, convex nondecreasing activations) **uniformly
approximates** any convex, differentiable function on a compact set. This is dev 2 of the
three-development ICNN program; it builds directly on dev 1's `ICNNLayer`/`ICNN`/`eval`/`IsConvex`/
`toFun` and the soundness headline `icnn_convex`.

**Scope decision (recorded).** The result targets **multivariate, differentiable convex**
functions. Mathlib's affine-minorant / subgradient machinery is entirely one-dimensional
(`Mathlib.Analysis.Convex.Deriv`: slopes and left/right derivatives of `f : ℝ → ℝ`); there is **no**
multivariate supporting-hyperplane / subgradient-existence result. Rather than build multivariate
subgradient existence from `geometric_hahn_banach` (a research-grade convex-analysis contribution —
the full non-differentiable case), we assume `f` differentiable and **derive** the multivariate
affine minorant (the tangent plane) from the existing 1-D lemmas by restricting `f` to lines. The
general non-differentiable case is a recorded follow-up (Non-goals §9).

## 2. Program context (3 developments, this is #2)

1. **ICNN soundness** — dev 1, shipped (PR #37): the architecture + `icnn_convex`.
2. **ICNN UAP** — this spec: differentiable convex functions are uniformly approximable by ICNNs.
3. **General-compact-domain partial-monotone** — independent monotone-line loop-closer (later cycle).

## 3. Headline statement

```lean
theorem icnn_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ ∀ y ∈ K, |N.toFun y - f y| ≤ ε
```

- `f` convex and differentiable on **all** of `ℝ^d` (`Fin d → ℝ`); uniform approximation on any
  compact `K`. `K` need not be convex — the tangent planes are global minorants (from convexity on
  `univ`), so the domain only needs compactness for the finite-net step.
- The produced `N` is a genuine dev-1-convex ICNN (`N.IsConvex`), so `icnn_convex` composes: the
  approximant is itself provably convex. This is the point of stating `N.IsConvex` in the conclusion.
- One-sided bound suffices: the approximant `h` satisfies `h ≤ f` (minorant) and `f − h ≤ ε` on `K`,
  hence `|h − f| ≤ ε`.

## 4. Proof architecture — three pillars

### Pillar A — Representability: a finite max of affine functions is a convex ICNN

```lean
/-- The running max of the first `n` affine functions `y ↦ ⟨a i, y⟩ + b i`. -/
noncomputable def maxAffine {d : ℕ} (n : ℕ) (a : Fin n → (Fin d → ℝ)) (b : Fin n → ℝ) :
    (Fin d → ℝ) → ℝ

theorem maxAffine_isICNN {d n : ℕ} (hn : 0 < n) (a : Fin n → (Fin d → ℝ)) (b : Fin n → ℝ) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ N.toFun = maxAffine n a b
```

Construction by the running-max recursion (fits the `Wz ≥ 0` constraint):

```
h₁ = g₁                         -- affine, via the unconstrained input skip Wy + bias
hₖ = gₖ + relu(hₖ₋₁ − gₖ)       -- = max(gₖ, hₖ₋₁) = max(g₁,…,gₖ)
```

where `gᵢ(y) = ⟨aᵢ, y⟩ + bᵢ`. Every **propagation** weight (`Wz`, acting on the running hidden value
`hₖ₋₁`) is `0` or `+1`, hence `≥ 0`; every affine term (`gₖ` and `−gₖ`) rides the **unconstrained**
input skip `Wy` and `bias`; activations are `relu` and `id` — both proven convex + nondecreasing in
dev 1 (`Amos/Activation.lean`), so `IsConvex` holds by construction. The `N.toFun = maxAffine …`
equality is a genuine functional identity (an `induction` on `n` mirroring the `eval` recursion),
NOT a re-statement.

*Largest task; risk is construction/index bookkeeping in the inductive `ICNN` type, not mathematics.*

### Pillar B — Tangent-plane minorant

```lean
theorem convex_diff_tangent_le {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x₀ y : Fin d → ℝ) :
    f x₀ + fderiv ℝ f x₀ (y - x₀) ≤ f y
```

Proof: the restriction `φ t := f (x₀ + t • (y − x₀))` is convex on `ℝ` (composition of `f` with an
affine map — `ConvexOn.comp_affineMap`) and differentiable with `φ' 0 = fderiv ℝ f x₀ (y − x₀)`
(chain rule, `HasFDerivAt.comp` / `fderiv` of an affine map). Convexity of `φ` gives
`φ 0 + φ' 0 · (1 − 0) ≤ φ 1`, i.e. `f x₀ + fderiv ℝ f x₀ (y − x₀) ≤ f y`, via a 1-D `ConvexOn`
tangent lemma (`ConvexOn.le_slope_of_hasDerivAt` / `Convex.mul_sub_le_image_sub_of_le_deriv`, whose
exact form is pinned during planning).

*Moderate risk: the `fderiv`→directional-derivative bridge and the exact 1-D lemma choice.*

### Pillar C — Uniform density via a finite max of tangent planes

```lean
theorem maxTangent_approx {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (a : Fin n → (Fin d → ℝ)) (b : Fin n → ℝ),
      (∀ y, maxAffine n a b y ≤ f y) ∧ (∀ y ∈ K, f y - maxAffine n a b y ≤ ε)
```

Steps:
1. `f` is Lipschitz on a compact neighborhood of `K` with constant `L` (`ConvexOn.locallyLipschitzOn`
   / `locallyLipschitz` in finite dimension + `IsCompact.exists…`), and `‖∇f‖ ≤ L` there.
2. Choose `δ = ε / (2L)` (handle `L = 0` — constant `f` — as a trivial/degenerate case with a single
   affine piece).
3. Extract a finite `δ`-net `{x₁,…,xₙ}` of `K` from compactness (`IsCompact.elim_finite_subcover` of
   the open `δ`-balls, `n ≥ 1` since `ε>0` forces `K` handling; empty `K` is a degenerate base case).
4. `aᵢ := ∇f(xᵢ) = fderiv ℝ f xᵢ` (as a vector via `InnerProductSpace`/`toDual`, or keep the
   functional and feed `Wy` its matrix row), `bᵢ := f(xᵢ) − ⟨∇f(xᵢ), xᵢ⟩`, so
   `gᵢ(y) = f(xᵢ) + ⟨∇f(xᵢ), y − xᵢ⟩` is the tangent plane at `xᵢ`.
5. `maxAffine n a b ≤ f` everywhere: each `gᵢ ≤ f` by Pillar B; max of minorants is a minorant.
6. `f y − maxAffine n a b y ≤ ε` on `K`: pick a net point `xᵢ` with `‖y − xᵢ‖ ≤ δ`; then
   `f y − gᵢ(y) = (f y − f xᵢ) − ⟨∇f(xᵢ), y − xᵢ⟩ ≤ L‖y−xᵢ‖ + L‖y−xᵢ‖ ≤ 2Lδ = ε`, and
   `maxAffine … y ≥ gᵢ(y)`.

*Moderate risk: the finite-net extraction and the `2Lδ` estimate; all pieces are in Mathlib.*

### Headline: compose A + C

`icnn_approximation` = Pillar C gives `(n, a, b)` with the two bounds; Pillar A turns `maxAffine n a b`
into `N : ICNN d 0 1` with `N.IsConvex` and `N.toFun = maxAffine n a b`; rewrite and combine the two
bounds into `|N.toFun y − f y| ≤ ε` on `K`.

## 5. File layout (`UniversalApproximation/Amos/Approx/`)

- `Approx/MaxAffine.lean` — `maxAffine`, `maxAffine_isICNN` (Pillar A). Depends on `Amos/Defs`,
  `Amos/Activation` (`relu`, `id` convex+monotone), `Amos/Convex` (for `IsConvex` helpers if reused).
- `Approx/Tangent.lean` — `convex_diff_tangent_le` (Pillar B). Depends on `Amos/Defs` +
  Mathlib convex-derivative / fderiv.
- `Approx/Density.lean` — `maxTangent_approx` (Pillar C) + the headline `icnn_approximation`.
  Depends on `Approx/MaxAffine`, `Approx/Tangent`.

`Amos.lean` re-exports the new `Approx.*` alongside the existing files.

## 6. Docs updates (IN SCOPE — not deferred)

- **`README.md`** — Amos entry: convex UAP now **proved** (`…Amos.icnn_approximation`), not forthcoming.
- **`CLAUDE.md`** — Amos bullet + layout note: soundness **and** UAP (for differentiable convex);
  general non-differentiable case noted as forthcoming.
- **`UniversalApproximation.lean` + `NeuralNetworkProofs.lean`** — add the `icnn_approximation`
  headline bullet to both docstrings (no aggregator import change needed if `Amos.lean` re-exports
  the new files, which it will).
- **`scripts/check_sorry_free.lean`** — add `#print axioms …Amos.icnn_approximation`.
- **Blueprint** — extend `blueprint/src/chapter/amos.tex` with the UAP theorem node
  (`\lean{UniversalApproximation.Amos.icnn_approximation}` + `\uses` for `icnn_convex` and the
  max-affine/tangent lemmas); `intro.tex` framing (soundness + UAP).
- **`site/index.html`** — update the Amos card (soundness + convex UAP proved).

## 7. Verification (acceptance gate)

`lake build` green; `lake env lean scripts/check_sorry_free.lean` extended with
`UniversalApproximation.Amos.icnn_approximation` reporting exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; blueprint `leanblueprint web` +
`lake exe checkdecls blueprint/lean_decls` pass (the new `\lean{}` node resolves); grep confirms docs
consistently describe Amos as soundness + UAP. Existing developments' statements/proofs untouched
(purely additive).

## 8. Feasibility summary (honest)

All three pillars are tractable against **current** Mathlib — there is no missing research-grade
dependency, because the multivariate minorant is *derived* from the existing 1-D convex-derivative
lemmas rather than assumed. Confirmed available: `ConvexOn.sup` / `Finset.sup'`,
`ConvexOn.locallyLipschitzOn(_interior)` and `locallyLipschitz` (finite-dim), 1-D `ConvexOn` slope/
deriv lemmas (`ConvexOn.le_slope_of_hasDerivAt`, …), `ConvexOn.comp_affineMap`, `HasFDerivAt.comp`,
`IsCompact.elim_finite_subcover`, and dev 1's `relu`/`id` convex+monotone activations. The realistic
failure mode is **effort/index-bookkeeping** in Pillar A's inductive `ICNN` construction, not a
mathematical wall. If Pillar B or C nonetheless hits a genuine research-grade blocker, report
`NEEDS_CONTEXT` — never weaken the statement, never `sorry`.

## 9. Non-goals (recorded follow-ups)

- **Full non-differentiable convex UAP** — arbitrary continuous convex functions; needs multivariate
  subgradient / affine-minorant existence built from `geometric_hahn_banach` on the epigraph (a
  substantial convex-analysis contribution absent from Mathlib). Recorded for a later cycle.
- **Convex-on-an-open-domain generalization** — `f` convex + differentiable only on an open convex
  `U ⊇ K` (rather than all of `ℝ^d`); more interior/neighborhood bookkeeping.
- **General-compact-domain partial-monotone** (dev 3).
- Any training/optimization claim; PICNN variants (FICNN only).

## 10. Conventions

Follow CLAUDE.md: line length ≤ 100 codepoints, no `sorry`/`admit`, minimal precise imports,
sorry-free gate. Build serially if a from-scratch rebuild hits EMFILE.
