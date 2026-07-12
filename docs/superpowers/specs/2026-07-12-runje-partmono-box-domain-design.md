# Partial-monotone UAP on general box domains (design)

**Date:** 2026-07-12
**Status:** design self-approved (author away, decisions delegated); pending plan
**Namespace:** `UniversalApproximation.Runje`
**Branch:** `feat/runje-partmono-box-domain`

## 1. Goal

Generalize the Runje partial-monotone universal-approximation theorem
`partial_monotone_approximation` from the **unit cube** `[0,1]^df × [0,1]^dm` to an **arbitrary
non-degenerate box** `[aF, bF] × [aM, bM]` (products of compact intervals with nonempty interior),
via an affine change of variables. This is dev 3 of the planned program and closes the recorded
general-compact-domain follow-up.

**Scope decision (recorded, and honest about the limit).** For a *coordinatewise-monotone* target the
admissible domain in the monotone block is precisely a **box** (a product of intervals): a general
compact subset of `ℝ^dm` is incompatible with the coordinatewise partial order without a
monotone-extension theorem that Mathlib does not have. So "general compact domain" here means
"general box", which is the maximal order-compatible domain. The truly general (non-box) monotone
domain is a recorded follow-up (Non-goals §8). The feature block *could* be generalized to an
arbitrary compact set independently, but in this theorem it is coupled to the monotone grid through
the joint target, so that too is deferred (§8).

## 2. Program context (3 developments, this is #3)

1. **ICNN soundness** — shipped (PR #37).
2. **ICNN UAP** — shipped (PR #38).
3. **General-box partial-monotone** — this spec.

## 3. The change of variables

For `a b : Fin d → ℝ` with `a j < b j` for all `j` (non-degenerate box):

- `cubeOfBox a b : (Fin d → ℝ) → (Fin d → ℝ)`, `cubeOfBox a b x j = (x j - a j) / (b j - a j)` —
  the coordinatewise affine map sending `Set.Icc a b` onto `Set.Icc 0 1`.
- `boxOfCube a b : (Fin d → ℝ) → (Fin d → ℝ)`, `boxOfCube a b x̃ j = a j + (b j - a j) * x̃ j` —
  its inverse, sending `Set.Icc 0 1` onto `Set.Icc a b`.

Both are coordinatewise **increasing** (since `b j - a j > 0`), continuous, and mutually inverse.
Key lemmas (all elementary): `cubeOfBox_mem` (`x ∈ Icc a b → cubeOfBox a b x ∈ Icc 0 1`),
`boxOfCube_mem`, `cubeOfBox_boxOfCube`/`boxOfCube_cubeOfBox` (inverses), `continuous_boxOfCube`,
`monotone_boxOfCube` (`Monotone (boxOfCube a b)` — the coordinatewise order, needed to preserve the
monotone hypothesis).

## 4. The two structural closure lemmas

### 4a. Feature block — `genSpanPi` closed under coordinatewise-affine precomposition

```lean
theorem genSpanPi_comp_cubeOfBox {σ : ℝ → ℝ} {df : ℕ} {aF bF : Fin df → ℝ}
    (hab : ∀ j, aF j < bF j) {g : (Fin df → ℝ) → ℝ} (hg : g ∈ genSpanPi σ df) :
    (fun u => g (cubeOfBox aF bF u)) ∈ genSpanPi σ df
```

Proof: precomposition `g ↦ g ∘ (cubeOfBox aF bF)` is an `ℝ`-linear map on `(Fin df → ℝ) → ℝ`; it
sends each generator `genFunPi σ w b` to another generator `genFunPi σ w' b'` (a ridge
`σ(∑ w·x + b)` composed with a coordinatewise-affine `x ↦ D x + c₀` is `σ(∑ (w·D)·u + (w·c₀+b))`).
A linear map carrying a spanning set into the submodule carries the span in; use
`Submodule.span_le` / `Submodule.mem_span` with the generator image computation.

### 4b. Monotone block — `MonoNet` suffix-block rescaling

```lean
def MonoNet.rescaleSuffix {p q : ℕ} (N : MonoNet (p + q)) (s t : Fin q → ℝ) : MonoNet (p + q)
theorem MonoNet.rescaleSuffix_isMonotone {p q N s t} (hN : N.IsMonotone) (hs : ∀ j, 0 ≤ s j) :
    (N.rescaleSuffix s t).IsMonotone
theorem MonoNet.rescaleSuffix_toFun {p q} (N : MonoNet (p + q)) (s t) (z : Fin p → ℝ)
    (x : Fin q → ℝ) :
    (N.rescaleSuffix s t).toFun (Fin.append z x)
      = N.toFun (Fin.append z (fun j => s j * x j + t j))
```

Construction: **prepend** an identity-activation, positive-diagonal affine layer to `N.stack`, so the
new stack first maps `(z, x) ↦ (z, s ⊙ x + t)` and then runs `N.stack`. Concretely a
`NeuralNetwork.Layer (p+q) (p+q)` with `W := Matrix.diagonal (Fin.addCases (fun _ => 1) s)` (entry `1`
on the `p` prefix coords, `s j` on the `q` suffix coords) and `c := Fin.addCases (fun _ => 0) t`,
activation `id`. `Layer.toFun id L (Fin.append z x) = Fin.append z (s ⊙ x + t)` because the diagonal
`mulVec` is the pointwise product (`Matrix.mulVec_diagonal`) and `Fin.append`/`Fin.addCases` split the
coordinates. `rescaleSuffix N s t := { N with stack := .cons L id N.stack }`.
- `IsMonotone`: the prepended layer has `Monotone id` (`monotone_id`) and all-nonnegative weights
  (diagonal entries `1`/`s j ≥ 0`, off-diagonal `0`), and `N.stack.IsMonotone` is unchanged; `readW`
  unchanged. So the whole net stays monotone. (This is why "prepend id-layer" beats folding into the
  first layer — `IsMonotone` is preserved trivially.)
- `toFun`: `ActStack.toFun (.cons L id N.stack) w = N.stack.toFun (L.toFun id w)`; the read-out is
  unchanged; combine with the layer identity above.

## 5. The headline

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

Proof (change of variables):
1. Define `f̃ ũ x̃ := f (boxOfCube aF bF ũ) (boxOfCube aM bM x̃)` on the unit cube.
2. `f̃` is `ContinuousOn` the unit-cube product (compose `hf` with the continuous `boxOfCube` maps,
   which send unit cubes into the boxes — `ContinuousOn.comp` + `boxOfCube_mem`).
3. `f̃` is monotone in `x̃` on the unit cube: `boxOfCube aM bM` is coordinatewise increasing
   (`monotone_boxOfCube`), and `f` is monotone in its monotone block; compose (via `hmono` +
   `boxOfCube_mem`).
4. Apply `partial_monotone_approximation σ hσ hnp f̃ … hε` to get `P̃` with `P̃.mono.IsMonotone`,
   `P̃.emb i ∈ genSpanPi σ df`, and `|P̃.toFun ũ x̃ − f̃ ũ x̃| ≤ ε` on the unit cube.
5. Build `P` by folding the rescalings in:
   - `P.emb u i := P̃.emb (cubeOfBox aF bF u) i` — in `genSpanPi σ df` by `genSpanPi_comp_cubeOfBox`.
   - `P.mono := P̃.mono.rescaleSuffix s t` with `s j = 1/(bM j − aM j)`, `t j = −aM j/(bM j − aM j)`
     (so `s ⊙ x + t = cubeOfBox aM bM x`); `IsMonotone` via `rescaleSuffix_isMonotone` (`s j > 0`).
   - `P := ⟨embWidth, fun u i => P̃.emb (cubeOfBox aF bF u) i, P̃.mono.rescaleSuffix s t⟩`.
6. Compute `P.toFun u x`: unfold `PartMonoNet.toFun`, use `rescaleSuffix_toFun` (the clamped-embedding
   prefix `z` is untouched; the monotone suffix `x` is mapped to `cubeOfBox aM bM x`), and the emb
   rewrite, to get `P.toFun u x = P̃.toFun (cubeOfBox aF bF u) (cubeOfBox aM bM x)`.
7. For `u ∈ Icc aF bF`, `x ∈ Icc aM bM`: `cubeOfBox … u ∈ Icc 0 1`, `cubeOfBox … x ∈ Icc 0 1`
   (`cubeOfBox_mem`), and `f̃ (cubeOfBox aF bF u) (cubeOfBox aM bM x) = f u x` (`boxOfCube`∘`cubeOfBox`
   = id, step 5's `s,t` chosen so `cubeOfBox aM bM = fun x => s ⊙ x + t`). So the step-4 bound gives
   `|P.toFun u x − f u x| ≤ ε`.

The unit-cube `partial_monotone_approximation` is the special case `aF=0,bF=1,aM=0,bM=1`; that frozen
headline is untouched (this theorem is additive).

## 6. File layout

- `Runje/BoxDomain.lean` — `cubeOfBox`/`boxOfCube` + their lemmas (§3); `genSpanPi_comp_cubeOfBox`
  (§4a); `MonoNet.rescaleSuffix` + `_isMonotone` + `_toFun` (§4b). Imports `Runje/Defs`,
  `Runje/Embedding`, `Monotone/Defs`, `NeuralNetwork/Network`, minimal Mathlib.
- `Runje/PartMonoBox.lean` — the headline `partial_monotone_approximation_box` (§5). Imports
  `Runje/Approximation` (for `partial_monotone_approximation`) and `Runje/BoxDomain`.
- `Runje.lean` re-exports the new files (add imports).

## 7. Docs + gate (IN SCOPE)

- `scripts/check_sorry_free.lean` — add `#print axioms partial_monotone_approximation_box`.
- `UniversalApproximation.lean` + `NeuralNetworkProofs.lean` — add a bullet noting the general-box
  partial-monotone result under Runje (match existing style).
- `README.md` + `CLAUDE.md` — note the box-domain generalization of the partial-monotone secondary
  result (keep the Runje framing: deep constrained monotone networks primary, partial monotone
  secondary; this extends the secondary result to general boxes). Keep "six developments".
- `blueprint/src/chapter/runje.tex` — add a theorem node
  `\lean{UniversalApproximation.Runje.partial_monotone_approximation_box}` + `\uses` for the cube
  version; `leanblueprint web` + `checkdecls` must resolve it.

## 8. Non-goals (recorded follow-ups)

- **Non-box (general compact) monotone domain** — needs a coordinatewise-monotone extension /
  Whitney-type theorem absent from Mathlib.
- **Feature block on a general compact set** independent of the monotone grid — needs a partition of
  unity subordinate to a general finite cover (the current proof uses the tent grid on the cube).
- **Deep variant** `deep_partial_monotone_approximation_box` — the identical change of variables
  applies to `DeepPartMonoNet`; deferred to keep this development tight (note it in the docstring).
- Degenerate boxes (`aF j = bF j`) — excluded by the strict `<` hypotheses.

## 9. Verification (acceptance gate)

`lake build` green; `lake env lean scripts/check_sorry_free.lean` extended with
`partial_monotone_approximation_box` reporting exactly `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`; blueprint `leanblueprint web` + `lake exe checkdecls blueprint/lean_decls` pass; existing
developments untouched (purely additive). If a structural lemma hits a genuine wall, report
`NEEDS_CONTEXT` — never `sorry` or weaken the statement.

## 10. Conventions

CLAUDE.md: ≤ 100 codepoints/line, no `sorry`/`admit`, minimal precise imports, sorry-free gate.
Build serially if a from-scratch rebuild hits EMFILE.
