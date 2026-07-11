# Deep residual monotone networks (design)

**Date:** 2026-07-11
**Status:** design approved, pending spec review → implementation plan
**Namespace:** `UniversalApproximation.Runje` (new files)

## 1. Goal

**Framing (see the `runje-development-framing` note).** `UniversalApproximation.Runje` is Runje et
al., **"Deep Constrained Monotonic Neural Networks"** (forthcoming), extending Runje–Shankaranarayana
2023 ("Constrained Monotonic Neural Networks", ICML 2023). The paper's **main contribution is this
work**: skip connections that make **deep constrained monotone networks** trainable, with soundness
+ UAP. Partial monotonicity (`partial_monotone_approximation`, already formalized) is a *secondary*
result. So this deliverable is the **centerpiece** of the Runje development, and part of it is to
**correct the existing documentation**, which mis-casts Runje as "the partial-monotone development."

This deliverable adds **skip connections** enabling **deep constrained monotone networks**, and
formalizes:

- **Soundness** — a residual block, and a stack of them of *any depth*, is monotone; hence deep
  monotone networks are monotone, and (integrated) deep partial-monotone networks are monotone in
  their monotone block.
- **Completeness (retains UAP)** — the residual/deep construction remains universal: it subsumes
  the shallow universal monotone net, so UAP lifts with no loss.
- **R–S dense layer is monotone** — the Runje–Shankaranarayana (2023) "absolute-mode" dense layer
  (the `mononet` construction) is a monotone map in our abstraction, via a convex/concave sublayer
  split.

Construction reference: the `mononet` implementation (https://github.com/davorrunje/mononet),
`mononet/core/reference.py`. Note `mononet`'s own Lean proofs do **not** cover the residual/skip;
this is new formalization.

## 2. Background: the `mononet` construction vs our abstraction

`mononet`'s residual block (`monotonic_residual`):

```
y = g_α(α)·skip(x) + g_β(β)·F(x)
```

- `F` = a monotone dense layer (`monotonic_dense`); `skip` = identity (in = out) or `x @ exp(W)`;
  `g_α, g_β` = scalar gates, **strictly positive** for all inputs
  (`shifted_elu = ELU+1 ∈ (0,∞)`, `scaled_elu = max(·,0)+ε·exp(…) > 0`).
- So a block is a **positive-scalar-gated sum of two monotone maps ⇒ monotone**, and a **deep stack
  is a composition of monotone maps ⇒ monotone**.

**R–S is the same monotone-net class as our `ActStack`/`MonoNet` abstraction**
(`nonneg weights ∧ monotone activation`), up to reparametrization:

- `|W|` (R–S) is a reparametrization forcing nonneg weights — denotationally identical to our
  `W ≥ 0` predicate.
- `mononet`'s `concave_reflection(ρ)(x) = -ρ(-x)` is *exactly* `Sartor.reflect`. R–S's base
  activations (`relu`, `elu`, `selu`, `softplus`) are monotone and **left-saturating** (`S⁻`);
  their concave reflections are monotone **right-saturating** (`S⁺`) — precisely the Sartor
  `S⁻/S⁺` pairing. So R–S activations satisfy the Sartor UAP hypotheses.

Consequence: **no new dense-layer construction is needed.** The dense layer is already covered
(soundness via the `ActStack.IsMonotone` class; UAP via Sartor / Mikulincer–Reichman). The only
new content is (a) an explicit "R–S dense layer is monotone" instance, and (b) the residual/skip +
deep composition.

## 3. Framing (avoids overclaiming)

For monotone functions the **shallow** monotone nets are already universal
(`MikulincerReichman.monotone_approximation`, depth 4). Therefore:

- **Completeness = retains UAP.** Depth + skip do not *lose* expressivity; their value is
  trainability (empirical, not a theorem here).
- **No more than 4 layers are needed to retain UAP.** The UAP witness sets the block's skip gate to
  `0` (abstract) — or drives it to `0⁺` with uniformly vanishing skip contribution on the compact
  cube (concrete `mononet` gates) — so the witness is denotationally the existing **depth-4** core,
  wrapped in a single (degenerate) residual block. Deeper nets remain universal by the same
  subsumption. This is recorded as a proven **structural witness bound** (the UAP witness uses a
  single `ResBlock` over the depth-4 core) plus a prose remark; depth is *not* tracked as heavy
  arithmetic (F stays an arbitrary monotone map).

## 4. File layout (all under `UniversalApproximation.Runje`)

- `Runje/RunjeShankaranarayana.lean` — R–S "absolute" dense layer as a monotone map + concrete
  activation instances.
- `Runje/Residual.lean` — abstract residual combinator + concrete `mononet` gate/skip instances;
  the deep stack (`ResBlock`, `ResNet`) + soundness; `DeepMonoNet` + deep UAP by subsumption.
- `Runje/DeepPartMono.lean` — the PartMonoNet integration (`DeepPartMonoNet`): soundness + partial
  UAP with a deep-residual core.

## 5. Part A — R–S dense layer is monotone

```lean
open UniversalApproximation.Monotone UniversalApproximation.Sartor

/-- R–S absolute-mode dense map: convex block (activation `ρ`, nonneg weights `|Wc|`) on the first
`c` outputs, concave block (`reflect ρ`, nonneg weights `|Wk|`) on the rest, appended. -/
noncomputable def rsDense {a c k : ℕ} (ρ : ℝ → ℝ)
    (Wc : Matrix (Fin c) (Fin a) ℝ) (bc : Fin c → ℝ)
    (Wk : Matrix (Fin k) (Fin a) ℝ) (bk : Fin k → ℝ) : (Fin a → ℝ) → (Fin (c + k) → ℝ) :=
  fun x => Fin.append (fun i => ρ ((Wc.map (|·|)).mulVec x i + bc i))
                      (fun j => reflect ρ ((Wk.map (|·|)).mulVec x j + bk j))

theorem rsDense_monotone {a c k : ℕ} {ρ : ℝ → ℝ} (hρ : Monotone ρ) (Wc bc Wk bk) :
    Monotone (rsDense ρ Wc bc Wk bk)
```

Proof: each block is a single-activation monotone layer — reuse `layer_toFun_monotone` (nonneg
`|W|`) for the convex block with `ρ` and for the concave block with `reflect ρ` (monotone by
`Sartor.reflect_monotone hρ`); `Fin.append` of two coordinatewise-monotone maps is monotone (the
`Fin.addCases` split, as in `PartMonoNet.monotone_snd`).

Concrete activation instances (a couple, to tie R–S to Sartor's UAP hypotheses):

```lean
def elu (x : ℝ) : ℝ := if 0 < x then x else Real.exp x - 1
def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)
theorem elu_monotone : Monotone elu
theorem elu_leftSaturating : LeftSaturating elu           -- → -1 at -∞
theorem softplus_monotone : Monotone softplus
theorem softplus_leftSaturating : LeftSaturating softplus  -- → 0 at -∞
-- reflect elu / reflect softplus are RightSaturating by Sartor.reflect_rightSaturating
--   (reflect of a LeftSaturating map is RightSaturating)
```

## 6. Part B — residual combinator

```lean
/-- A residual block on maps: positive-gated sum of a skip and a sublayer `F`. -/
def residual {a b : ℕ} (gα gβ : ℝ) (skip F : (Fin a → ℝ) → (Fin b → ℝ)) :
    (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x i => gα * skip x i + gβ * F x i

theorem residual_monotone {a b : ℕ} {gα gβ : ℝ} {skip F : (Fin a → ℝ) → (Fin b → ℝ)}
    (hgα : 0 ≤ gα) (hgβ : 0 ≤ gβ) (hskip : Monotone skip) (hF : Monotone F) :
    Monotone (residual gα gβ skip F)
```

Proof: `x ≤ y ⇒ skip x ≤ skip y`, `F x ≤ F y` pointwise; scale by nonneg gates and add (coordinatewise `gcongr`).

Concrete `mononet` instances (certify the actual block satisfies the hypotheses):

```lean
noncomputable def shiftedElu (r : ℝ) : ℝ := (if 0 < r then r else Real.exp r - 1) + 1
noncomputable def scaledElu (ε r : ℝ) : ℝ := max r 0 + ε * Real.exp (min r 0 / ε)
theorem shiftedElu_pos (r) : 0 < shiftedElu r
theorem scaledElu_pos {ε} (hε : 0 < ε) (r) : 0 < scaledElu ε r
/-- exp-projected skip: `x ↦ (exp W).mulVec x` — nonneg matrix, hence monotone. -/
noncomputable def expSkip {a b} (W : Matrix (Fin b) (Fin a) ℝ) : (Fin a → ℝ) → (Fin b → ℝ) :=
  fun x => (W.map Real.exp).mulVec x
theorem expSkip_monotone (W) : Monotone (expSkip W)
theorem id_monotone : Monotone (id : (Fin a → ℝ) → (Fin a → ℝ))   -- identity skip
```

## 7. Part C — deep stack + soundness

```lean
structure ResBlock (a b : ℕ) where
  gα gβ : ℝ
  skip F : (Fin a → ℝ) → (Fin b → ℝ)
def ResBlock.IsMonotone {a b} (B : ResBlock a b) : Prop :=
  0 ≤ B.gα ∧ 0 ≤ B.gβ ∧ Monotone B.skip ∧ Monotone B.F
def ResBlock.toFun {a b} (B : ResBlock a b) := residual B.gα B.gβ B.skip B.F
theorem ResBlock.monotone_toFun {a b} (B : ResBlock a b) (h : B.IsMonotone) : Monotone B.toFun

inductive ResNet : ℕ → ℕ → Type where
  | nil  : {a : ℕ} → ResNet a a
  | cons : {a b c : ℕ} → ResBlock a b → ResNet b c → ResNet a c
def ResNet.toFun : {a c : ℕ} → ResNet a c → (Fin a → ℝ) → (Fin c → ℝ)
  | _, _, .nil, x => x
  | _, _, .cons B rest, x => rest.toFun (B.toFun x)
def ResNet.IsMonotone : {a c : ℕ} → ResNet a c → Prop
  | _, _, .nil => True
  | _, _, .cons B rest => B.IsMonotone ∧ rest.IsMonotone

/-- **Soundness: a residual stack of ANY depth is monotone.** -/
theorem ResNet.monotone_toFun : {a c : ℕ} → (N : ResNet a c) → N.IsMonotone → Monotone N.toFun
```

Proof: induction on `ResNet`; `nil` is `monotone_id`; `cons` composes `ResBlock.monotone_toFun`
with the tail via `Monotone.comp`.

## 8. Part D — deep UAP by subsumption

```lean
structure DeepMonoNet (d : ℕ) where
  width : ℕ
  net : ResNet d width
  readW : Fin width → ℝ
  readBias : ℝ
noncomputable def DeepMonoNet.toFun {d} (D : DeepMonoNet d) (x : Fin d → ℝ) : ℝ :=
  (∑ i, D.readW i * D.net.toFun x i) + D.readBias
def DeepMonoNet.IsMonotone {d} (D : DeepMonoNet d) : Prop :=
  D.net.IsMonotone ∧ ∀ i, 0 ≤ D.readW i
theorem DeepMonoNet.monotone_toFun {d} (D : DeepMonoNet d) (h : D.IsMonotone) : Monotone D.toFun

/-- Embed a shallow `MonoNet` as a single-block `DeepMonoNet` (skip off: `gα = 0, gβ = 1`,
`F = the stack's monotone map`), preserving the denotation exactly. -/
noncomputable def MonoNet.toDeep {d} (N : MonoNet d) : DeepMonoNet d
theorem MonoNet.toDeep_toFun {d} (N : MonoNet d) : N.toDeep.toFun = N.toFun
theorem MonoNet.toDeep_isMonotone {d} (N : MonoNet d) (h : N.IsMonotone) : N.toDeep.IsMonotone
/-- structural witness bound: the embedding uses exactly one residual block. -/
theorem MonoNet.toDeep_single_block {d} (N : MonoNet d) :
    ∃ B : ResBlock d N.width, N.toDeep.net = ResNet.cons B ResNet.nil

/-- **Deep UAP (retains UAP): every continuous monotone `f` on the cube is uniformly
ε-approximated by a monotone `DeepMonoNet`.** The witness is a single residual block over the
existing depth-4 core (see `MonoNet.toDeep_single_block`), so no depth beyond 4 is required. -/
theorem deep_monotone_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hmono : ∀ ⦃a b⦄, a ∈ Set.Icc (0 : Fin d → ℝ) 1 → b ∈ Set.Icc (0 : Fin d → ℝ) 1 →
      a ≤ b → f a ≤ f b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : DeepMonoNet d, D.IsMonotone ∧
      ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, |D.toFun x - f x| ≤ ε
```

Proof: `monotone_approximation` → `MonoNet N` (depth 4) within ε; take `N.toDeep`; rewrite the
bound and monotonicity through `toDeep_toFun` / `toDeep_isMonotone`.

**Note on `toDeep`.** `F` in the embedding block is the stack's monotone map
`N.stack.toOrderHom` (an arbitrary monotone map — no depth arithmetic). `gα = 0` makes the skip
vanish so `residual 0 1 skip F = F` denotationally; the block's `IsMonotone` uses `0 ≤ 0`,
`0 ≤ 1`, any monotone `skip` (e.g. `0`), and `F` monotone.

## 9. Part E — PartMonoNet integration

```lean
structure DeepPartMonoNet (df dm : ℕ) where
  embWidth : ℕ
  emb : (Fin df → ℝ) → (Fin embWidth → ℝ)
  mono : DeepMonoNet (embWidth + dm)
noncomputable def DeepPartMonoNet.toFun {df dm} (P : DeepPartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)

/-- Soundness: monotone in the monotone block `x`. -/
theorem DeepPartMonoNet.monotone_snd {df dm} (P : DeepPartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u)

/-- Partial-monotone UAP with a deep-residual core (retains the Runje headline). -/
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
        |P.toFun u x - f u x| ≤ ε
```

Soundness mirrors `PartMonoNet.monotone_snd` (deep core monotone via `DeepMonoNet.monotone_toFun`
+ `Fin.append` monotone in `x`). UAP: run `partial_monotone_approximation` → `PartMonoNet P₀`
with `MonoNet` core `M`; set `P := ⟨P₀.embWidth, P₀.emb, M.toDeep⟩`; `MonoNet.toDeep_toFun` gives
`P.toFun = P₀.toFun`, so the embedding certification and the ε bound transfer verbatim.

## 10. Verification

`lake build` green; sorry-free gate extended with the new headlines — `rsDense_monotone`,
`ResNet.monotone_toFun`, `deep_monotone_approximation`, `DeepPartMonoNet.monotone_snd`,
`deep_partial_monotone_approximation` — each reporting `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`. New files re-exported via `Runje.lean`; the aggregator + `NeuralNetworkProofs.lean`
docstring updated to list the new headlines.

## 11. Scope / non-goals

- **In scope:** §5–§9 (R–S monotone instance; residual combinator + concrete instances; deep stack
  + soundness; deep UAP by subsumption with a single-block structural witness; PartMonoNet
  integration).
- **In scope — documentation reframing (this PR).** Correct the framing of the Runje development
  everywhere to lead with *deep constrained monotone networks via skip connections* (soundness +
  UAP), with partial monotonicity as secondary: the module docstrings of the existing and new Runje
  files, the `Runje.lean` re-export + `UniversalApproximation` aggregator + `NeuralNetworkProofs.lean`
  docstrings, `README.md`, `CLAUDE.md`, and the leanblueprint Runje chapter
  (`blueprint/src/chapter/runje.tex`) — reframed *and* extended with the deep-residual results
  (`rsDense`, residual combinator, `ResNet` soundness, `deep_monotone_approximation`,
  `DeepPartMonoNet`), verified via `leanblueprint web` + `checkdecls`.
- **Non-goals (recorded follow-ups):**
  - Any *trainability* claim (empirical; not formalized).
  - Heavy depth arithmetic / a formal `depth ≤ 4` clause (the structural single-block witness +
    remark is the agreed level).
  - Re-deriving the R–S/Sartor UAP for the specific `mononet` activation names (subsumed by the
    existing Sartor UAP; only monotonicity + saturating instances are provided).

## 12. Risks

- **Low mathematical risk** — soundness is `Monotone.comp`/`gcongr` bookkeeping; UAP is exact
  subsumption of an existing theorem. No new analysis.
- **`ResNet` dependent-index induction** (the `{a b c}` chain) is the main Lean-mechanics fiddliness;
  mitigated by mirroring `ActStack`'s inductive style.
- **`MonoNet.toDeep`** must reproduce `MonoNet.toFun` exactly — the readout is copied verbatim and
  the single block computes `N.stack.toOrderHom`; the denotational equality is by `rfl`/`simp`.

## 13. Conventions

Follow CLAUDE.md: line length ≤ 100 codepoints, no `sorry`/`admit`, minimal precise imports,
sorry-free gate. Build serially if a rename/new-file rebuild hits EMFILE.
