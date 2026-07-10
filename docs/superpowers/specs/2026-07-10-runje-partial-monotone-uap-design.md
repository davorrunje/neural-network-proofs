# Runje et al. — partial-monotone universal approximation (design)

**Date:** 2026-07-10
**Status:** design approved, pending spec review → implementation plan
**Namespace:** `UniversalApproximation.Runje` (new, author-named; see naming note §7)

## 1. Goal

Extend the monotone-network universal-approximation line (Mikulincer–Reichman 2022,
Sartor et al. 2025) to **partially monotone** functions. Inputs split into a non-monotone
block `u` and a monotone block `x`. The architecture, credited **Runje et al.**, is:

```
g(u, x) = MonoNet( concat( clamp(φ(u)), x ) )
```

where `φ` is an *unconstrained* single-hidden-layer embedding (Leshno UAP) and `MonoNet`
is the existing monotone network, monotone in *all* its (concatenated) inputs.

Two results:

- **Soundness** — every such network is monotone in `x` for each fixed `u`.
- **UAP** — the architecture uniformly approximates any continuous target that is monotone
  in `x`.

## 2. Target function class (approved)

`f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ`, on the **unit cubes** `Icc 0 1` for both blocks,
such that:

- `f` is jointly continuous on `Icc 0 1 ×ˢ Icc 0 1`, and
- for each fixed `u ∈ Icc 0 1`, the section `x ↦ f u x` is coordinatewise nondecreasing
  (`MonotoneOn (f u) (Icc 0 1)`).

Arbitrary (continuous) dependence on `u`. This is the standard "partially monotone" class
and matches the architecture's guarantee exactly.

## 3. Reused black boxes (verified signatures)

- **`UniversalApproximation.Monotone.monotone_approximation`**
  (`Monotone/Approximation.lean:54`): any continuous, coordinatewise-monotone
  `f : (Fin d → ℝ) → ℝ` on `Icc 0 1` is uniformly ε-approximable by a `MonoNet` (depth 4,
  `IsMonotone`). Used as a **joint** monotone UAP on the concatenated cube.
- **`UniversalApproximation.Leshno.leshno_dense`** (`Leshno/Theorem.lean:86`) via
  **`DenselyApproximates`** (`Leshno/Family.lean:129`) and **`genSpan`** (`Family.lean:41`):
  for a non-polynomial `ClassM` activation `σ`, every continuous function on a compact
  `K ⊆ EuclideanSpace ℝ (Fin df)` is sup-norm approximable by a single-hidden-layer span
  `genSpan σ K`. Used to build the embedding `φ`.
- **`MonoNet` / `MonoNet.IsMonotone` / `MonoNet.monotone_toFun`** (`Monotone/Defs.lean:144,163,168`).

`Fin.append` (Mathlib) provides the concatenation; there is currently no network-level
concat/product combinator in the repo, so the composite architecture is new (§4).

## 4. Architecture: `PartMonoNet`

New structure (in `Runje/Defs.lean`):

```lean
structure PartMonoNet (df dm : ℕ) where
  embWidth : ℕ
  emb  : (Fin df → ℝ) → (Fin embWidth → ℝ)   -- unconstrained embedding
  mono : MonoNet (embWidth + dm)

def PartMonoNet.toFun (P : PartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)
```

`clamp01 : ℝ → ℝ := fun t => max 0 (min 1 t)` clamps to `[0,1]`. It is baked into `toFun`
as a fixed bounded output activation on the embedding, so that the certified `emb`
coordinates remain pure single-hidden-layer nets (`∈ genSpanPi σ`, §5.1) while the value fed
to `mono` always lies in the unit cube.

### Soundness (Level 1 — fully general, no continuity needed)

```lean
theorem PartMonoNet.monotone_snd (P : PartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u)
```

Proof: `clamp01 ∘ (P.emb u)` is a fixed vector; `x ↦ Fin.append _ x` is monotone in the Pi
order; compose with `MonoNet.monotone_toFun`.

## 5. Headline theorem (Level 2 — UAP)

```lean
theorem partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2)
            (Set.Icc (0:Fin df→ℝ) 1 ×ˢ Set.Icc (0:Fin dm→ℝ) 1))
    (hmono : ∀ u ∈ Set.Icc (0:Fin df→ℝ) 1,
        MonotoneOn (f u) (Set.Icc (0:Fin dm→ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ (Set.Icc (0:Fin df→ℝ) 1)) ∧
      ∀ u ∈ Set.Icc (0:Fin df→ℝ) 1, ∀ x ∈ Set.Icc (0:Fin dm→ℝ) 1,
        |P.toFun u x - f u x| ≤ ε
```

The `genSpanPi` clause certifies the embedding is a genuine unconstrained single-hidden-layer
network (analogue of Sartor's `N.stack.activations = [...]` clause). The `σ`, `ClassM`,
`¬IsAEPolynomial` hypotheses are inherited from Leshno so the embedding works for any
Leshno-admissible activation.

### 5.1 The `genSpanPi` adaptor

Leshno's `genSpan`/`DenselyApproximates` live on `EuclideanSpace ℝ (Fin df)`, which carries
the inner-product instance `genSpan` needs; the monotone side uses plain `Fin df → ℝ`, which
does **not** have an `InnerProductSpace` instance. `Runje/Embedding.lean` bridges the two via
the isometry `e : EuclideanSpace ℝ (Fin df) ≃ᵢ (Fin df → ℝ)` (the `PiLp` equiv), defining

```lean
def genSpanPi (σ : ℝ → ℝ) (K : Set (Fin df → ℝ)) : Submodule ℝ (↥K → ℝ) :=
  (genSpan σ (e ⁻¹' K)).comap (precompose-with-e)   -- transported span
```

plus a bridging lemma turning `DenselyApproximates σ` into: every continuous `h : ↥K → ℝ`
on a compact `K ⊆ Fin df → ℝ` is sup-norm approximable by an element of `genSpanPi σ K`. The
inner product `⟪w, e v⟫` equals the dot product `Σ_j w_j v_j`, so a `genSpanPi` unit is
exactly a ridge unit `u ↦ σ(Σ_j w_j u_j + b)` — a bona fide single-hidden-layer neuron on
`Fin df → ℝ`.

## 6. Proof of the headline (error chain)

Approach A (soft partition-of-unity reduction) + clamp fix. Fix `ε > 0`.

1. **Partition of unity (ε/3).** `f` is uniformly continuous on the compact product, so
   choose grid spacing `h` such that a shift of `u` within cell diameter moves `f` by `<ε/3`
   uniformly in `x`. Build an explicit **tent (degree-1 multilinear) partition of unity**
   `{ψ_i}_{i<N}` on the `u`-cube: `ψ_i ≥ 0`, `Σ_i ψ_i = 1`, and `supp ψ_i` within `h` of node
   `u_i`. Let `C = ‖f‖∞ + 1 > 0` (attained on the compact product), `g_i(x) = f(u_i, x) + C`
   (so `g_i ≥ 0` on the cube), and define the joint target

   ```
   F(z, x) = (Σ_i z_i · g_i(x)) − C.
   ```

   With `Ψ(u) = (ψ_1(u), …, ψ_N(u))`, `F(Ψ(u), x) = Σ_i ψ_i(u) f(u_i, x)` (the `C` cancels
   via `Σψ_i = 1`), a convex combination of values `f(u_i, x)` with `u_i` within `h` of `u`,
   hence `|f(u, x) − F(Ψ(u), x)| < ε/3`.

2. **Joint monotone net (ε/3).** `F` is jointly continuous and **coordinatewise monotone** on
   `[0,1]^{N+dm}`: monotone in each `z_i` (coefficient `g_i(x) ≥ 0`), monotone in `x` (each
   `z_i ≥ 0`, each `g_i ↑`). The constant `−C` is irrelevant to monotonicity. Apply
   `monotone_approximation` to `F` (viewed as `(Fin (N+dm) → ℝ) → ℝ` via `Fin.append`
   splitting) to get `MonoNet M` with `M.IsMonotone` and `|M(w) − F(w)| ≤ ε/3` on the cube.

3. **Embedding (ε/3).** `F` is Lipschitz in `z` with constant `L = max_i ‖g_i‖∞`. Set
   `η = ε/(3L)`. Each `ψ_i` is continuous on the cube, so `leshno_dense` (through the
   `genSpanPi` bridge, §5.1) yields `φ_i ∈ genSpanPi σ` with `sup|ψ_i − φ_i| < η`. Since `clamp01` is 1-Lipschitz and
   `Ψ(u) ∈ [0,1]^N`, `‖(clamp01 ∘ φ)(u) − Ψ(u)‖ < η`, so
   `|F((clamp01 ∘ φ)(u), x) − F(Ψ(u), x)| ≤ L·η = ε/3`.

4. **Combine.** `clamp01 ∘ φ(u) ∈` cube keeps step 2 applicable, and the triangle inequality
   over steps 1–3 gives `|P.toFun u x − f u x| ≤ ε`, where `P = ⟨N, φ, M⟩`.

Dependency order is acyclic: `ε → (grid, F) → L → η → Leshno` and `F → M`.

### Key new lemma

"A convex combination `Σ z_i g_i(x) − C` of nonneg-shifted monotone-in-`x` functions, with
`z_i ∈ [0,1]`, is jointly coordinatewise monotone and Lipschitz in `z`." Elementary.

## 7. File layout (namespace `UniversalApproximation.Runje`)

New directory `NeuralNetworkProofs/UniversalApproximation/Runje/` + root re-export
`NeuralNetworkProofs/UniversalApproximation/Runje.lean`, added to `NeuralNetworkProofs.lean`
so `lake build` verifies the headline.

| File | Contents |
|------|----------|
| `Runje/Clamp.lean` | `clamp01`; continuous / monotone / range-in-`[0,1]` / 1-Lipschitz lemmas. |
| `Runje/Defs.lean` | `PartMonoNet` structure, `toFun`, `monotone_snd` (soundness). |
| `Runje/PartitionOfUnity.lean` | grid nodes + tent (1-D hat × product) partition of unity on the cube: `ψ_i ≥ 0`, `Σψ_i = 1`, support bound. **Main new analysis.** |
| `Runje/JointTarget.lean` | `F(z,x)`; joint continuity, coordinatewise monotonicity, Lipschitz-in-`z`; the convex-combination lemma. |
| `Runje/Embedding.lean` | `genSpanPi` adaptor (§5.1) + bridging lemma; vector Leshno embedding; `EuclideanSpace ℝ (Fin df) ↔ (Fin df → ℝ)` `PiLp` transport (inner product = dot product). |
| `Runje/Approximation.lean` | `partial_monotone_approximation` (headline), chaining §6. |
| `Runje.lean` | re-export root. |

Every file header credits **Runje et al.**; README and CLAUDE.md layout table gain a
`UniversalApproximation.Runje` row crediting Runje et al.

## 8. Naming note

The repo's UAT namespaces are currently *mixed*: `Cybenko`/`Leshno` are author-named,
while `Monotone` is topic-named and holds **both** Mikulincer–Reichman and Sartor et al.
This development takes a **new author-named namespace `UniversalApproximation.Runje`** (in
line with Cybenko/Leshno), accepting a temporary mixed convention.

**Follow-up (separate spec/PR, deferred):** unify all UAT namespaces to author-named by
splitting `Monotone` into `MikulincerReichman` + `Sartor`. Mechanical rename of existing
sorry-free code; kept out of this proof work.

## 9. Risks / effort

- **Highest:** tent partition of unity with the support bound (`PartitionOfUnity.lean`).
  Elementary but fiddly over `Fin`-indexed products; built explicitly rather than via
  Mathlib's abstract `PartitionOfUnity` to keep sum/support bounds concrete.
- **Medium:** `EuclideanSpace ↔ Fin df → ℝ` adaptor for `DenselyApproximates`.
- **Low:** joint monotonicity/Lipschitz of `F`, `Fin.append` monotonicity, clamp lemmas,
  soundness.

Scale: comparable to a mid-size slice of the existing monotone development — six new files,
one genuinely analytic, the rest reuse + plumbing.

## 10. Deferred follow-ups (recorded)

1. **General compact domains.** Generalize both blocks from the unit cube to arbitrary
   compact `K_f`, `K_m`. Needs `monotone_approximation` off the unit cube (currently
   cube-only). Recorded during brainstorming.
2. **Namespace unification** (§8).

## 11. Conventions

Follow CLAUDE.md: line length ≤ 100 codepoints, no `sorry`/`admit`, minimal precise imports
(no blanket `import Mathlib`), sorry-free gate via `scripts/check_sorry_free.lean`, and the
serialize-after-large-moves build workaround if needed.
