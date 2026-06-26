# Leshno Universal Approximation (M-class) — Design Spec

**Date:** 2026-06-26
**Status:** Approved (design) — pending spec review
**Goal:** A compiling Lean 4 / Mathlib scaffold of the **Leshno–Lin–Pinkus–Schocken (1993)** universal approximation theorem in its full `M`-class generality: a single-hidden-layer network family with activation `σ ∈ M` is dense in `C(ℝⁿ)` (uniform on compacta) **iff** `σ` is not (a.e.) a polynomial. Built top-down with every deep analytic leaf as a documented `sorry`; all structural glue genuinely proved.

## Context

The repo already contains a near-complete Cybenko UAT scaffold under
`LeanPlayground/UniversalApproximation/` (`universal_approximation` proved modulo the single
admitted `riesz_repr`; `sigmoidal_discriminatory` fully proved). This effort targets the strictly
more general **Leshno** result, whose proof takes a completely different, *constructive* route
(mollification + ridge functions) that **bypasses Riesz/duality entirely** — so this branch can in
principle become `sorry`-free independently of `riesz_repr`.

**Reference.** Leshno, Lin, Pinkus, Schocken (1993), *Multilayer feedforward networks with a
nonpolynomial activation function can approximate any function*, Neural Networks 6(6):861–867.
Proof followed via Pinkus, *Approximation theory of the MLP model in neural networks*, Acta
Numerica 8 (1999), Theorem 3.1.

### Decisions locked during brainstorming

1. **Target:** full `M`-class (`L∞_loc`) theorem, the **iff**.
2. **Approximation metric:** everywhere-sup (uniform convergence on compacta), *not* ess-sup —
   the topology must work for thin compacta (e.g. a segment in ℝ², ambient-measure zero).
3. **"Polynomial" notion:** a.e.-polynomial (correct converse hypothesis under everywhere-sup;
   continuity of the target turns the a.e. statement into an everywhere obstruction).
4. **Staging:** go straight for the `M`-class theorem; the continuous-σ case is just an instance.
5. **Location:** `LeanPlayground/UniversalApproximation/Leshno/` (no existing file renamed).
6. **Upstreaming:** PR-candidate lemmas in `LeanPlayground/Contrib/` (the repo's contribution area,
   established by PR #5), each in a per-contribution namespace with an inline `Intended Mathlib home:`
   header — no separate tracking doc.

## Precise statement

```lean
theorem leshno_dense_iff (σ : ℝ → ℝ) (hσ : ClassM σ) :
    DenselyApproximates σ ↔ ¬ IsAEPolynomial σ
```

with

```lean
/-- The Leshno class `M`: locally bounded, and the closure of the discontinuity set is null
(equivalently, σ is locally Riemann integrable). -/
structure ClassM (σ : ℝ → ℝ) : Prop where
  locBdd : ∀ R : ℝ, ∃ C, ∀ t, |t| ≤ R → |σ t| ≤ C
  discNull : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt σ t}) = 0

/-- σ agrees a.e. (Lebesgue) with a polynomial function. -/
def IsAEPolynomial (σ : ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, σ =ᵐ[MeasureTheory.volume] (fun t => p.eval t)

/-- The family of single-hidden-unit functions `x ↦ σ(⟪w,x⟫+b)` densely approximates every
continuous function on every compact set, in everywhere-sup distance. -/
def DenselyApproximates (σ : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
    ∀ (f : C(↥K, ℝ)) {ε : ℝ}, 0 < ε →
      ∃ g ∈ genSpan σ K, ∀ x : ↥K, |f x - g x| < ε
```

The substantive direction is **(⇐) `¬ IsAEPolynomial σ ⇒ DenselyApproximates σ`**. The converse
(⇒, contrapositive `IsAEPolynomial σ ⇒ ¬ DenselyApproximates σ`) is easier.

## The discontinuity-localizing model

For `σ ∈ M`, the generator `x ↦ σ(⟪w,x⟫+b)` is only locally bounded and a.e. continuous, so it is
**not** an inhabitant of `C(↥K,ℝ)`. We therefore host the raw span in the plain `ℝ`-module
`↥K → ℝ`, and introduce a *continuous-core* submodule that captures exactly the continuous
functions the span can reach uniformly. All discontinuity is then confined to a single membership
fact (Lemma A); everything downstream is ordinary `C(↥K,ℝ)` analysis reusing
`Submodule.topologicalClosure`.

```lean
/-- A single hidden unit as a plain (possibly discontinuous) function on `↥K`. -/
def genFun (σ : ℝ → ℝ) {n} {K : Set (EuclideanSpace ℝ (Fin n))}
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) : ↥K → ℝ :=
  fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)

/-- The linear span of all single hidden units, inside the module of all functions `↥K → ℝ`. -/
def genSpan (σ : ℝ → ℝ) {n} (K : Set (EuclideanSpace ℝ (Fin n))) : Submodule ℝ (↥K → ℝ) :=
  Submodule.span ℝ (Set.range fun wb : EuclideanSpace ℝ (Fin n) × ℝ => genFun σ wb.1 wb.2)

/-- The continuous functions on `↥K` that are everywhere-sup limits of elements of `genSpan`.
This is a submodule of `C(↥K,ℝ)` and is closed; proving `T σ K = ⊤` is the heart of (⇐). -/
def T (σ : ℝ → ℝ) {n} (K : Set (EuclideanSpace ℝ (Fin n))) : Submodule ℝ C(↥K, ℝ) := …
  -- carrier: { h | ∀ ε > 0, ∃ g ∈ genSpan σ K, ∀ x, |h x - g x| < ε }
```

## Lemma DAG

```
leshno_dense_iff                                                         [Theorem.lean]
├─ (⇐)  T_eq_top ⇒ DenselyApproximates                                   [Family.lean]
│   └─ T_eq_top : ¬IsAEPolynomial σ ⇒ T σ K = ⊤
│       ├─ ridge_density          (C(K) ⊆ T, given univariate density)   [Ridge.lean]
│       │   ├─ C1 ridge_mem_T     (univariate ⇒ ridge x↦h(⟪a,x⟫) ∈ T)
│       │   ├─ C2a ridgePow_span  (powers (⟪a,·⟫)ᵏ span homog. degree-k)  [Contrib]
│       │   └─ C2b polys dense in C(K)        (Stone–Weierstrass)         [Mathlib]
│       └─ univariate_density     (the 1-D engine reaches all of C(ℝ))   [SmoothEngine + Mollify]
│           ├─ A  mollify_mem_T   (σ⋆φ ∈ T)    — hard M-class core        [Mollify.lean]
│           ├─ D  exists_nonpoly_mollify  (∃φ, ¬IsAEPolynomial (σ⋆φ))     [Mollify.lean]
│           ├─ E  contDiff_mollify (σ⋆φ ∈ C^∞)            (Mathlib)       [Mollify.lean]
│           └─ B  smooth_engine    (g∈C^∞, ¬poly ⇒ span{g(λ·+b)} dense)   [SmoothEngine.lean]
│               ├─ B1 deriv_pow_mem (tᵏ g⁽ᵏ⁾(λt+b) ∈ closure of shifts)
│               ├─ B2 exists_deriv_ne (¬poly ⇒ ∀k ∃bₖ, g⁽ᵏ⁾(bₖ)≠0)
│               │     └─ iteratedDeriv_eq_zero_imp_poly   (helper)        [Contrib]
│               └─ B3 monomials + Weierstrass            (Mathlib)
└─ (⇒)  IsAEPolynomial σ ⇒ ¬DenselyApproximates σ                        [Converse.lean]
```

### Node signatures (scaffold targets)

All `{n}`, `{K}`, `hK : IsCompact K` implicit/standing as needed; `open scoped RealInnerProductSpace`.

```lean
-- Family.lean
theorem genSpan_dilation_translation_invariant …    -- genSpan closed under w↦λw, b↦λb+c
theorem T_isClosed (σ K) : IsClosed (T σ K : Set C(↥K,ℝ))
theorem denselyApproximates_of_forall_T_eq_top
    (h : ∀ {n} (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → T σ K = ⊤) :
    DenselyApproximates σ

-- SmoothEngine.lean (univariate; work on compact intervals / C(ℝ) uniform on compacta)
theorem deriv_pow_mem (hg : ContDiff ℝ ⊤ g) (k : ℕ) (b : ℝ) … -- B1
theorem iteratedDeriv_eq_zero_imp_poly {f : ℝ → ℝ} {k : ℕ}
    (h : ∀ x, iteratedDeriv k f x = 0) : ∃ p : Polynomial ℝ, … ∧ p.natDegree < k   -- Contrib
theorem exists_deriv_ne (hg : ContDiff ℝ ⊤ g) (hnp : ¬ IsPolynomialFun g) (k : ℕ) :
    ∃ b, iteratedDeriv k g b ≠ 0                                                   -- B2
theorem smooth_engine (hg : ContDiff ℝ ⊤ g) (hnp : ¬ IsPolynomialFun g) : …       -- B3: span{g(λ·+b)} dense in C(ℝ)

-- Mollify.lean
noncomputable def mollify (σ : ℝ → ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := σ ⋆ φ              -- convolution
theorem contDiff_mollify (hσ : ClassM σ) (hφ : ContDiff ℝ ⊤ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ⊤ (mollify σ φ)                                                    -- E (Mathlib)
theorem exists_nonpoly_mollify (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    ∃ φ, ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ ∧ ¬ IsAEPolynomial (mollify σ φ)     -- D
theorem mollify_mem_T (hσ : ClassM σ) (hφ : ContDiff ℝ ⊤ φ) (hφc : HasCompactSupport φ) :
    (⟨mollify-as-ridge, …⟩ : C(↥K,ℝ)) ∈ T σ K                                      -- A (HARD)

-- Ridge.lean
theorem ridge_mem_T (huniv : univariate density) (a : EuclideanSpace ℝ (Fin n)) (h : C(ℝ,ℝ)) :
    (ridge a h : C(↥K,ℝ)) ∈ T σ K                                                  -- C1
theorem ridgePow_span … -- (⟪a,·⟫)ᵏ span homogeneous degree-k polynomials           -- C2a (Contrib)
theorem ridge_density (huniv) : T σ K = ⊤                                          -- C2 assembled

-- Converse.lean
theorem aePolynomial_not_dense (hσ : ClassM σ) (hp : IsAEPolynomial σ) :
    ¬ DenselyApproximates σ
```

(`IsPolynomialFun g := ∃ p : Polynomial ℝ, g = fun t => p.eval t` for the smooth/univariate
nodes, where everywhere-equality is available; `IsAEPolynomial` is the a.e. version used at the
`M`-class boundary. A small lemma bridges the two for continuous functions.)

## Mathlib-contribution candidates

Stated generally in `LeanPlayground/Contrib/`, each in a per-contribution namespace with an inline
`Intended Mathlib home: …` file-docstring header (the convention established by PR #5's
`RieszKantorovich.lean`; no separate tracking doc). Each is verified absent from Mathlib
(`lean_leansearch`/`lean_loogle`/`lean_local_search`) before scaffolding.

1. **`iteratedDeriv_eq_zero_imp_poly`** — `iteratedDeriv n f ≡ 0 ⇒ f` is a polynomial function of
   degree `< n` (needed by B2). Intended near `Mathlib/Analysis/Calculus/IteratedDeriv/*`.
2. **`ridgePow_span`** — powers `(⟪a,·⟫)ᵏ` of linear functionals span the homogeneous degree-`k`
   polynomials on a finite-dimensional inner-product space (polarization; needed by C2a).
3. **(conditional)** uniform-on-compacta approximation of `σ ⋆ φ` by Riemann sums for locally
   Riemann-integrable `σ` and `φ ∈ C_c^∞` — the general core of Lemma A — *only if* it crystallizes
   into a clean, project-independent statement.

## File layout

New, under `LeanPlayground/UniversalApproximation/Leshno/`:

- `ClassM.lean` — `ClassM`, `IsAEPolynomial`; `Continuous ⇒ ClassM`; ReLU/Heaviside ∈ M examples.
- `Family.lean` — `genFun`, `genSpan`, dilation/translation invariance, `T`, `T_isClosed`,
  `denselyApproximates_of_forall_T_eq_top`.
- `Mollify.lean` — `mollify`, E (Mathlib), D, A (hard).
- `SmoothEngine.lean` — B1, B2 (+ `iteratedDeriv_eq_zero_imp_poly` import), B3 = `smooth_engine`.
- `Ridge.lean` — C1, C2a (+ `ridgePow_span` import), C2b, `ridge_density`.
- `Converse.lean` — `aePolynomial_not_dense`.
- `Theorem.lean` — `leshno_dense_iff`.
- `Leshno.lean` (re-export root) — imports all of the above; admit-inventory docstring.

New, under `LeanPlayground/Contrib/` (alongside PR #5's `RieszKantorovich.lean`):

- `IteratedDerivPolynomial.lean` — `namespace IteratedDerivPolynomial`, `iteratedDeriv_eq_zero_imp_poly`.
- `RidgePowersSpan.lean` — `namespace RidgePowersSpan`, `ridgePow_span`.
- (conditional) `ConvolutionRiemannApprox.lean`.

Light reuse of existing scaffold: the `EuclideanSpace ℝ (Fin n)` / `⟪·,·⟫` conventions, and
optionally `Network.lean` for the network interpretation. No reuse of `Sigmoidal`, `Discriminatory`,
`Riesz`, or the Hahn–Banach reduction (this proof route does not need them).

## `sorry` policy & definition of done

- Each **leaf** lemma (A, D, B1, B2, `iteratedDeriv_eq_zero_imp_poly`, `ridgePow_span`, and any
  genuinely-hard residue) gets a full docstring (the missing mathematics + the Leshno/Pinkus
  reference) and a single `sorry`. **No bare `sorry` inside glue proofs** — all DAG-internal wiring
  (`T_eq_top`, `denselyApproximates_of_forall_T_eq_top`, `ridge_density`, `smooth_engine` assembly,
  `Converse`, `Theorem`) is genuinely proved so the skeleton type-checks.
- **Per-file done criterion:** `lean_diagnostic_messages` reports **no error-severity items**; the
  only warnings are `declaration uses 'sorry'` on the leaf lemmas (plus harmless linter notes).
- **Cycle deliverable:** the whole DAG compiles; `leshno_dense_iff` is stated and fully assembled,
  with only the documented analytic leaves left as `sorry`; everything else proved.
- **Lean iteration expected.** Signatures above are best-effort; exact Mathlib names are verified
  during implementation via `lean_leansearch` / `lean_loogle` / `lean_local_search` /
  `lean_hover_info`. Each leaf: (a) write with `sorry`, confirm the *statement* elaborates; commit.
- **Branch** `feat/leshno-uat`; commit per file/task; commit trailer
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. If commit signing hangs,
  retry once with `-c commit.gpgsign=false` and continue.

## Non-goals

- Discharging the deep analytic leaves this cycle (that is later work / the upstreaming effort).
- Touching the Cybenko files or `riesz_repr`.
- Approximation in any topology other than everywhere-sup uniform-on-compacta.
