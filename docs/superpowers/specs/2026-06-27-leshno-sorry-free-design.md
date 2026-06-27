# Leshno UAT — eliminating the final two `sorry` leaves — Design Spec

**Date:** 2026-06-27
**Status:** Approved (design) — pending spec review
**Goal:** Discharge the two remaining `sorry` leaves of the Leshno M-class UAT —
`TestFunctionDegreeBound.exists_uniform_degree_bound` (D) and
`UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` (A) — via **elementary,
self-contained, in-repo routes that avoid the upstream Mathlib infrastructure** the current blocker
notes assume. On completion the entire `leshno_dense_iff` development is `sorry`-free (axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

## Context

After PR #7 (merged), `leshno_dense_iff` is fully assembled and the development bottoms out in
**exactly two `sorry` leaves**, each now a clean general statement in `LeanPlayground/Contrib/`:

```lean
-- D (Contrib/TestFunctionDegreeBound.lean)
theorem exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : ClassM σ)
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → IsPolynomialFun (mollify σ φ)) :
    ∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      iteratedDeriv (d + 1) (mollify σ φ) = 0

-- A (Contrib/UniformRiemannConvolution.lean)
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S
```

The merged blocker notes assume D needs a `BaireSpace`/`CompleteSpace` instance on the test-function
space `ContDiffMapSupportedIn` (absent from Mathlib), and A needs a parameter-uniform
Riemann/Lebesgue criterion (only `BoxIntegral`, no uniformity hook). **Both assumptions are
avoidable.** Two feasibility spikes (each probing Mathlib for exact signatures and elaborating
skeletons) validated alternative routes that need only lemmas confirmed to exist.

Relevant proved helpers (reuse): `mollify_eq_convolution` (`mollify σ φ = convolution φ σ
(ContinuousLinearMap.mul ℝ ℝ) volume`), `ClassM.locallyIntegrable`, `ClassM.aestronglyMeasurable`,
`ConvolutionIteratedDeriv.iteratedDeriv_convolution_left`, and — for A — the **already-proved
continuous-kernel sibling** `tendstoUniformly_riemannSum_continuous` in the same file (its cell /
partition machinery is reused wholesale).

**Non-goal:** no change to `leshno_dense_iff`, `mollify`, `ClassM`, `T`, the two leaf *statements*
(only their proofs are filled), or any already-proved lemma. No new Mathlib upstream dependency.

## Decisions locked during brainstorming

1. **In-repo elementary routes** for both leaves (validated by spikes), not upstream infrastructure.
2. **One combined spec/plan** with two independent workstreams (D and A), buildable and reviewable
   separately.

## D — `exists_uniform_degree_bound` via algebraic degree-invariance

**Idea.** The degree of `σ⋆φ` is invariant under further convolution. Convolving a degree-`e`
polynomial with a test function `ψ` with `∫ψ ≠ 0` yields a polynomial of degree exactly `e` (the
`x^e` coefficient scales by the 0th moment `∫ψ`). With associativity
`(σ⋆φ)⋆ψ = σ⋆(φ⋆ψ) = (σ⋆ψ)⋆φ`, fix a normalized bump `ψ₀` (`∫ψ₀ = 1`) and set
`d₀ := (the polynomial mollify σ ψ₀).natDegree`. Then for any test `φ`:
`deg(σ⋆φ) = deg((σ⋆φ)⋆ψ₀) = deg((σ⋆ψ₀)⋆φ) ≤ d₀`. No Baire, no Fréchet completeness.

**Sub-lemmas (ordered; new `Contrib/` content unless noted):**

- **D1 `convolution_comm_mul`** — `convolution f g (mul ℝ ℝ) volume = convolution g f (mul ℝ ℝ)
  volume`. *Trivial* (`convolution_flip` + `ContinuousLinearMap.flip_mul`; proved in spike).
- **D2 convolution-exists helpers** — `ConvolutionExistsAt`/integrability for the
  compactly-supported-factor cases (`HasCompactSupport.convolutionExists_left/_right`,
  `LocallyIntegrable.aestronglyMeasurable`). *Easy.*
- **D3 `mollify_conv_assoc`** — `(σ⋆φ)⋆ψ = σ⋆(φ⋆ψ)` in our orientation (through
  `mollify_eq_convolution`), via `MeasureTheory.convolution_assoc` (exists) + `mul_assoc`
  coherence + D2. *Moderate.*
- **D4 `monomial_conv_isPoly`** — `(fun x => ∫ (x − y)^n * ψ y) = q.eval` with `q.natDegree ≤ n`
  and `q.coeff n = ∫ ψ`. *Substantial (the crux):* `sub_pow` + `MeasureTheory.integral_finset_sum`
  + moment coefficients; the leading-coefficient identity (top coeff = 0th moment) is unavoidable
  but conceptually clean.
- **D5 `poly_conv_degree`** — `convolution (p.eval) ψ (mul ℝ ℝ) volume = (Φ p).eval` with
  `(Φ p).natDegree ≤ p.natDegree`, and `= p.natDegree` when `∫ψ = 1`. *Moderate:* linearity over
  monomials of D4 + `leadingCoeff` propagation.
- **D6 `poly_iteratedDeriv_succ_eq_zero`** — `natDegree ≤ d ⟹ iteratedDeriv (d+1) (fun x =>
  p.eval x) = 0` (`Polynomial.deriv` + `Polynomial.iterate_derivative_eq_zero` +
  `iteratedDeriv_eq_iterate`). *Easy* (proved in spike).
- **D7 normalized bump** — `ψ₀ := (ContDiffBump …).normed volume`: `ContDiff ℝ ∞`, compact
  support, `∫ψ₀ = 1 ≠ 0` (`ContDiffBump.contDiff_normed/hasCompactSupport_normed/integral_normed`).
  *Trivial.*
- **D-assembly** — close `exists_uniform_degree_bound`: `d₀ := (mollify σ ψ₀ as poly).natDegree`;
  for any `φ`, chain D3 + D5 (both orientations) to `deg(σ⋆φ) ≤ d₀`, then D6.

*Estimate: ~200–280 lines. Riskiest: D4.* Spike verdict: **GREEN-leaning-YELLOW**, no Mathlib gaps.

## A — `tendstoUniformly_riemannSum_aeContinuous` via oscillation + dominated convergence

**Idea.** Write the Riemann sum as a step-sampled integral; the error splits into a φ-variation
term (handled as in the continuous case) and an f-variation term. After the substitution `v = s − y`
the f-variation term is bounded by `‖φ‖∞ · ∫_{[-(L+M), L+M]} G(v, Δ) dv` over a **fixed compact
domain** (`S ⊆ [-L,L]`), where `G(v,Δ) = sup_{0≤h≤Δ}|f(v) − f(v+h)|`. The domain is independent of
`s` (uniformity for free); `G(v, Δ_m) → 0` at every continuity point of `f` (a.e., by `hdisc`) and
`G ≤ 2C`; dominated convergence finishes it.

**Sub-lemmas (ordered):**

- **A1 `aestronglyMeasurable_of_aeContinuous`** — a.e.-continuous + locally bounded `f ⟹
  AEStronglyMeasurable f volume` (`ContinuousOn.aestronglyMeasurable` on the conull complement of
  `closure {discontinuities}`). *Easy.* (May reuse/relate to `ClassM.aestronglyMeasurable`.)
- **A2 `ae_continuousAt`** — `∀ᵐ v, ContinuousAt f v` from `hdisc`
  (`measure_zero_iff_ae_notMem` + `subset_closure`). *Easy.*
- **A3 integrability** — `y ↦ f(s − y) * φ y` integrable on `Icc (-M) M`, with the local bound on
  the compact `S − Icc (-M) M` via `hbdd`. *Easy.*
- **A4 φ-variation term → 0 uniformly** — port directly from the continuous-case proof (uniform
  continuity of `φ` + bound on `f`). *Easy–medium.*
- **A5 f-variation reduction** — cell sum `= ∫_{[-M,M]} (f(s−y) − f(s−q(y))) * φ(q(y)) dy`, then
  `intervalIntegral.integral_comp_sub_left` to a fixed `s`-independent domain. *Medium.*
- **A6 `aemeasurable_oscillation`** — *the one novel lemma:* `AEMeasurable (fun v => G(v,Δ))`.
  The uncountable real sup is **not** Borel-measurable, but the rational sup `Ωrat` IS measurable
  (`Measurable.iSup`, proved in spike) and `G =ᵐ Ωrat` off the null discontinuity set; DCT needs
  only `AEStronglyMeasurable`. *Medium–hard (~50 lines).*
- **A7 `tendsto_oscillation_ae` + bound** — `G(v, Δ_m) → 0` a.e. (A2) and `G ≤ 2C` (`hbdd`).
  *Easy–medium.*
- **A-assembly** — `MeasureTheory.tendsto_integral_of_dominated_convergence` (dominator the
  constant `2C` on the fixed compact) + `Metric.tendstoUniformlyOn_iff`, combining A4 + A5–A7.

*Estimate: ~220–270 lines. Riskiest: A6.* Spike verdict: **YELLOW** (A6 surmountable; route
genuinely smaller than the BoxIntegral alternative and reuses the proved continuous-case machinery).

## Files

- **New** `LeanPlayground/Contrib/ConvolutionPolynomial.lean` — the *general, upstream-candidate*
  lemmas of the D route: D1 (`convolution_comm_mul`), D2 (convolution-exists helpers), D4
  (`monomial_conv_isPoly`), D5 (`poly_conv_degree`), D6 (`poly_iteratedDeriv_succ_eq_zero`). Per
  the convention: per-contribution namespace + inline `Intended Mathlib home:` header. (These are
  stated in pure `convolution` / `Polynomial` terms, independent of `mollify`/`ClassM`.)
- Edited `LeanPlayground/Contrib/TestFunctionDegreeBound.lean` — the *project-specific* D content:
  D3 (`mollify_conv_assoc`, the `mollify`-orientation bridge), D7 (the normalized bump), and the
  D-assembly closing `exists_uniform_degree_bound`; imports `ConvolutionPolynomial`. Removes the
  `sorry`.
- Edited `LeanPlayground/Contrib/UniformRiemannConvolution.lean` — A1–A7 + A-assembly added beside
  the existing continuous-case lemmas; removes the `sorry`.
- Edited `LeanPlayground/UniversalApproximation/Leshno.lean` — update the admit inventory to
  **0 leaves / fully `sorry`-free**.

## Sequencing

The two workstreams are independent. Within each, build sub-lemmas in the listed order (each
elaborates, then is proved `sorryAx`-free, then committed). Recommended overall order: **D first**
(higher confidence, GREEN-leaning), then **A** (the A6 measurability lemma is the single item most
likely to need extra care — tackle it when the rest of A is in place). Finish by flipping the
`Leshno.lean` inventory and confirming a `sorry`-free `lake build` + clean `lean_verify
leshno_dense_iff`.

## Verification (per the established discipline)

Per sub-lemma: write statement `:= by sorry` → confirm it elaborates (`lean_diagnostic_messages`,
only `sorry` warning) → prove → `lean_verify <name>` axioms `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`, since both leaves' dependencies are/will be proved) → `lean_build`
green → signed commit. Research-grade items (D4, A6): if genuinely intractable after serious
effort, STOP and report NEEDS_CONTEXT with the exact stuck goal and the precise missing lemma —
never a hidden `sorry`, never a weakened statement.

## Non-goals

- No change to the headline, `mollify`, `ClassM`, `T`, the two leaf statements, or any proved lemma.
- No modification of existing Cybenko files.
- No new Mathlib upstream dependency; no `BaireSpace`/`CompleteSpace`/`BoxIntegral` development.
