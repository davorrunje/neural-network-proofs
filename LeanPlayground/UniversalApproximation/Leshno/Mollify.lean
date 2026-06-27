import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family

/-! # Mollification: smoothness (E), the nonpolynomial mollifier (D), and the M-class membrane (A).

This file builds the mollification (convolution) layer of the top-down Leshno (1993) universal
approximation scaffold:

* `mollify σ φ` — the convolution `x ↦ ∫ σ (x - y) · φ y`, smoothing an `M`-class activation `σ`
  against a smooth compactly-supported kernel `φ`;
* `contDiff_mollify` (E) — the mollification of an `M`-class `σ` by a smooth compactly-supported
  kernel is `C^∞`;
* `exists_nonpoly_mollify` (D, leaf) — a non-a.e.-polynomial `M`-class `σ` admits a kernel whose
  mollification is not an everywhere polynomial;
* `mollify_ridge_mem_T` (A, leaf, the hard M-class core) — every dilated/translated ridge of a
  mollified `M`-class `σ` lands in the continuous-core submodule `T`.
-/

namespace UniversalApproximation.Leshno

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Mollification of `σ` by a smooth compactly-supported kernel `φ` (convolution). -/
noncomputable def mollify (σ φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, σ (x - y) * φ y

/-- An `M`-class `σ` is a.e.-strongly-measurable: `σ` is continuous on the open set
`G := (closure {t | ¬ ContinuousAt σ t})ᶜ` whose complement is null (`ClassM.discNull`), so it is
a.e.-strongly-measurable on `volume.restrict G = volume`. -/
theorem ClassM.aestronglyMeasurable {σ : ℝ → ℝ} (hσ : ClassM σ) :
    AEStronglyMeasurable σ volume := by
  set G : Set ℝ := (closure {t | ¬ ContinuousAt σ t})ᶜ with hG
  have hGopen : IsOpen G := isClosed_closure.isOpen_compl
  have hcont : ContinuousOn σ G := by
    intro x hx
    have hx' : ContinuousAt σ x := by
      by_contra h
      exact hx (subset_closure h)
    exact hx'.continuousWithinAt
  have hmeas : AEStronglyMeasurable σ (volume.restrict G) :=
    hcont.aestronglyMeasurable hGopen.measurableSet
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ G := by
    rw [ae_iff]
    simpa [hG, compl_compl] using hσ.discNull
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hmeas

/-- An `M`-class `σ` is locally integrable: on each closed interval `Icc (x-1) (x+1)` (a
neighbourhood of `x`) the local bound `ClassM.locBdd` gives `|σ| ≤ C`, and bounded +
a.e.-strongly-measurable on a finite-measure set is integrable (`Measure.integrableOn_of_bounded`).
-/
theorem ClassM.locallyIntegrable {σ : ℝ → ℝ} (hσ : ClassM σ) :
    LocallyIntegrable σ volume := by
  intro x
  obtain ⟨C, hC⟩ := hσ.locBdd (|x| + 1)
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  apply Measure.integrableOn_of_bounded (M := C)
  · exact (measure_Icc_lt_top).ne
  · exact hσ.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro t ht
    have htR : |t| ≤ |x| + 1 := by
      rw [abs_le]
      constructor <;> [(have := ht.1); (have := ht.2)] <;>
        [(have hx := neg_abs_le x); (have hx := le_abs_self x)] <;> linarith
    simpa [Real.norm_eq_abs] using hC t htR

/-- E. The mollification of an `M`-class `σ` by a smooth compactly-supported kernel is `C^∞`.

Proof: `mollify σ φ` is the Mathlib convolution `φ ⋆[ContinuousLinearMap.mul ℝ ℝ] σ` (since
`(φ ⋆[mul] σ) x = ∫ t, φ t * σ (x - t)` by `convolution_mul`, and the integrands agree by
`mul_comm`). Then `HasCompactSupport.contDiff_convolution_left` yields `C^∞` from
`HasCompactSupport φ`, `ContDiff ℝ ∞ φ` and `LocallyIntegrable σ volume`; the latter comes from
`ClassM.locallyIntegrable` (local boundedness + a.e. continuity). -/
theorem contDiff_mollify {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) : ContDiff ℝ ∞ (mollify σ φ) := by
  have hconv : mollify σ φ
      = MeasureTheory.convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    rw [MeasureTheory.convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  rw [hconv]
  exact hφc.contDiff_convolution_left _ hφ hσ.locallyIntegrable

/-- D (leaf). A non-a.e.-polynomial `M`-class `σ` admits a smooth compactly-supported kernel whose
mollification is not an everywhere polynomial.

Proof sketch (standard distribution theory; reserved as a leaf). Suppose, for contradiction, that
`mollify σ φ` were an everywhere polynomial for *every* smooth compactly-supported `φ`. Each
mollification `σ ⋆ φ` is then a polynomial, and moreover its degree is uniformly bounded
independently of `φ`: differentiation commutes with convolution, `(d/dx)^N (σ ⋆ φ) = σ ⋆ φ^(N)`,
so if `σ ⋆ φ` had unbounded degree as `φ` ranges over an approximate identity, a fixed-order
derivative `(d/dx)^N (σ ⋆ φ)` would fail to vanish for arbitrarily large `N`, contradicting that
`σ ⋆ φ` is a polynomial of bounded degree. A distribution all of whose mollifications are
polynomials of uniformly bounded degree `≤ N` is itself (a.e.) a polynomial of degree `≤ N`
(test against the approximate identity and pass to the limit). Hence `σ` would be a.e. a polynomial,
contradicting `hnp`. The contrapositive produces the required witness `φ`. -/
theorem exists_nonpoly_mollify {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ¬ IsPolynomialFun (mollify σ φ) := by
  sorry

/-- A (leaf, hard M-class core). For `M`-class `σ`, every dilated/translated ridge of the smooth
mollification `σ ⋆ φ` lies in the continuous-core submodule `T`: it is an everywhere-sup limit on
`K` of `genSpan` elements (the Riemann sums of the convolution integral).

Proof sketch (the central analytic step; reserved as a leaf). Write
`s := lam * (⟪w, x⟫ + b) + c`. As `x` ranges over the compact `K`, `s` ranges over the compact
image `S := (fun x => lam * (⟪w, x⟫ + b) + c) '' K`. The mollification value is
`(σ ⋆ φ)(s) = ∫ σ (s - y) · φ y dy`, an integral over the *fixed* compact `tsupport φ`. Partition
that support into `m` cells of width `Δ` with nodes `yᵢ`; the Riemann sum
`Rₘ(s) := ∑ᵢ σ (s - yᵢ) · φ yᵢ · Δ` approximates `(σ ⋆ φ)(s)` uniformly for `s ∈ S`:
* `ClassM.locBdd` bounds `σ` on the compact `S - tsupport φ`, so the integrand is bounded;
* `ClassM.discNull` (the closure of the discontinuity set of `σ` is null) makes the integrand
  Riemann-integrable in `y` with error tending to `0` uniformly in `s ∈ S` (a.e.-continuous +
  bounded ⇒ uniform Riemann convergence on the compact node set).
For each fixed partition, `Rₘ` *as a function of `x`* is the finite linear combination
`∑ᵢ (φ yᵢ · Δ) · (fun x => σ (lam * (⟪w, x⟫ + b) + (c - yᵢ)))`. Each summand lies in `genSpan σ K`
by `genFun_reparam_mem` (reparametrisation with the same `lam`, `w`, `b` and shifted constant
`c - yᵢ`), so `Rₘ ∈ genSpan σ K`. Uniform convergence `Rₘ → (σ ⋆ φ) ∘ (ridge)` on `K` then gives
`ApproxByGen σ K`, i.e. membership in `T σ K`. (Cross-reference: the conditional `Contrib`
Riemann-sum convolution-approximation lemma.) -/
theorem mollify_ridge_mem_T {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩
      : C(↥K, ℝ)) ∈ T σ K := by
  sorry

end UniversalApproximation.Leshno
