import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.ClassM
import LeanPlayground.UniversalApproximation.Leshno.Family
import LeanPlayground.UniversalApproximation.Leshno.MollifyDef
import LeanPlayground.Contrib.UniformRiemannConvolution
import LeanPlayground.Contrib.ConvolutionIteratedDeriv
import LeanPlayground.Contrib.SmoothCompactAntideriv
import LeanPlayground.Contrib.PolynomialDistribution
import LeanPlayground.Contrib.IteratedDerivPolynomial
import LeanPlayground.Contrib.TestFunctionDegreeBound

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
  rw [mollify_eq_convolution]
  exact hφc.contDiff_convolution_left _ hφ hσ.locallyIntegrable

/-- D (leaf). A non-a.e.-polynomial `M`-class `σ` admits a smooth compactly-supported kernel whose
mollification is not an everywhere polynomial.

Proof sketch (standard distribution theory; reserved as a leaf for the 7b assembly step). -/
theorem exists_nonpoly_mollify {σ : ℝ → ℝ} (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ¬ IsPolynomialFun (mollify σ φ) := by
  sorry

/-- Assembly core (σ-regularity-independent): if the ridge `x ↦ (σ⋆φ)(lam*(⟪w,x⟫+b)+c)` is a
uniform-on-`K` limit of the point-sampling Riemann sums (each of which is a `genSpan` element via
`genFun_reparam_mem`), it lies in `T σ K`. -/
private theorem mollify_ridge_mem_T_of_uniformRiemann {σ φ : ℝ → ℝ} (M : ℝ)
    (K : Set E) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c))
    (hunif : TendstoUniformlyOn
      (fun m (x : ↥K) => UniformRiemannConvolution.riemannSum σ φ M m (lam * (⟪w, (x:E)⟫ + b) + c))
      (fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) Filter.atTop Set.univ) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩ : C(↥K, ℝ)) ∈ T σ K := by
  intro ε hε
  -- Extract a partition index `m` for which the Riemann sum is uniformly within `ε`.
  obtain ⟨m, hm⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif ε hε).exists
  -- The Riemann sum, as a function of `x`, lies in `genSpan σ K`.
  refine ⟨fun x : ↥K => UniformRiemannConvolution.riemannSum σ φ M m
      (lam * (⟪w, (x : E)⟫ + b) + c), ?_, ?_⟩
  · -- It is a finite ℝ-combination of reparametrised generators.
    rw [show (fun x : ↥K => UniformRiemannConvolution.riemannSum σ φ M m
        (lam * (⟪w, (x : E)⟫ + b) + c))
        = ∑ i ∈ Finset.range m,
            (φ (-M + (i : ℝ) * (2 * M / m)) * (2 * M / m)) •
              (fun x : ↥K =>
                σ (lam * (⟪w, (x : E)⟫ + b) + (c - (-M + (i : ℝ) * (2 * M / m))))) from ?_]
    · refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
      exact genFun_reparam_mem σ K lam w b (c - (-M + (i : ℝ) * (2 * M / m)))
    · funext x
      simp only [UniformRiemannConvolution.riemannSum, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hsub : lam * (⟪w, (x : E)⟫ + b) + c - (-M + (i : ℝ) * (2 * M / m))
          = lam * (⟪w, (x : E)⟫ + b) + (c - (-M + (i : ℝ) * (2 * M / m))) := by ring
      rw [hsub]; ring
  · intro x
    have := hm x (Set.mem_univ x)
    rwa [Real.dist_eq] at this

theorem mollify_ridge_mem_T_of_continuous {σ φ : ℝ → ℝ} (hσc : Continuous σ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (K : Set E) (hK : IsCompact K)
    (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩ : C(↥K, ℝ)) ∈ T σ K := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  -- Choose `M > 0` with `support φ ⊆ Icc (-M) M` from compact support of `φ`.
  have hbdd : Bornology.IsBounded (Function.support φ) :=
    (hφc.isCompact).isBounded.subset (subset_closure)
  obtain ⟨M, hM, hsubball⟩ := hbdd.subset_closedBall_lt 0 0
  have hsupp : Function.support φ ⊆ Set.Icc (-M) M := by
    rw [← Real.closedBall_zero_eq_Icc]; exact hsubball
  -- The continuous parametrization `p : ↥K → ℝ`.
  set p : ↥K → ℝ := fun x : ↥K => lam * (⟪w, (x : E)⟫ + b) + c with hp
  have hpc : Continuous p := by rw [hp]; fun_prop
  -- Its range is compact (continuous image of compact `↥K`).
  have hScpt : IsCompact (Set.range p) := isCompact_range hpc
  -- Uniform Riemann-sum convergence on the compact range.
  have huS := UniformRiemannConvolution.tendstoUniformly_riemannSum_continuous
    hσc hφ.continuous hM hsupp hScpt
  -- Transport to uniform-on-univ of `↥K` via the parametrization.
  have huniv : TendstoUniformlyOn
      (fun m (x : ↥K) => UniformRiemannConvolution.riemannSum σ φ M m (p x))
      (fun x : ↥K => mollify σ φ (p x)) Filter.atTop Set.univ := by
    have hcomp := huS.comp p
    rwa [Set.preimage_range] at hcomp
  exact mollify_ridge_mem_T_of_uniformRiemann M K w b lam c hcont huniv

/-- A (leaf, hard M-class core). For `M`-class `σ`, every dilated/translated ridge of the smooth
mollification `σ ⋆ φ` lies in the continuous-core submodule `T`: it is an everywhere-sup limit on
`K` of `genSpan` elements (the Riemann sums of the convolution integral).

Proof. Mirrors `mollify_ridge_mem_T_of_continuous`, but feeds the a.e.-continuous M-class Riemann
core `UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` (using `hσ.locBdd` and
`hσ.discNull`) instead of the continuous one. Choose `M > 0` with `support φ ⊆ Icc (-M) M`; the
ridge parametrisation `p : ↥K → ℝ` has compact range (`hK`); uniform Riemann convergence on
`range p` transports to uniform-on-`univ` of `↥K`, and `mollify_ridge_mem_T_of_uniformRiemann` packs
each Riemann sum as a `genSpan σ K` element via `genFun_reparam_mem`, giving membership in `T σ K`.
-/
theorem mollify_ridge_mem_T {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (K : Set E) (hK : IsCompact K) (w : E) (b lam c : ℝ)
    (hcont : Continuous fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c)) :
    (⟨fun x : ↥K => mollify σ φ (lam * (⟪w, (x : E)⟫ + b) + c), hcont⟩
      : C(↥K, ℝ)) ∈ T σ K := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  -- Choose `M > 0` with `support φ ⊆ Icc (-M) M` from compact support of `φ`.
  have hbdd_supp : Bornology.IsBounded (Function.support φ) :=
    (hφc.isCompact).isBounded.subset (subset_closure)
  obtain ⟨M, hM, hsubball⟩ := hbdd_supp.subset_closedBall_lt 0 0
  have hsupp : Function.support φ ⊆ Set.Icc (-M) M := by
    rw [← Real.closedBall_zero_eq_Icc]; exact hsubball
  -- The continuous parametrization `p : ↥K → ℝ`.
  set p : ↥K → ℝ := fun x : ↥K => lam * (⟪w, (x : E)⟫ + b) + c with hp
  have hpc : Continuous p := by rw [hp]; fun_prop
  -- Its range is compact (continuous image of compact `↥K`).
  have hScpt : IsCompact (Set.range p) := isCompact_range hpc
  -- Uniform Riemann-sum convergence on the compact range (a.e.-continuous core).
  have huS := UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous
    hσ.locBdd hσ.discNull hφ.continuous hM hsupp hScpt
  -- Transport to uniform-on-univ of `↥K` via the parametrization.
  have huniv : TendstoUniformlyOn
      (fun m (x : ↥K) => UniformRiemannConvolution.riemannSum σ φ M m (p x))
      (fun x : ↥K => mollify σ φ (p x)) Filter.atTop Set.univ := by
    have hcomp := huS.comp p
    rwa [Set.preimage_range] at hcomp
  exact mollify_ridge_mem_T_of_uniformRiemann M K w b lam c hcont huniv

end UniversalApproximation.Leshno
