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

/-- E (leaf, this cycle). The mollification of an `M`-class `σ` by a smooth compactly-supported
kernel is smooth.

Intended proof (reserved as a leaf this cycle): `mollify σ φ` is the convolution
`MeasureTheory.convolution φ σ (ContinuousLinearMap.mul ℝ ℝ) volume`
(since `convolution φ σ L x = ∫ t, L (φ t) (σ (x - t)) = ∫ t, φ t * σ (x - t)` and
`σ (x - y) * φ y = φ y * σ (x - y)`), so `HasCompactSupport.contDiff_convolution_left`
yields `C^∞` (the smoothness order is now `∞ = ↑(⊤ : ℕ∞)`, which is exactly what that lemma
delivers — `ω`/analyticity is not claimed and would be false in general). The lemma needs
`HasCompactSupport φ` and `ContDiff ℝ ∞ φ` (have both) and `LocallyIntegrable σ volume`; local
integrability of an `M`-class `σ` follows from local boundedness (`ClassM.locBdd`) + a.e. continuity
(`ClassM.discNull`). The remaining work is the `mollify = convolution` rewrite plus deriving
`LocallyIntegrable σ` from `ClassM`; left as a documented `sorry` for this cycle. -/
theorem contDiff_mollify {σ φ : ℝ → ℝ} (hσ : ClassM σ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) : ContDiff ℝ ∞ (mollify σ φ) := by
  sorry

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
