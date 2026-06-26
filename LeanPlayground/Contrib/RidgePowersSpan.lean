import Mathlib

/-! # Powers of linear functionals span the homogeneous polynomials.
Intended Mathlib home: `Mathlib/LinearAlgebra/Polynomial` / `Mathlib/RingTheory/MvPolynomial`
(polarization; confirm with maintainers).

This is the polarization identity for symmetric tensors, phrased at the level of polynomial
*functions* on `Fin n → ℝ`. As of the toolchain pin (`v4.32.0-rc1`) no off-the-shelf statement
was found via `lean_leansearch`/`lean_loogle`. The closest existing material is
`MvPolynomial.homogeneousSubmodule` (the submodule of homogeneous polynomials of a given degree),
`MvPolynomial.homogeneousSubmodule_one_eq_span_X`, and `MvPolynomial.evalₗ`
(`MvPolynomial.evalₗ_apply : evalₗ K σ p e = eval e p`), all of which we reuse to phrase the
right-hand side; none of them give the "powers of linear forms span" statement directly.

## Choice of right-hand side

The left-hand side is the span of the *functions* `x ↦ (∑ i, a i * x i) ^ k`, so the right-hand
side must also be a `Submodule ℝ ((Fin n → ℝ) → ℝ)`. We take it to be the image, under the
evaluation-as-a-function linear map `MvPolynomial.evalₗ ℝ (Fin n) : MvPolynomial (Fin n) ℝ →ₗ[ℝ]
(Fin n → ℝ) → ℝ`, of the canonical Mathlib submodule of homogeneous degree-`k` polynomials
`MvPolynomial.homogeneousSubmodule (Fin n) ℝ k`. This is the most faithful elaborating
formulation: it names "homogeneous degree-`k` polynomial functions" via Mathlib's existing
`homogeneousSubmodule` rather than reinventing a monomial-span, and the generators on the left are
exactly the evaluations of `(∑ i, C (a i) * X i) ^ k`, which is homogeneous of degree `k`, so the
two sides live in the same space and the `⊆` inclusion is definitionally on track. -/

namespace RidgePowersSpan

open MvPolynomial

variable {n : ℕ}

/-- The powers `x ↦ (∑ i, a i * x i) ^ k`, ranging over `a : Fin n → ℝ`, span
(over ℝ) the space of homogeneous polynomial functions of degree `k` on `Fin n → ℝ`.
(Polarization of symmetric tensors.) Needed for the Leshno ridge-function step.
Leshno et al. 1993 / Pinkus, Acta Numerica 1999, Thm 3.1.

The right-hand side is the image of `MvPolynomial.homogeneousSubmodule (Fin n) ℝ k` under the
evaluation linear map `MvPolynomial.evalₗ ℝ (Fin n)`; see the file docstring for the rationale. -/
theorem ridgePow_span (k : ℕ) :
    Submodule.span ℝ
        (Set.range fun a : Fin n → ℝ =>
          (fun x : Fin n → ℝ => (∑ i, a i * x i) ^ k))
      = Submodule.map (MvPolynomial.evalₗ ℝ (Fin n))
          (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) := by
  sorry

end RidgePowersSpan
