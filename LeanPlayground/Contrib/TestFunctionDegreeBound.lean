import Mathlib
import LeanPlayground.UniversalApproximation.Leshno.MollifyDef

/-! # Uniform degree bound for polynomial mollifications (Baire category).
Intended Mathlib home: research leaf — no general Mathlib home yet. The argument needs a
`CompleteSpace`/`BaireSpace` instance on the test-function space `ContDiffMapSupportedIn`
(`𝓓^{∞}_{K}`), which Mathlib does not (yet) provide; see the per-declaration blocker note. -/

namespace TestFunctionDegreeBound

open MeasureTheory
open UniversalApproximation.Leshno

open scoped ContDiff

/-- **Uniform degree bound (research leaf).** If every mollification `mollify σ φ` of an
`M`-class `σ` by a `C^∞` compactly-supported kernel `φ` is an everywhere polynomial, then there is
a single `d : ℕ` bounding the degree of *all* of them simultaneously, expressed as the vanishing of
the `(d+1)`-st iterated derivative.

This is the only research-grade analytic input to the (D) leaf `exists_nonpoly_mollify`. The
standard proof is a Baire-category argument on the Fréchet space `𝓓(ℝ)` of test functions: for each
`d`, the set `Fd := {φ | iteratedDeriv (d+1) (mollify σ φ) = 0}` is closed (the map
`φ ↦ iteratedDeriv (d+1) (mollify σ φ)` is continuous: it equals
`convolution (iteratedDeriv (d+1) φ) σ` by
`ConvolutionIteratedDeriv.iteratedDeriv_convolution_left`, and convolution against a fixed
locally-integrable `σ` is continuous in the smooth factor), and the hypothesis `H` says the `Fd`
cover `𝓓(ℝ)`. Baire (`nonempty_interior_of_iUnion_of_closed`) gives one `Fd` with nonempty interior,
whence a uniform bound for all `φ` by translation/scaling invariance of `𝓓(ℝ)`.

BLOCKER (toolchain pin `v4.32.0-rc1`). Mathlib *does* provide the right object,
`Mathlib.Analysis.Distribution.ContDiffMapSupportedIn` — the space `𝓓^{n}_{K}(E,F)` of `C^n`
functions supported in a fixed compact `K`, with the countable seminorm family `N[ℝ]_{K, i}`
(`ContDiffMapSupportedIn.withSeminorms`) making it metrizable, and a `T2Space`. What is **missing**
is a `CompleteSpace 𝓓^{n}_{K}` (equivalently `BaireSpace`) instance:
`nonempty_interior_of_iUnion_of_closed` needs `BaireSpace X`, and no `CompleteSpace`/`BaireSpace`
instance exists on `ContDiffMapSupportedIn` (nor on any `C^∞_c(ℝ)`/LF-space encoding). Supplying it
— proving the countable-seminorm metric on `𝓓_{[-R,R]}` is complete, then either using
`K = [-R,R]` for large `R` or assembling the LF colimit over `R` with translation/scaling to
globalize — is the substantial formalization effort reserved as this research leaf. The rest of the
argument (closedness of each `Fd` via the continuity of `φ ↦ iteratedDeriv (d+1) (mollify σ φ)`, and
globalization) is routine once `BaireSpace` is in hand. -/
theorem exists_uniform_degree_bound {σ : ℝ → ℝ} (hσ : ClassM σ)
    (H : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      IsPolynomialFun (mollify σ φ)) :
    ∃ d : ℕ, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      iteratedDeriv (d + 1) (mollify σ φ) = 0 := by
  sorry

end TestFunctionDegreeBound
