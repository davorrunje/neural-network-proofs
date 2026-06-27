import LeanPlayground.UniversalApproximation
import LeanPlayground.UniversalApproximation.Leshno

/-! # LeanPlayground — universal approximation theorems

Root module of the package. It re-exports both formalized universal approximation
developments so that the default `lake build` target exercises (and thus verifies) their headline
theorems:

* `LeanPlayground.UniversalApproximation` — **Cybenko (1989)**: a single-hidden-layer network with a
  continuous sigmoidal activation is dense in `C(K, ℝ)`
  (`UniversalApproximation.universal_approximation`).
* `LeanPlayground.UniversalApproximation.Leshno` — **Leshno–Lin–Pinkus–Schocken (1993)**: an
  `M`-class activation densely approximates iff it is not (a.e.) a polynomial
  (`UniversalApproximation.Leshno.leshno_dense_iff`).
-/
