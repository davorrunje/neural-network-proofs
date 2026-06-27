import NeuralNetworkProofs.UniversalApproximation
import NeuralNetworkProofs.UniversalApproximation.Leshno

/-! # NeuralNetworkProofs — universal approximation theorems

Root module of the package. It re-exports both formalized universal approximation
developments so that the default `lake build` target exercises (and thus verifies) their headline
theorems:

* `NeuralNetworkProofs.UniversalApproximation` — **Cybenko (1989)**: a single-hidden-layer
  network with a continuous sigmoidal activation is dense in `C(K, ℝ)`
  (`UniversalApproximation.universal_approximation`).
* `NeuralNetworkProofs.UniversalApproximation.Leshno` — **Leshno–Lin–Pinkus–Schocken (1993)**: an
  `M`-class activation densely approximates iff it is not (a.e.) a polynomial
  (`UniversalApproximation.Leshno.leshno_dense_iff`).
-/
