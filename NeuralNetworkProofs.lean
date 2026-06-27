import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.NeuralNetwork.Network

/-! # NeuralNetworkProofs — universal approximation theorems

Re-exports the formalized developments so the default `lake build` builds and verifies both
headlines:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).

General neural-network infrastructure lives under `NeuralNetwork` (`NeuralNetwork.Layer`,
`NeuralNetwork.Network`); Mathlib-upstream candidates under `NeuralNetworkProofs.ForMathlib`. -/
