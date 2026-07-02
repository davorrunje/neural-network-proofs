/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.UniversalApproximation.Monotone
import NeuralNetworkProofs.NeuralNetwork.Network

/-! # NeuralNetworkProofs — universal approximation theorems

Re-exports the formalized developments so the default `lake build` builds and verifies all
headlines:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).
* `UniversalApproximation.Monotone.monotone_interpolation` — Mikulincer–Reichman (2022),
  interpolation form (Result 1).
* `UniversalApproximation.Monotone.monotone_approximation` — Mikulincer–Reichman (2022),
  approximation form (Result 1).

General neural-network infrastructure lives under `NeuralNetwork` (`NeuralNetwork.Layer`,
`NeuralNetwork.Network`); Mathlib-upstream candidates under `NeuralNetworkProofs.ForMathlib`. -/
