/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation
import NeuralNetworkProofs.NeuralNetwork.Network

/-! # NeuralNetworkProofs — universal approximation theorems

Re-exports the formalized developments so the default `lake build` builds and verifies all
headlines. `NeuralNetworkProofs.UniversalApproximation` is the canonical results aggregator; see
its docstring for the full headline list:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Cybenko.universal_approximation_eps` — Cybenko (1989), ε-approximate
  form.
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).
* `UniversalApproximation.MikulincerReichman.monotone_interpolation` — Mikulincer–Reichman (2022),
  interpolation form (Result 1).
* `UniversalApproximation.MikulincerReichman.monotone_approximation` — Mikulincer–Reichman (2022),
  approximation form (Result 1).
* `UniversalApproximation.Sartor.saturating_interpolation` — Sartor et al. (2025), Theorem 3.5
  (ε-approximate; monotone one-sided-saturating activations).
* `UniversalApproximation.Sartor.nonpos_weight_universal` — Sartor et al. (2025),
  Proposition 3.11.
* `UniversalApproximation.Runje.partial_monotone_approximation` — Runje et al. (2026),
  partial-monotone universal approximation.
* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — Runje et al. (2026), soundness.

General neural-network infrastructure lives under `NeuralNetwork` (`NeuralNetwork.Layer`,
`NeuralNetwork.Network`); Mathlib-upstream candidates under `NeuralNetworkProofs.ForMathlib`. -/
