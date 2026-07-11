/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.UniversalApproximation.Monotone
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman
import NeuralNetworkProofs.UniversalApproximation.Sartor
import NeuralNetworkProofs.UniversalApproximation.Runje

/-!
# Universal approximation theorems — results aggregator

Re-exports every UAT development so a single import brings in all results. Headlines:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Cybenko.universal_approximation_eps` — Cybenko (1989), ε form.
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).
* `UniversalApproximation.MikulincerReichman.monotone_interpolation` — M–R (2022), interpolation.
* `UniversalApproximation.MikulincerReichman.monotone_approximation` — M–R (2022), approximation.
* `UniversalApproximation.Sartor.saturating_interpolation` — Sartor et al. (2025), Thm 3.5.
* `UniversalApproximation.Sartor.nonpos_weight_universal` — Sartor et al. (2025), Prop 3.11.

`UniversalApproximation.Runje` — Runje et al., Deep Constrained Monotonic Neural Networks
(forthcoming; extends Runje–Shankaranarayana 2023). Skip connections make deep constrained
monotone networks trainable; formalized soundness (monotone at any depth) + UAP. Includes partial
monotonicity as a secondary result.

* `UniversalApproximation.Runje.deep_monotone_approximation` — deep monotone UAP (retains UAP).
* `UniversalApproximation.Runje.ResNet.monotone_toFun` — deep residual stack is monotone
  (soundness).
* `UniversalApproximation.Runje.rsDense_monotone` — R–S dense layer is monotone.
* `UniversalApproximation.Runje.partial_monotone_approximation` — Runje et al. (forthcoming),
  partial-monotone UAP (secondary).
* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — Runje et al. (forthcoming), soundness
  (secondary).

The shared `ActStack` core lives in `UniversalApproximation.Monotone`.
-/
