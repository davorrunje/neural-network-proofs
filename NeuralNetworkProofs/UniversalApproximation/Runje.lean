/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.Clamp
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity
import NeuralNetworkProofs.UniversalApproximation.Runje.JointTarget
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation
import NeuralNetworkProofs.UniversalApproximation.Runje.BoxDomain
import NeuralNetworkProofs.UniversalApproximation.Runje.PartMonoBox
import NeuralNetworkProofs.UniversalApproximation.Runje.RunjeShankaranarayana
import NeuralNetworkProofs.UniversalApproximation.Runje.Residual
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepMono
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepPartMono

/-!
# Deep Constrained Monotonic Neural Networks — root module (Runje et al.)

Runje et al., Deep Constrained Monotonic Neural Networks (forthcoming; extends
Runje–Shankaranarayana 2023). Skip connections make deep constrained monotone networks trainable;
formalized soundness (monotone at any depth) + UAP. Includes partial monotonicity as a secondary
result.

* `UniversalApproximation.Runje.rsDense_monotone` — R–S dense layer is monotone.
* `UniversalApproximation.Runje.ResNet.monotone_toFun` — deep residual stack is monotone
  (soundness).
* `UniversalApproximation.Runje.deep_monotone_approximation` — deep monotone UAP (retains UAP).
* `UniversalApproximation.Runje.DeepPartMonoNet.monotone_snd` — deep-core partial-monotone
  soundness.
* `UniversalApproximation.Runje.deep_partial_monotone_approximation` — deep-core partial UAP.
* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — shallow partial-monotone soundness
  (secondary).
* `UniversalApproximation.Runje.partial_monotone_approximation` — shallow partial-monotone UAP
  (secondary).
* `UniversalApproximation.Runje.partial_monotone_approximation_box` — shallow partial-monotone UAP
  on a general box domain (secondary).
-/
