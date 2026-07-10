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

/-!
# Universal Approximation for Partially Monotone Networks — root module (Runje et al.)

Formalization of partial-monotone universal approximation: a non-monotone feature block is
embedded by an unconstrained single-hidden-layer network (Leshno UAP), clamped, concatenated
with the monotone block, and fed to a monotone network (Mikulincer–Reichman / Sartor line).

* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — soundness (monotone in `x`).
* `UniversalApproximation.Runje.partial_monotone_approximation` — the UAP headline.
-/
