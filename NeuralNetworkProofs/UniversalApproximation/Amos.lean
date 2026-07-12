/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs
import NeuralNetworkProofs.UniversalApproximation.Amos.Activation
import NeuralNetworkProofs.UniversalApproximation.Amos.Convex
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.MaxAffine
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Tangent
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Density

/-!
# Input-Convex Neural Networks — Amos et al. (2017)

The fully-input-convex network (FICNN) and its soundness: an ICNN with nonnegative propagation
weights and convex, nondecreasing activations denotes a convex function. Together with the convex
universal approximation theorem: any convex, differentiable function is uniformly approximated on
any compact set by such a network.

* `UniversalApproximation.Amos.icnn_convex` — soundness (convex denotation).
* `UniversalApproximation.Amos.icnn_approximation` — convex UAP (uniform approximation on compacts).
-/
