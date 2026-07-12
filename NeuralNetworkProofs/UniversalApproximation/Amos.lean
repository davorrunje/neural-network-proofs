/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Amos.Defs
import NeuralNetworkProofs.UniversalApproximation.Amos.Activation
import NeuralNetworkProofs.UniversalApproximation.Amos.Convex

/-!
# Input-Convex Neural Networks — Amos et al. (2017)

The fully-input-convex network (FICNN) and its soundness: an ICNN with nonnegative propagation
weights and convex, nondecreasing activations denotes a convex function. Universal approximation of
convex functions is a forthcoming development.

* `UniversalApproximation.Amos.icnn_convex` — soundness (convex denotation).
-/
