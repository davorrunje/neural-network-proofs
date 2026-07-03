/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Domination
import NeuralNetworkProofs.UniversalApproximation.Monotone.Grid
import NeuralNetworkProofs.UniversalApproximation.Monotone.Interpolation
import NeuralNetworkProofs.UniversalApproximation.Monotone.Approximation

/-!
# Universal Approximation for Monotone Neural Networks — root module

This is the root module of a Lean 4 + Mathlib formalization of **Result 1** of

> D. Mikulincer and R. Reichman, "The Size of the Weights Matter",
> arXiv:2207.05275 (2022).

The result states that every monotone continuous function on the unit cube
`[0,1]^d ⊆ ℝ^d` can be uniformly approximated, to any precision `ε > 0`, by a
depth-4 monotone neural network; and that the data-interpolation analogue holds
with exact equality on finitely many points.

This module re-exports all six component modules:

* `Basic` — general reusable lemmas (`sum_le_one_card_le_iff`, `dist_le_of_coord`,
  `sort_key_linear_extension`).
* `Defs` — `MonoNet`, `MonoNet.toFun`, `MonoNet.depth`, `MonoNet.IsMonotone`;
  uses `heaviside` as the activation function.
* `Domination` — the domination-indicator gadget used in the construction.
* `Grid` — the grid construction and its properties.
* `Interpolation` — headline theorem `monotone_interpolation`.
* `Approximation` — headline theorem `monotone_approximation`.

## Headlines

```
UniversalApproximation.Monotone.monotone_interpolation
UniversalApproximation.Monotone.monotone_approximation
```
-/
