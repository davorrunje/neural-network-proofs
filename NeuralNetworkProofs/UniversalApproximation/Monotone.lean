/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Indicator
import NeuralNetworkProofs.UniversalApproximation.Monotone.Grid
import NeuralNetworkProofs.UniversalApproximation.Monotone.Interpolation
import NeuralNetworkProofs.UniversalApproximation.Monotone.Approximation
import NeuralNetworkProofs.UniversalApproximation.Monotone.Saturating
import NeuralNetworkProofs.UniversalApproximation.Monotone.Equivalence
import NeuralNetworkProofs.UniversalApproximation.Monotone.SaturatingInterp

/-!
# Universal Approximation for Monotone Neural Networks — root module

This is the root module of a Lean 4 + Mathlib formalization of **Result 1** of

> D. Mikulincer and R. Reichman, "The Size of the Weights Matter",
> arXiv:2207.05275 (2022).

The result states that every monotone continuous function on the unit cube
`[0,1]^d ⊆ ℝ^d` can be uniformly approximated, to any precision `ε > 0`, by a
depth-4 monotone neural network; and that the data-interpolation analogue holds
with exact equality on finitely many points.

**Phase 1 (feat/monotone-saturating-uat):** the model is now activation-generic
(`ActStack`, with `heaviside` as the canonical instance); M-R's interpolation proof
is re-derived through the shared `IsEpsIndicator` engine (historical note: the
original standalone threshold construction ships in PR #16).

This module re-exports all six component modules:

* `Basic` — general reusable lemmas (`sum_le_one_card_le_iff`, `dist_le_of_coord`,
  `sort_key_linear_extension`).
* `Defs` — `MonoNet`, `MonoNet.toFun`, `MonoNet.depth`, `MonoNet.IsMonotone`;
  activation-generic via `ActStack`; `heaviside` is the canonical instance.
* `Indicator` — `IsEpsIndicator` gadget abstraction and the threshold instance
  (`ε = 0`); replaces the retired `Domination` module.
* `Grid` — the grid construction and its properties.
* `Interpolation` — headline theorem `monotone_interpolation`; proof routed through
  the shared ε-indicator engine.
* `Approximation` — headline theorem `monotone_approximation`.

**Sartor et al. (arXiv:2505.02537) saturating-activation results** build on the same
activation-generic core:

* `Saturating` — Definition 3.3 (`RightSaturating`/`LeftSaturating`), point reflection
  `reflect` (Prop 3.8), the quantitative half-space (Lemma 3.6) and intersection (Lemma 3.7)
  limits, and `approx_interior_value`.
* `Equivalence` — the weight-sign ↔ saturation-side two-layer equivalence (`prop_3_10_two_layer`,
  Prop 3.10).
* `SaturatingInterp` — headline theorem `saturating_interpolation` (Theorem 3.5, the faithful
  ε-approximate form; three alternating one-sided-saturating activations), built on a
  γ-normalized read-out engine and the depth-3 core `sat_preadout_approx`.

## Headlines

```
UniversalApproximation.Monotone.monotone_interpolation
UniversalApproximation.Monotone.monotone_approximation
UniversalApproximation.Monotone.saturating_interpolation
```
-/
