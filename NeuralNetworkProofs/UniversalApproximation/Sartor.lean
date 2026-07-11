/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating
import NeuralNetworkProofs.UniversalApproximation.Sartor.SaturatingInterp
import NeuralNetworkProofs.UniversalApproximation.Sartor.Equivalence
import NeuralNetworkProofs.UniversalApproximation.Sartor.NonPositive

/-!
# Universal Approximation for Monotone Networks — Sartor et al. (2025)

> D. Sartor et al., "Advancing Constrained Monotonic Neural Networks: Achieving Universal
> Approximation Beyond Bounded Activations", arXiv:2505.02537 (2025).

For monotone, one-sided-saturating, non-constant activations, depth-4 monotone networks are
universal, via alternating-saturation non-negative weights (Thm 3.5) or, equivalently,
non-positive weights and a single activation (Prop 3.11), tied by the weight-sign ↔ saturation-side
reflection (Props 3.8/3.10). Built on the shared `ActStack` core in
`UniversalApproximation.Monotone`.

* `UniversalApproximation.Sartor.saturating_interpolation` — Theorem 3.5.
* `UniversalApproximation.Sartor.nonpos_weight_universal` — Proposition 3.11.
-/
