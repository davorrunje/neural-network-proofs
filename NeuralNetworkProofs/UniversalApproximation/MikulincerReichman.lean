/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Indicator
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Grid
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Interpolation
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Approximation

/-!
# Universal Approximation for Monotone Networks — Mikulincer–Reichman (2022)

> D. Mikulincer and R. Reichman, "The Size of the Weights Matter", arXiv:2207.05275 (2022).

Every monotone continuous function on the unit cube `[0,1]^d` is uniformly `ε`-approximated by a
depth-4 monotone threshold network, with exact interpolation on finitely many points. Built on the
shared `ActStack` core in `UniversalApproximation.Monotone`.

* `UniversalApproximation.MikulincerReichman.monotone_interpolation` — Result 1, interpolation.
* `UniversalApproximation.MikulincerReichman.monotone_approximation` — Result 1, approximation.
-/
