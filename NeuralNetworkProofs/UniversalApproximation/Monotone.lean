/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic

/-!
# Monotone neural networks — shared core

Shared infrastructure for the monotone-network universal-approximation developments
(`UniversalApproximation.MikulincerReichman` and `UniversalApproximation.Sartor`, and reused by
`UniversalApproximation.Runje`): the activation-generic `ActStack` model, the monotone network
`MonoNet`, the `heaviside` gate, and shared lemmas.

* `UniversalApproximation.Monotone.ActStack`, `…MonoNet`, `…heaviside`.
-/
