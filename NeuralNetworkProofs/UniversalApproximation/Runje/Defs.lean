/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.Clamp

/-!
# Partial-monotone networks (Runje et al.)

The shallow partial-monotone construction — a secondary result of the Deep Constrained Monotonic
Neural Networks development. A `PartMonoNet` embeds the non-monotone input block through an
unconstrained map `emb`, clamps it into `[0,1]`, concatenates it with the monotone block, and
feeds the result to a monotone network. Soundness: the denotation is monotone in the monotone
block for every fixed non-monotone input. UAP is proved in `Approximation.lean`; the deep-residual
generalization `DeepPartMonoNet` is in `DeepPartMono.lean`.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone

/-- A partial-monotone network: unconstrained embedding + monotone network over the
concatenation of the clamped embedding with the monotone inputs. -/
structure PartMonoNet (df dm : ℕ) where
  /-- Embedding width. -/
  embWidth : ℕ
  /-- Unconstrained embedding of the non-monotone block. -/
  emb : (Fin df → ℝ) → (Fin embWidth → ℝ)
  /-- Monotone network over the concatenated `[clamp(emb u), x]`. -/
  mono : MonoNet (embWidth + dm)

/-- Denotation: clamp the embedding, append the monotone inputs, apply the monotone net. -/
noncomputable def PartMonoNet.toFun {df dm} (P : PartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)

/-- **Soundness.** A partial-monotone network with a monotone core is monotone in the
monotone block `x`, for every fixed non-monotone input `u`. -/
theorem PartMonoNet.monotone_snd {df dm} (P : PartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u) := by
  intro x y hxy
  refine P.mono.monotone_toFun h ?_
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]; exact le_rfl
  · simpa only [Fin.append_right] using hxy j

end UniversalApproximation.Runje
