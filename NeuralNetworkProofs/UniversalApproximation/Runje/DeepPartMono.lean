/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Runje.DeepMono
import NeuralNetworkProofs.UniversalApproximation.Runje.Approximation

/-!
# Deep-core partial-monotone networks (Runje et al.)

`DeepPartMonoNet` swaps the monotone core of `PartMonoNet` for a deep-residual `DeepMonoNet`.
Soundness (monotone in the monotone block) mirrors `PartMonoNet.monotone_snd`; partial-monotone UAP
is inherited from `partial_monotone_approximation` by embedding its `MonoNet` core via
`MonoNet.toDeep`.

* `DeepPartMonoNet`, `DeepPartMonoNet.toFun`, `DeepPartMonoNet.monotone_snd` — the deep-core
  partial-monotone network, its denotation, and soundness in the monotone block.
* `deep_partial_monotone_approximation` — **deep-core partial-monotone UAP by subsumption of the
  shallow `PartMonoNet`.**
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.Leshno

/-- A deep-core partial-monotone network: unconstrained embedding + deep-residual monotone network
over the concatenation of the clamped embedding with the monotone inputs. -/
structure DeepPartMonoNet (df dm : ℕ) where
  /-- Embedding width. -/
  embWidth : ℕ
  /-- Unconstrained embedding of the non-monotone block. -/
  emb : (Fin df → ℝ) → (Fin embWidth → ℝ)
  /-- Deep-residual monotone network over the concatenated `[clamp(emb u), x]`. -/
  mono : DeepMonoNet (embWidth + dm)

/-- Denotation: clamp the embedding, append the monotone inputs, apply the deep monotone net. -/
noncomputable def DeepPartMonoNet.toFun {df dm} (P : DeepPartMonoNet df dm)
    (u : Fin df → ℝ) (x : Fin dm → ℝ) : ℝ :=
  P.mono.toFun (Fin.append (fun i => clamp01 (P.emb u i)) x)

/-- **Soundness.** A deep-core partial-monotone network with a monotone core is monotone in the
monotone block `x`, for every fixed non-monotone input `u`. -/
theorem DeepPartMonoNet.monotone_snd {df dm} (P : DeepPartMonoNet df dm)
    (h : P.mono.IsMonotone) (u : Fin df → ℝ) : Monotone (P.toFun u) := by
  intro x y hxy
  refine P.mono.monotone_toFun h ?_
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]; exact le_rfl
  · simpa only [Fin.append_right] using hxy j

/-- **Deep-core partial-monotone UAP (retains UAP).** Every jointly continuous `f` that is
coordinatewise monotone in its second (monotone) block on the unit cube is uniformly
`ε`-approximated by a `DeepPartMonoNet`: an unconstrained Leshno embedding of the non-monotone
block, clamped and concatenated with the monotone block, fed to a deep-residual monotone network.
The witness embeds the shallow `PartMonoNet` core via `MonoNet.toDeep`, sharing the same
embedding, so the denotation and the bound transfer verbatim. -/
theorem deep_partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2)
            (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1))
    (hmono : ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1,
        ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 → y ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
          x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : DeepPartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1,
        |P.toFun u x - f u x| ≤ ε := by
  obtain ⟨P₀, hmono0, hemb, hbound⟩ :=
    partial_monotone_approximation σ hσ hnp f hf hmono hε
  refine ⟨⟨P₀.embWidth, P₀.emb, P₀.mono.toDeep⟩,
    P₀.mono.toDeep_isMonotone hmono0, hemb, ?_⟩
  intro u hu x hx
  have hEq : (⟨P₀.embWidth, P₀.emb, P₀.mono.toDeep⟩ : DeepPartMonoNet df dm).toFun u x
      = P₀.toFun u x := by
    simp only [DeepPartMonoNet.toFun, PartMonoNet.toFun, MonoNet.toDeep_toFun]
  rw [hEq]
  exact hbound u hu x hx

end UniversalApproximation.Runje
