/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating
import NeuralNetworkProofs.UniversalApproximation.Sartor.Equivalence
import NeuralNetworkProofs.UniversalApproximation.Sartor.SaturatingInterp

/-!
# Non-positive-weight monotone networks (Proposition 3.11, `𝒮⁺` case)

This file formalizes Proposition 3.11 of the Sartor et al. saturating-activation universal
approximation development: an all-**non-positive**-weight MLP using a *single* right-saturating
activation `σ` on its three hidden layers is universal (interpolation) for monotone datasets, and
its denotation is nonetheless monotone.

The proof reduces to Theorem 3.5 (`saturating_interpolation`) instantiated with the
`reflect`-alternating activations `[reflect σ, σ, reflect σ] = [𝒮⁻, 𝒮⁺, 𝒮⁻]`, giving a
non-negative-weight net `Npos`. The Proposition 3.10 sign-flip identities
(`reflect_negLayer_toFun`, `negWeights_toFun`) then convert each hidden layer to a single-`σ`
non-positive-weight layer, negating the stack's output; the resulting output sign flip is absorbed
into the read-out weights, so the new net `Nneg` has denotation identical to `Npos`
(`Nneg.toFun = Npos.toFun` exactly). The left-saturating (`𝒮⁻`) case is the exact `reflect`-dual
(as with Theorem 3.5's Case 2) and is not formalized here.

* `nonpos_weight_universal` — Proposition 3.11 (`𝒮⁺` case), stated with the
  `ActStack.WeightsNonpos` predicate (defined in `Monotone.Defs`).
-/

namespace UniversalApproximation.Sartor

open UniversalApproximation.Monotone
open NeuralNetwork

open scoped BigOperators

/-- **Proposition 3.11 (non-positive weights, 𝒮⁺ case).** For a monotone non-decreasing,
non-constant, right-saturating activation `σ`, any monotone dataset is ε-interpolated by a depth-4
MLP with ALL non-positive weights and the single activation `σ` on its three hidden layers — whose
denotation is nonetheless monotone. Obtained from Theorem 3.5 (`saturating_interpolation` with
activations `[reflect σ, σ, reflect σ] = [𝒮⁻,𝒮⁺,𝒮⁻]`) by the Prop 3.10 sign-flip identities; the
final output sign flip is absorbed into the read-out weights, so the denotation is unchanged. The
left-saturating (`𝒮⁻`) case is the exact `reflect`-dual (as with Theorem 3.5's Case 2) and is not
formalized here. -/
theorem nonpos_weight_universal {d n : ℕ} (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x)
    (σ : ℝ → ℝ) (hmσ : Monotone σ) (hsat : RightSaturating σ) (hnc : ∃ a b, σ a < σ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : MonoNet d, N.stack.WeightsNonpos ∧ (∀ i, N.readW i ≤ 0) ∧
      N.stack.activations = [σ, σ, σ] ∧ N.depth = 4 ∧ Monotone N.toFun ∧
      ∀ i, |N.toFun (x i) - y i| ≤ ε := by
  classical
  -- Step 1: `reflect σ` is left-saturating, monotone, and non-constant.
  have hmr : Monotone (reflect σ) := reflect_monotone hmσ
  have hlr : LeftSaturating (reflect σ) := reflect_leftSaturating hsat
  have hncr : ∃ a b, reflect σ a < reflect σ b := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨-b, -a, by simp only [reflect, neg_neg]; linarith⟩
  -- Step 2: instantiate Theorem 3.5 with `[reflect σ, σ, reflect σ]`.
  obtain ⟨Npos, hposMono, hposDepth, hposAct, hposEps⟩ :=
    saturating_interpolation x y hmono hinj (reflect σ) σ (reflect σ) hmr hmσ hmr
      hlr hsat hlr hncr hnc hncr (ε := ε) hε
  -- Step 3: destructure the stack via its `activations` equation.
  obtain ⟨w, S, readW, readBias⟩ := Npos
  -- Peel three layers; the `activations` list has length 3, forcing the shape.
  match S, hposAct, hposMono with
  | .cons L1 s1 (.cons L2 s2 (.cons L3 s3 (.nil _))), hposAct, hposMono =>
    -- Pin the activation slots via list injectivity.
    simp only [ActStack.activations, List.cons.injEq] at hposAct
    obtain ⟨hs1, hs2, hs3, -⟩ := hposAct
    subst s1; subst s2; subst s3
    -- Per-layer non-negative weights and non-negative read-out from `IsMonotone`.
    obtain ⟨⟨_, hW1⟩, ⟨_, hW2⟩, ⟨_, hW3⟩, -⟩ := hposMono.1
    have hrW : ∀ i, 0 ≤ readW i := hposMono.2
    -- Step 4: the negated, single-`σ` stack and net.
    set Sneg : ActStack d w :=
      .cons (Layer.neg L1) σ
        (.cons ({ W := -L2.W, c := L2.c } : Layer _ _) σ
          (.cons (Layer.neg L3) σ (.nil w))) with hSneg
    set Nneg : MonoNet d := ⟨w, Sneg, fun i => -(readW i), readBias⟩ with hNneg
    -- Step 5: `Sneg.toFun x' i = -(stack.toFun x' i)` pointwise.
    have hden : ∀ x', ∀ i,
        Sneg.toFun x' i =
          -((ActStack.cons L1 (reflect σ) (.cons L2 σ (.cons L3 (reflect σ) (.nil w)))).toFun
              x' i) := by
      intro x' i
      -- Layer 1: `L1.toFun (reflect σ) x' = fun i => -((Layer.neg L1).toFun σ x' i)`.
      have hL1 : L1.toFun (reflect σ) x' = fun i => -((Layer.neg L1).toFun σ x' i) := by
        have h := reflect_negLayer_toFun (Layer.neg L1) σ x'
        rw [Layer.neg_neg] at h
        exact h
      -- Layer 3 (same form).
      have hL3 : ∀ b, L3.toFun (reflect σ) b = fun i => -((Layer.neg L3).toFun σ b i) := by
        intro b
        have h := reflect_negLayer_toFun (Layer.neg L3) σ b
        rw [Layer.neg_neg] at h
        exact h
      -- Unfold both denotations inside-out.
      simp only [hSneg, ActStack.toFun]
      rw [hL1,
        negWeights_toFun L2 σ ((Layer.neg L1).toFun σ x'),
        hL3 (({ W := -L2.W, c := L2.c } : Layer _ _).toFun σ ((Layer.neg L1).toFun σ x'))]
      simp only [neg_neg]
    -- Step 6: `Nneg.toFun = Npos.toFun` (the sign flip is absorbed by `readW ↦ -readW`).
    have hNtoFun : ∀ x', Nneg.toFun x'
        = (∑ i, readW i *
            (ActStack.cons L1 (reflect σ) (.cons L2 σ (.cons L3 (reflect σ) (.nil w)))).toFun
              x' i) + readBias := by
      intro x'
      simp only [hNneg, MonoNet.toFun]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hden x' i]; ring
    -- Step 7: discharge all goals for `Nneg`.
    refine ⟨Nneg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- WeightsNonpos: each hidden layer's weights are ≤ 0.
      refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, trivial⟩
      · simp only [Layer.neg_W, Matrix.neg_apply]; exact neg_nonpos.2 (hW1 i j)
      · simp only [Matrix.neg_apply]; exact neg_nonpos.2 (hW2 i j)
      · simp only [Layer.neg_W, Matrix.neg_apply]; exact neg_nonpos.2 (hW3 i j)
    · -- Read-out weights ≤ 0.
      intro i; exact neg_nonpos.2 (hrW i)
    · -- Activations `[σ, σ, σ]`.
      rfl
    · -- Depth 4.
      rfl
    · -- Monotone `Nneg.toFun`: it agrees with the monotone `Npos.toFun`.
      have hmonoPos : Monotone
          (⟨w, .cons L1 (reflect σ) (.cons L2 σ (.cons L3 (reflect σ) (.nil w))), readW,
              readBias⟩ : MonoNet d).toFun :=
        MonoNet.monotone_toFun _ hposMono
      have heq : Nneg.toFun =
          (⟨w, .cons L1 (reflect σ) (.cons L2 σ (.cons L3 (reflect σ) (.nil w))), readW,
              readBias⟩ : MonoNet d).toFun := by
        funext x'; rw [hNtoFun x']; rfl
      rw [heq]; exact hmonoPos
    · -- ε bound: reuse `hposEps` after rewriting `Nneg.toFun = Npos.toFun`.
      intro i
      have heq : Nneg.toFun (x i) =
          (⟨w, .cons L1 (reflect σ) (.cons L2 σ (.cons L3 (reflect σ) (.nil w))), readW,
              readBias⟩ : MonoNet d).toFun (x i) := by
        rw [hNtoFun (x i)]; rfl
      rw [heq]; exact hposEps i

end UniversalApproximation.Sartor
