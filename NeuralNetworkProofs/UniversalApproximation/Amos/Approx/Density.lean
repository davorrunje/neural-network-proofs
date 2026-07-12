/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Fintype.EquivFin
import NeuralNetworkProofs.UniversalApproximation.Amos.Approx.Tangent

/-!
# ICNN universal approximation for convex differentiable functions (Amos et al.)

`maxTangent_approx`: on a compact set `K`, a finite max of tangent planes of a convex differentiable
`f` approximates `f` uniformly to within any `ε`. Combined with the `maxAffine`-is-a-convex-ICNN
construction (`Approx/MaxAffine.lean`) this yields the convex UAP headline.

The upper estimate avoids any Lipschitz constant or operator-norm bound. At a net point `xᵢ` close
to the query `y`, the tangent value is `f xᵢ + fderiv ℝ f xᵢ (y - xᵢ)`; applying the tangent
minorant `convex_diff_tangent_le` at the reflected point `2•xᵢ - y` bounds
`-fderiv ℝ f xᵢ (y - xᵢ)` by `f (2•xᵢ - y) - f xᵢ`, and uniform continuity of `f` on a compact ball
controls both `f y - f xᵢ` and `f (2•xᵢ - y) - f xᵢ` by `ε/2`.
-/

namespace UniversalApproximation.Amos

open scoped Matrix

/-- The tangent-plane data `dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x)` evaluates at `y` to
the tangent value `f x + fderiv ℝ f x (y - x)`. -/
theorem dotAffine_gradVec {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x y : Fin d → ℝ) :
    dotAffine (gradVec f x) (f x - gradVec f x ⬝ᵥ x) y = f x + fderiv ℝ f x (y - x) := by
  unfold dotAffine
  rw [gradVec_dotProduct, gradVec_dotProduct, map_sub]
  ring

/-- A finite max of tangent planes of a convex differentiable `f` approximates `f` uniformly on any
compact set, from below everywhere and within `ε` on `K`. -/
theorem maxTangent_approx {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin (n + 1) → (Fin d → ℝ)) (b : Fin (n + 1) → ℝ),
      (∀ y, maxAffine n a b y ≤ f y) ∧ ∀ y ∈ K, f y - maxAffine n a b y ≤ ε := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Empty domain: a single tangent plane; the uniform bound is vacuous.
    refine ⟨0, fun _ => gradVec f 0, fun _ => f 0 - gradVec f 0 ⬝ᵥ 0, ?_, ?_⟩
    · intro y
      exact maxAffine_le 0 _ _ y (f y) (fun _ => tangent_le hf hd 0 y)
    · intro y hy; rw [hKe] at hy; exact (Set.mem_empty_iff_false y).1 hy |>.elim
  · -- Nonempty compact domain: cover by a finite δ-net and use the reflection estimate.
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hK.isBounded
    have hBcpt : IsCompact (Metric.closedBall (0 : Fin d → ℝ) (r + 1)) :=
      isCompact_closedBall _ _
    have hcont : ContinuousOn f (Metric.closedBall (0 : Fin d → ℝ) (r + 1)) :=
      hd.continuous.continuousOn
    have hunif := hBcpt.uniformContinuousOn_of_continuous hcont
    rw [Metric.uniformContinuousOn_iff] at hunif
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hunif (ε / 2) (by linarith)
    set δ := min δ₀ 1 with hδdef
    have hδpos : 0 < δ := lt_min hδ₀pos one_pos
    -- Finite δ-net of `K`.
    obtain ⟨t, hts, htfin, htcover⟩ := hK.finite_cover_balls hδpos
    set s := htfin.toFinset with hsdef
    have hsne : s.Nonempty := by
      obtain ⟨y0, hy0⟩ := hKne
      obtain ⟨p, hp, _⟩ := Set.mem_iUnion₂.1 (htcover hy0)
      exact ⟨p, htfin.mem_toFinset.2 hp⟩
    obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 :=
      ⟨s.card - 1, (Nat.succ_pred_eq_of_pos hsne.card_pos).symm⟩
    set e := (Finset.equivFinOfCardEq hn).symm with hedef
    set x : Fin (n + 1) → (Fin d → ℝ) := fun i => (e i : Fin d → ℝ) with hxdef
    have hxK : ∀ i, x i ∈ K := by
      intro i; rw [hxdef]; exact hts (htfin.mem_toFinset.1 (e i).2)
    set a : Fin (n + 1) → (Fin d → ℝ) := fun i => gradVec f (x i) with hadef
    set b : Fin (n + 1) → ℝ := fun i => f (x i) - gradVec f (x i) ⬝ᵥ x i with hbdef
    refine ⟨n, a, b, ?_, ?_⟩
    · -- Minorant: every tangent plane lies below `f`.
      intro y
      refine maxAffine_le n a b y (f y) (fun i => ?_)
      rw [hadef, hbdef]; exact tangent_le hf hd (x i) y
    · -- Uniform upper bound via the reflection estimate.
      intro y hy
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.1 (htcover hy)
      set i : Fin (n + 1) :=
        (Finset.equivFinOfCardEq hn) ⟨p, htfin.mem_toFinset.2 hp⟩ with hidef
      have hxi : x i = p := by
        rw [hxdef]; simp only [hedef, hidef, Equiv.symm_apply_apply]
      have hclose : dist y (x i) < δ := by rw [hxi]; exact Metric.mem_ball.1 hyp
      have hyB : y ∈ Metric.closedBall (0 : Fin d → ℝ) (r + 1) :=
        Metric.mem_closedBall.2 (le_trans (Metric.mem_closedBall.1 (hr hy)) (by linarith))
      have hxiB : x i ∈ Metric.closedBall (0 : Fin d → ℝ) (r + 1) :=
        Metric.mem_closedBall.2 (le_trans (Metric.mem_closedBall.1 (hr (hxK i))) (by linarith))
      set z : Fin d → ℝ := x i + (x i - y) with hzdef
      have hdistz : dist z (x i) = dist y (x i) := by
        rw [hzdef, dist_eq_norm, dist_eq_norm,
          show x i + (x i - y) - x i = x i - y by abel, norm_sub_rev]
      have hzB : z ∈ Metric.closedBall (0 : Fin d → ℝ) (r + 1) := by
        refine Metric.mem_closedBall.2 ?_
        have hxc : dist (x i) 0 ≤ r := Metric.mem_closedBall.1 (hr (hxK i))
        have hyxi : dist (x i) y ≤ 1 := by
          rw [dist_comm]; exact le_trans hclose.le (min_le_right _ _)
        calc dist z 0 = ‖z‖ := by rw [dist_zero_right]
          _ = ‖(x i - 0) + (x i - y)‖ := by rw [hzdef]; congr 1; abel
          _ ≤ ‖x i - 0‖ + ‖x i - y‖ := norm_add_le _ _
          _ = dist (x i) 0 + dist (x i) y := by rw [dist_eq_norm, dist_eq_norm]
          _ ≤ r + 1 := by linarith
      have hd1 : dist y (x i) < δ₀ := lt_of_lt_of_le hclose (min_le_left _ _)
      have hd2 : dist z (x i) < δ₀ := by rw [hdistz]; exact hd1
      have hfy : f y - f (x i) ≤ ε / 2 := by
        have h := hδ₀ y hyB (x i) hxiB hd1
        rw [Real.dist_eq] at h; exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
      have hfz : f z - f (x i) ≤ ε / 2 := by
        have h := hδ₀ z hzB (x i) hxiB hd2
        rw [Real.dist_eq] at h; exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
      -- Reflection: the tangent minorant at `z = 2•xᵢ - y`.
      have hrefl := convex_diff_tangent_le hf hd (x i) z
      rw [show z - x i = -(y - x i) by rw [hzdef]; abel, map_neg] at hrefl
      have heq : dotAffine (a i) (b i) y = f (x i) + fderiv ℝ f (x i) (y - x i) := by
        rw [hadef, hbdef]; exact dotAffine_gradVec f (x i) y
      have hmax := le_maxAffine n a b y i
      linarith

/-- **Universal approximation.** A convex, differentiable function is uniformly approximated on any
compact set by a fully input-convex network (with nonnegative propagation weights and convex
nondecreasing activations). -/
theorem icnn_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ICNN d 0 1, N.IsConvex ∧ ∀ y ∈ K, |N.toFun y - f y| ≤ ε := by
  obtain ⟨n, a, b, hle, hunif⟩ := maxTangent_approx hf hd hK hε
  obtain ⟨N, hNconv, hNeq⟩ := maxAffine_isICNN a b
  refine ⟨N, hNconv, fun y hy => ?_⟩
  rw [hNeq]
  have h1 : maxAffine n a b y - f y ≤ 0 := sub_nonpos.mpr (hle y)
  have h2 : f y - maxAffine n a b y ≤ ε := hunif y hy
  rw [abs_le]; constructor <;> [linarith; linarith]

end UniversalApproximation.Amos
