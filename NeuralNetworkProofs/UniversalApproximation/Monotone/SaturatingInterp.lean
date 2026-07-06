/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Saturating

/-!
# γ-normalized read-out engine + reindex scaffold (Sartor Theorem 3.5)

This file provides a self-contained reindex scaffold and a γ-normalized telescoping read-out
engine for the Sartor et al. (arXiv) Theorem 3.5 saturating-network universal approximation
construction.

The key design: instead of M-R's forward-difference weights `Δpotential`, here the weights are
`readW = Δpotential / γ`, where `γ` is the interior value of the saturating activation. The
telescoping identity becomes `∑ i, (Δpot i / γ) * (γ * 𝟙(i ≤ j)) + bias = y' j`, and the γ
factors cancel. This file mirrors `Interpolation.lean`'s Reindex and read-out sections, but with
all declarations PUBLIC and adapted for the γ-normalized setting.

The assembly (Phase 2) imports this file and applies the engine with the saturating approximation
from `Saturating.lean`.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

variable {d n : ℕ}

/-- Self-contained reindexing permutation: sort indices by the lexicographic key
`(y i, toLinearExtension (x i))`. Identical body to M-R's `reindex`, redefined here so this file
depends only on public API. -/
noncomputable def satReindex (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => toLex (y i, toLinearExtension (x i)))

/-- Along `satReindex`, `y` is nondecreasing. (via `Tuple.monotone_sort` + `Prod.Lex.le_iff`.) -/
theorem satReindex_y_monotone (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) {a b : Fin n}
    (hab : a ≤ b) : y (satReindex x y a) ≤ y (satReindex x y b) := by
  have h := Tuple.monotone_sort (fun i => toLex (y i, toLinearExtension (x i))) hab
  simp only [Function.comp_apply, Prod.Lex.le_iff, ofLex_toLex] at h
  rcases h with h | h
  · exact le_of_lt h
  · exact le_of_eq h.1

/-- `satReindex` linearly extends the coordinatewise order: comparability of the reindexed points
forces the index order. Direct application of public `sort_key_linear_extension y x hmono hinj`
(definitionally the same sort). -/
theorem satReindex_linear_extension (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) {a b : Fin n}
    (hx : x (satReindex x y a) ≤ x (satReindex x y b)) : a ≤ b :=
  sort_key_linear_extension y x hmono hinj hx

/-- Reindexed targets `y' i = y (satReindex i)`. -/
noncomputable def satReTarget (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  y (satReindex x y i)

/-- Telescoping potential: `Y k = y' (k-1)` in range (Nat sub gives `Y 0 = y' 0`), else 0. -/
noncomputable def satPotential (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if hk : k - 1 < n then satReTarget x y ⟨k - 1, hk⟩ else 0

/-- On the sampled range, the potential reads the target at shift `k+1`. -/
theorem satPotential_succ (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (k : Fin n) :
    satPotential x y (k + 1) = satReTarget x y k := by
  unfold satPotential
  have hk' : (k : ℕ) + 1 - 1 < n := by simp only [Nat.add_sub_cancel]; exact k.2
  rw [dif_pos hk']
  congr 1

/-- γ-normalized read-out weights: forward differences of the potential divided by `γ`. -/
noncomputable def satReadW (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (γ : ℝ) : Fin n → ℝ :=
  fun i => (satPotential x y ((i : ℕ) + 1) - satPotential x y (i : ℕ)) / γ

/-- Read-out bias: the potential base `Y 0`. -/
noncomputable def satReadBias (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℝ :=
  satPotential x y 0

/-- The read-out weights are non-negative when `γ > 0`: the forward difference of the potential is
`≥ 0` (targets nondecreasing along the reindex) and `γ > 0`. -/
theorem satReadW_nonneg (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (i : Fin n) : 0 ≤ satReadW x y γ i := by
  unfold satReadW
  apply div_nonneg _ hγ.le
  rw [sub_nonneg, satPotential_succ]
  unfold satPotential satReTarget
  have hi' : (i : ℕ) - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
  rw [dif_pos hi']
  apply satReindex_y_monotone
  simp only [Fin.le_def]; omega

/-- Normalized telescoping identity on the scaled exact indicator `γ · 𝟙(i ≤ j)`: the `γ` cancels
the `/γ` in the weights, then the forward differences telescope to `y' j` (mirror
`readout_telescope`, using `Finset.sum_range_sub`). -/
theorem satReadout_telescope (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (j : Fin n) :
    (∑ i, satReadW x y γ i * (γ * (if i ≤ j then (1 : ℝ) else 0))) + satReadBias x y
      = satReTarget x y j := by
  -- simplify each term: (Δpot i / γ) * (γ * c) = Δpot i * c
  have hstep : (∑ i, satReadW x y γ i * (γ * (if i ≤ j then (1 : ℝ) else 0)))
      = ∑ i : Fin n,
          (satPotential x y ((i : ℕ) + 1) - satPotential x y (i : ℕ))
          * (if (i : ℕ) ≤ (j : ℕ) then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold satReadW
    have hc : (if i ≤ j then (1 : ℝ) else 0) = (if (i : ℕ) ≤ (j : ℕ) then (1 : ℝ) else 0) :=
      rfl
    rw [hc, div_mul_eq_mul_div, mul_comm γ, mul_div_assoc, mul_div_cancel_right₀ _ hγ]
  rw [hstep]
  -- move to a sum over `Finset.range n`
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (satPotential x y (k + 1) - satPotential x y k)
        * (if k ≤ (j : ℕ) then (1 : ℝ) else 0))
      n]
  -- restrict to `range (j + 1)`: terms with `k > j` vanish
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range n :=
    Finset.range_subset_range.2 (Nat.succ_le_of_lt j.isLt)
  rw [← Finset.sum_subset hsub]
  · -- on `range (j + 1)` the indicator is `1`, then telescope forward differences
    have hind : ∀ k ∈ Finset.range ((j : ℕ) + 1),
        (satPotential x y (k + 1) - satPotential x y k)
        * (if k ≤ (j : ℕ) then (1 : ℝ) else 0)
        = satPotential x y (k + 1) - satPotential x y k := by
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [if_pos hk, mul_one]
    rw [Finset.sum_congr rfl hind, Finset.sum_range_sub (satPotential x y) ((j : ℕ) + 1)]
    -- the bias supplies `Y 0`, and `Y (j+1) = y' j`
    rw [satPotential_succ x y j]
    unfold satReadBias satReTarget
    ring
  · intro k _ hk
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
    rw [if_neg (by omega), mul_zero]

/-- **γ-normalized read-out error bound.** For any pre-read-out vector `v` within `η` of the scaled
indicator `γ · 𝟙(i ≤ j)`, the normalized telescoping read-out reproduces `y' j` to accuracy
`(∑ i, |satReadW γ i|) · η`. Mirror `readout_error_bound`: rewrite the target via
`satReadout_telescope`, then bound the linear read-out difference by `Finset.abs_sum_le_sum_abs`
and `abs_mul`. -/
theorem satReadout_error_bound (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) {γ : ℝ} (hγ : γ ≠ 0)
    (j : Fin n) {v : Fin n → ℝ} {η : ℝ}
    (hv : ∀ i, |v i - γ * (if i ≤ j then (1 : ℝ) else 0)| ≤ η) :
    |((∑ i, satReadW x y γ i * v i) + satReadBias x y) - satReTarget x y j|
      ≤ (∑ i, |satReadW x y γ i|) * η := by
  rw [← satReadout_telescope x y hγ j]
  have hdiff : ((∑ i, satReadW x y γ i * v i) + satReadBias x y)
      - ((∑ i, satReadW x y γ i * (γ * (if i ≤ j then (1 : ℝ) else 0)))
          + satReadBias x y)
      = ∑ i, satReadW x y γ i * (v i - γ * (if i ≤ j then (1 : ℝ) else 0)) := by
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [mul_sub])
  rw [hdiff, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)

/-- Layer 1 of the saturating interpolation net: coordinate half-space block layer with gain `lam`
and half-margin shift `mgn`. Neuron flattened from `(r, c)` reads coordinate `c` (weight `lam`) and
has bias `−lam·(mgn + (p r) c)`, so under an activation it computes `σ (lam·(x c − (p r) c − mgn))`.
Same block structure as `dominationLayer1`, scaled/shifted for the saturating construction. -/
noncomputable def satLayer1 (p : Fin n → (Fin d → ℝ)) (lam mgn : ℝ) :
    NeuralNetwork.Layer d (n * d) where
  W := fun q k => if k = (finProdFinEquiv.symm q).2 then lam else 0
  c := fun q => -lam * (mgn + (p (finProdFinEquiv.symm q).1) (finProdFinEquiv.symm q).2)

/-- Per-neuron value of layer 1 at the neuron flattened from `(r, c)`:
`σ (lam·(x c − (p r) c − mgn))`. Mirror `dominationLayer1_apply`. -/
theorem satLayer1_apply (p : Fin n → (Fin d → ℝ)) (σ : ℝ → ℝ) (lam mgn : ℝ)
    (x : Fin d → ℝ) (r : Fin n) (c : Fin d) :
    (satLayer1 p lam mgn).toFun σ x (finProdFinEquiv (r, c))
      = σ (lam * (x c - (p r) c - mgn)) := by
  unfold NeuralNetwork.Layer.toFun satLayer1
  congr 1
  rw [Matrix.mulVec]
  simp only [dotProduct, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl]; ring
  · intro k _ hk; rw [if_neg hk]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Below/equal bound (saturating side). If `σ` is left-saturating with left limit `L`, then for any
accuracy `ε>0` and half-margin `mgn>0` there is a gain threshold `Λ>0` such that for `lam ≥ Λ`,
whenever `x c ≤ (p r) c` (coordinate dominated-by, gap `≤ 0`), the layer-1 neuron is within `ε` of
`L`: `|σ (lam·(x c − (p r) c − mgn)) − L| ≤ ε`. -/
theorem satLayer1_below (σ : ℝ → ℝ) {L : ℝ} (hL : Filter.Tendsto σ Filter.atBot (nhds L))
    {ε mgn : ℝ} (hε : 0 < ε) (hmgn : 0 < mgn) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, t ≤ 0 →
      |σ (lam * (t - mgn)) - L| ≤ ε := by
  obtain ⟨Λ, hΛpos, hb⟩ := leftSaturating_scaled_approx hL hε hmgn
  exact ⟨Λ, hΛpos, fun lam hlam t ht => by
    have hs : t - mgn ≤ -mgn := by linarith
    exact hb lam hlam (t - mgn) hs⟩

/-- Above bound (non-saturating side, lower bound only). If `σ` is monotone and some value `σ z`
strictly exceeds the reference level `L` (`∃ z, L < σ z`, the non-degeneracy witness; in the
assembly `L = σ(−∞)`), then there is a separation `m₁>0` and a gain threshold `Λ>0` such that for
`lam ≥ Λ`, whenever `x c − (p r) c ≥ mgn·2` (i.e. `t ≥ mgn·2` so `t − mgn ≥ mgn`), the layer-1
neuron exceeds `L` by at least `m₁`: `L + m₁ ≤ σ (lam·(t − mgn))`. (Left-saturation of `σ` is not
needed here — only monotonicity and the witness.) -/
theorem satLayer1_above (σ : ℝ → ℝ) {L : ℝ}
    (hmono : Monotone σ) (hz : ∃ z, L < σ z) {mgn : ℝ} (hmgn : 0 < mgn) :
    ∃ m₁ : ℝ, 0 < m₁ ∧ ∃ Λ : ℝ, 0 < Λ ∧ ∀ lam : ℝ, Λ ≤ lam → ∀ t : ℝ, mgn * 2 ≤ t →
      L + m₁ ≤ σ (lam * (t - mgn)) := by
  obtain ⟨z, hz⟩ := hz
  refine ⟨σ z - L, by linarith, max 1 (z / mgn), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun lam hlam t ht => ?_⟩
  have hlam_pos : 0 < lam := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left _ _)) hlam
  have hmgn_le : t - mgn ≥ mgn := by linarith
  have hlam_ge : z / mgn ≤ lam := le_trans (le_max_right _ _) hlam
  have hzm : z ≤ lam * mgn := by
    rw [div_le_iff₀ hmgn] at hlam_ge; linarith
  have harg : lam * mgn ≤ lam * (t - mgn) :=
    mul_le_mul_of_nonneg_left hmgn_le (le_of_lt hlam_pos)
  have harg' : z ≤ lam * (t - mgn) := le_trans hzm harg
  have hσ : σ z ≤ σ (lam * (t - mgn)) := hmono harg'
  linarith

/-- Layer 2 of the saturating net: intersection block layer `Layer (n * d) n`. Neuron `i` sums
the `d` coordinate values of block `i` (weight `lam` on the block whose curried point index is
`i`), plus a bias `bsh`. Same block structure as `dominationLayer2`, with gain `lam` and a free
bias. -/
noncomputable def satLayer2 (d : ℕ) {n : ℕ} (lam bsh : ℝ) : NeuralNetwork.Layer (n * d) n where
  W := fun i q => if (finProdFinEquiv.symm q).1 = i then lam else 0
  c := fun _ => bsh

/-- Per-neuron value of layer 2 at neuron `i`: `σ (lam · ∑_c u (finProdFinEquiv (i,c)) + bsh)`.
Mirror `dominationStack_apply`'s layer-2 block-sum step. -/
theorem satLayer2_apply {n : ℕ} (lam bsh : ℝ) (σ : ℝ → ℝ) (u : Fin (n * d) → ℝ) (i : Fin n) :
    (satLayer2 d lam bsh).toFun σ u i
      = σ (lam * (∑ c : Fin d, u (finProdFinEquiv (i, c))) + bsh) := by
  unfold NeuralNetwork.Layer.toFun satLayer2
  congr 1
  have hsum : (Matrix.mulVec (fun i q => if (finProdFinEquiv.symm q).1 = i then lam else 0) u i)
      = lam * ∑ c : Fin d, u (finProdFinEquiv (i, c)) := by
    rw [Matrix.mulVec]
    simp only [dotProduct]
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · -- on-block: each `i`-block term rewrites to `lam * u (finProdFinEquiv (i, c))`
      rw [show ∑ c : Fin d,
              (if (finProdFinEquiv.symm (finProdFinEquiv (i, c))).1 = i then lam else 0)
                * u (finProdFinEquiv (i, c))
            = ∑ c : Fin d, lam * u (finProdFinEquiv (i, c)) from
          Finset.sum_congr rfl (fun c _ => by rw [Equiv.symm_apply_apply, if_pos rfl])]
      rw [← Finset.mul_sum]
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro c _
      rw [Equiv.symm_apply_apply, if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hsum]

/-- Layer 3 of the saturating net: strict-lower-prefix layer `Layer n n`. Neuron `i` sums the
values of all neurons `r < i` (weight `lam`, all `≥ 0`), plus a PER-NEURON bias `bsh i`. Like
`revPrefixLayer` but summing the strict lower prefix `r < i` instead of `i ≤ r`. The bias is a
function `Fin n → ℝ` because the assembly must absorb the `i`-dependent baseline `i · σ₂(+∞)` of the
variable-length prefix sum (a constant bias cannot). The per-neuron bias does not affect
monotonicity — only the weights must be non-negative. -/
noncomputable def satLayer3 (n : ℕ) (lam : ℝ) (bsh : Fin n → ℝ) : NeuralNetwork.Layer n n where
  W := fun i r => if r < i then lam else 0
  c := bsh

/-- Per-neuron value of layer 3 at neuron `i`:
`σ (lam · ∑_r (if r < i then v r else 0) + bsh i)`. -/
theorem satLayer3_apply (lam : ℝ) (bsh : Fin n → ℝ) (σ : ℝ → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (satLayer3 n lam bsh).toFun σ v i
      = σ (lam * (∑ r : Fin n, (if r < i then v r else 0)) + bsh i) := by
  unfold NeuralNetwork.Layer.toFun satLayer3
  congr 1
  have hsum : (Matrix.mulVec (fun i r => if r < i then lam else 0) v i)
      = lam * ∑ r : Fin n, (if r < i then v r else 0) := by
    rw [Matrix.mulVec]
    simp only [dotProduct]
    -- rewrite each term: `(if r < i then lam else 0) * v r = lam * (if r < i then v r else 0)`
    rw [show ∑ r : Fin n, (if r < i then lam else 0) * v r
          = ∑ r : Fin n, lam * (if r < i then v r else 0) from
        Finset.sum_congr rfl (fun r _ => by split_ifs <;> ring)]
    rw [← Finset.mul_sum]
  simp only [hsum]

end UniversalApproximation.Monotone
