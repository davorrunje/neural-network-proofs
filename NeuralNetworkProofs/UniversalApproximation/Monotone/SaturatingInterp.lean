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

/-- The list of per-layer activations of a stack (for stating which activations a net uses). -/
def ActStack.activations : {a b : ℕ} → ActStack a b → List (ℝ → ℝ)
  | _, _, .nil _ => []
  | _, _, .cons _ σ rest => σ :: rest.activations

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

/-!
## Analysis foundations for the depth-4 assembly

The following five lemmas are self-contained analysis foundations used by the Theorem 3.5
depth-4 assembly: saturation-limit bounds, continuity-point existence for monotone functions,
and a finite coordinate-margin lemma.
-/

/-- For a monotone `σ` with left limit `L` at `−∞`, `L` is a lower bound: `L ≤ σ x` for all
`x`. (The limit at `atBot` is the infimum.) -/
theorem monotone_atBot_le {σ : ℝ → ℝ} {L : ℝ} (hmono : Monotone σ)
    (hL : Filter.Tendsto σ Filter.atBot (nhds L)) (x : ℝ) : L ≤ σ x :=
  Monotone.le_of_tendsto hmono hL x

/-- For a monotone `σ` with right limit `L` at `+∞`, `L` is an upper bound: `σ x ≤ L`
for all `x`. -/
theorem monotone_le_atTop {σ : ℝ → ℝ} {L : ℝ} (hmono : Monotone σ)
    (hL : Filter.Tendsto σ Filter.atTop (nhds L)) (x : ℝ) : σ x ≤ L :=
  Monotone.ge_of_tendsto hmono hL x

/-- A monotone function has a continuity point at which its value is strictly below any level
`L` that it is somewhere below. (Continuity points of a monotone function are co-countable,
hence dense; the sublevel set `{z | σ z < L}` contains a nondegenerate interval when nonempty.)
-/
theorem exists_continuousAt_lt_of_monotone {σ : ℝ → ℝ} {L : ℝ} (hmono : Monotone σ)
    (ha : ∃ a, σ a < L) : ∃ b, ContinuousAt σ b ∧ σ b < L := by
  obtain ⟨a, haL⟩ := ha
  let D := {x | ¬ContinuousAt σ x}
  have hD : D.Countable := hmono.countable_not_continuousAt
  have hdense : Dense Dᶜ := hD.dense_compl ℝ
  have hopen : IsOpen (Set.Ioo (a - 1) a) := isOpen_Ioo
  have hne : (Set.Ioo (a - 1) a).Nonempty := ⟨a - 1 / 2, by constructor <;> linarith⟩
  obtain ⟨b, hbI, hbD⟩ := hdense.inter_open_nonempty (Set.Ioo (a - 1) a) hopen hne
  simp only [D, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hbD
  exact ⟨b, hbD, lt_of_le_of_lt (hmono (le_of_lt hbI.2)) haL⟩

/-- Dual: a monotone function has a continuity point at which its value is strictly above any
level `L` that it is somewhere above. -/
theorem exists_continuousAt_gt_of_monotone {σ : ℝ → ℝ} {L : ℝ} (hmono : Monotone σ)
    (ha : ∃ a, L < σ a) : ∃ b, ContinuousAt σ b ∧ L < σ b := by
  obtain ⟨a, haL⟩ := ha
  let D := {x | ¬ContinuousAt σ x}
  have hD : D.Countable := hmono.countable_not_continuousAt
  have hdense : Dense Dᶜ := hD.dense_compl ℝ
  have hopen : IsOpen (Set.Ioo a (a + 1)) := isOpen_Ioo
  have hne : (Set.Ioo a (a + 1)).Nonempty := ⟨a + 1 / 2, by constructor <;> linarith⟩
  obtain ⟨b, hbI, hbD⟩ := hdense.inter_open_nonempty (Set.Ioo a (a + 1)) hopen hne
  simp only [D, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hbD
  exact ⟨b, hbD, lt_of_lt_of_le haL (hmono (le_of_lt hbI.1))⟩

/-- Finite coordinate margin: for finitely many points `p : Fin n → (Fin d → ℝ)` there is
`m > 0` such that any two coordinate values are either equal or at least `m` apart. -/
theorem exists_coord_margin {d n : ℕ} (p : Fin n → (Fin d → ℝ)) :
    ∃ m : ℝ, 0 < m ∧ ∀ a b : Fin n, ∀ c : Fin d,
      (p a) c ≠ (p b) c → m ≤ |(p a) c - (p b) c| := by
  let S : Finset ℝ := ((Finset.univ : Finset (Fin n × Fin n × Fin d)).image
    (fun t => |(p t.1) t.2.2 - (p t.2.1) t.2.2|)).filter (fun z => z ≠ 0)
  by_cases hne : S.Nonempty
  · refine ⟨S.min' hne, ?_, fun a b c hneq => ?_⟩
    · rw [Finset.lt_min'_iff]
      intro z hz
      simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨⟨t, _, rfl⟩, hnez⟩ := hz
      exact abs_pos.mpr (abs_ne_zero.mp hnez)
    · apply Finset.min'_le
      rw [Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨(a, b, c), Finset.mem_univ _, rfl⟩, by rwa [abs_ne_zero, sub_ne_zero]⟩
  · refine ⟨1, one_pos, fun a b c hneq => absurd ?_ hne⟩
    exact ⟨|(p a) c - (p b) c|, by
      rw [Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨(a, b, c), Finset.mem_univ _, rfl⟩, by rwa [abs_ne_zero, sub_ne_zero]⟩⟩

/-!
## The depth-3 saturating pre-read-out approximation (Sartor Theorem 3.5, heart)

The single hardest proof of the development: a 3-layer saturating stack (Case 1,
`σ₁∈𝒮⁻, σ₂∈𝒮⁺, σ₃∈𝒮⁻`) approximates, at each reindexed data point `p j`, the scaled level-set
indicator `base + γ₃·𝟙(i ≤ j)`. The gains are chosen backward and finitely (`lam₃`, then `lam₂`,
then `lam₁`), each from the quantitative saturation/continuity lemmas of `Saturating.lean`.
-/

/-- **Sartor Theorem 3.5 heart (depth-3 saturating pre-read-out approximation).**
For monotone, one-sided-saturating, non-constant activations `σ₁∈𝒮⁻, σ₂∈𝒮⁺, σ₃∈𝒮⁻`, there is a
3-layer monotone stack `S` (weights `≥ 0`, activations `[σ₁,σ₂,σ₃]`) and constants `base, γ₃` with
`γ₃ > 0` such that, at every reindexed data point `p j = x (satReindex x y j)`, the pre-read-out
output `S.toFun (p j) i` is within `η` of the scaled level-set indicator
`base + γ₃·𝟙(i ≤ j)`. Feeding this into the γ-normalized read-out engine
(`satReadout_error_bound`) yields the interpolation of `y`. -/
theorem sat_preadout_approx {d n : ℕ} (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x)
    (σ₁ σ₂ σ₃ : ℝ → ℝ) (hm₁ : Monotone σ₁) (hm₂ : Monotone σ₂) (hm₃ : Monotone σ₃)
    (hs₁ : LeftSaturating σ₁) (hs₂ : RightSaturating σ₂) (hs₃ : LeftSaturating σ₃)
    (hnc₁ : ∃ a b, σ₁ a < σ₁ b) (hnc₂ : ∃ a b, σ₂ a < σ₂ b) (hnc₃ : ∃ a b, σ₃ a < σ₃ b)
    {η : ℝ} (hη : 0 < η) :
    ∃ (S : ActStack d n) (base γ₃ : ℝ), 0 < γ₃ ∧ S.IsMonotone ∧ S.depth = 3 ∧
      S.activations = [σ₁, σ₂, σ₃] ∧
      ∀ j i : Fin n, |S.toFun (x (satReindex x y j)) i
        - (base + γ₃ * (if i ≤ j then (1 : ℝ) else 0))| ≤ η := by
  classical
  -- Reindexed points.
  set p : Fin n → (Fin d → ℝ) := fun r => x (satReindex x y r) with hp
  -- Saturation limits.
  obtain ⟨c₁, hL₁⟩ := hs₁
  obtain ⟨c₂, hL₂⟩ := hs₂
  obtain ⟨c₃, hL₃⟩ := hs₃
  -- `c₁` is a lower bound, `c₂` an upper bound, `c₃` a lower bound.
  have hc₁le : ∀ z, c₁ ≤ σ₁ z := monotone_atBot_le hm₁ hL₁
  have hc₂ge : ∀ z, σ₂ z ≤ c₂ := monotone_le_atTop hm₂ hL₂
  have hc₃le : ∀ z, c₃ ≤ σ₃ z := monotone_atBot_le hm₃ hL₃
  -- Coordinate margin.
  obtain ⟨m, hmpos, hgap⟩ := exists_coord_margin p
  set mgn : ℝ := m / 2 with hmgn
  have hmgnpos : 0 < mgn := by rw [hmgn]; linarith
  -- L1 non-degeneracy witness: some value strictly above `c₁`.
  have hz₁ : ∃ z, c₁ < σ₁ z := by
    obtain ⟨a, b, hab⟩ := hnc₁
    exact ⟨b, lt_of_le_of_lt (hc₁le a) hab⟩
  -- L1 separation `m₁` and above-threshold `Λ₁a` (gain-independent existence).
  obtain ⟨m₁, hm₁pos, Λ₁a, hΛ₁a_pos, hL1above⟩ := satLayer1_above σ₁ hm₁ hz₁ hmgnpos
  -- `b₂`: continuity point with `σ₂ b₂ < c₂`; `γ₂ := σ₂ b₂ − c₂ < 0`.
  have hb₂ex : ∃ a, σ₂ a < c₂ := by
    obtain ⟨a, b, hab⟩ := hnc₂
    exact ⟨a, lt_of_lt_of_le hab (hc₂ge b)⟩
  obtain ⟨b₂, hcont₂, hb₂lt⟩ := exists_continuousAt_lt_of_monotone hm₂ hb₂ex
  set γ₂ : ℝ := σ₂ b₂ - c₂ with hγ₂
  have hγ₂neg : γ₂ < 0 := by rw [hγ₂]; linarith
  -- `b₃`: continuity point with `c₃ < σ₃ b₃`; `γ₃ := σ₃ b₃ − c₃ > 0`, `base := c₃`.
  have hb₃ex : ∃ a, c₃ < σ₃ a := by
    obtain ⟨a, b, hab⟩ := hnc₃
    exact ⟨b, lt_of_le_of_lt (hc₃le a) hab⟩
  obtain ⟨b₃, hcont₃, hb₃gt⟩ := exists_continuousAt_gt_of_monotone hm₃ hb₃ex
  set γ₃ : ℝ := σ₃ b₃ - c₃ with hγ₃
  have hγ₃pos : 0 < γ₃ := by rw [hγ₃]; linarith
  -- L3 outside margin.
  set m₃ : ℝ := -γ₂ / 2 with hm₃def
  have hm₃pos : 0 < m₃ := by rw [hm₃def]; linarith
  -- BACKWARD GAIN CHAIN.
  -- L3 interior radius (accuracy `η` at `b₃`).
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := approx_interior_value hcont₃ hη
  -- L3 outside threshold `lam₃` (accuracy `η`, margin `m₃`, bias `b₃`).
  obtain ⟨lam₃, hlam₃pos, hL3out⟩ := leftSaturating_scaled_approx_bias
    (b := b₃) hL₃ hη hm₃pos
  -- L2 accuracy `ε₂`: small enough for the L3 outside sum and interior drift.
  set ε₂ : ℝ := min (m₃ / (n + 1)) (δ₃ / (lam₃ * (n + 1))) with hε₂def
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hε₂pos : 0 < ε₂ := by
    rw [hε₂def]; refine lt_min ?_ ?_
    · positivity
    · positivity
  have hε₂le1 : ε₂ ≤ m₃ / (n + 1) := (min_le_left _ _).trans_eq rfl
  have hε₂le2 : ε₂ ≤ δ₃ / (lam₃ * (n + 1)) := (min_le_right _ _).trans_eq rfl
  -- L2 interior radius (accuracy `ε₂` at `b₂`).
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := approx_interior_value hcont₂ hε₂pos
  -- L2 outside threshold `lam₂` (accuracy `ε₂`, margin `m₁`, bias `b₂`).
  obtain ⟨lam₂, hlam₂pos, hL2out⟩ := rightSaturating_scaled_approx_bias
    (b := b₂) hL₂ hε₂pos hm₁pos
  -- L1 accuracy `δ₁`: small enough that L2's interior drift stays within `δ₂`.
  set δ₁ : ℝ := δ₂ / (lam₂ * (d + 1)) with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; positivity
  -- L1 below threshold `Λ₁b` (accuracy `δ₁`, half-margin `mgn`).
  obtain ⟨Λ₁b, hΛ₁b_pos, hL1below⟩ := satLayer1_below σ₁ hL₁ hδ₁pos hmgnpos
  -- L1 gain: satisfy both above and below thresholds.
  set lam₁ : ℝ := max Λ₁a Λ₁b with hlam₁def
  have hlam₁pos : 0 < lam₁ := by rw [hlam₁def]; exact lt_of_lt_of_le hΛ₁a_pos (le_max_left _ _)
  have hlam₁a : Λ₁a ≤ lam₁ := le_max_left _ _
  have hlam₁b : Λ₁b ≤ lam₁ := le_max_right _ _
  -- The stack biases.
  set bsh₂ : ℝ := b₂ - lam₂ * d * c₁ with hbsh₂
  set bsh₃ : Fin n → ℝ := fun i => b₃ - lam₃ * (i : ℝ) * c₂ with hbsh₃
  -- The explicit stack.
  set S : ActStack d n :=
    .cons (satLayer1 p lam₁ mgn) σ₁
      (.cons (satLayer2 d lam₂ bsh₂) σ₂
        (.cons (satLayer3 n lam₃ bsh₃) σ₃ (.nil n))) with hS
  refine ⟨S, c₃, γ₃, hγ₃pos, ?_, ?_, ?_, ?_⟩
  · -- IsMonotone: each layer has non-negative weights and a monotone activation.
    refine ⟨⟨hm₁, ?_⟩, ⟨hm₂, ?_⟩, ⟨hm₃, ?_⟩, trivial⟩
    · intro i j; simp only [satLayer1]; split_ifs
      · exact hlam₁pos.le
      · exact le_refl 0
    · intro i j; simp only [satLayer2]; split_ifs
      · exact hlam₂pos.le
      · exact le_refl 0
    · intro i j; simp only [satLayer3]; split_ifs
      · exact hlam₃pos.le
      · exact le_refl 0
  · rfl
  · rfl
  · -- The per-neuron bound.
    intro j i
    -- Closed forms of the three layers at input `p j`.
    set u : Fin (n * d) → ℝ := (satLayer1 p lam₁ mgn).toFun σ₁ (p j) with hu
    set D : Fin n → ℝ := (satLayer2 d lam₂ bsh₂).toFun σ₂ u with hD
    set V : Fin n → ℝ := (satLayer3 n lam₃ bsh₃).toFun σ₃ D with hV
    have hStoFun : S.toFun (p j) i = V i := rfl
    rw [hStoFun]
    -- L1 per-neuron closed form and bounds at coordinate `(r, c)`.
    have hu_apply : ∀ r : Fin n, ∀ c : Fin d,
        u (finProdFinEquiv (r, c)) = σ₁ (lam₁ * ((p j) c - (p r) c - mgn)) := by
      intro r c; rw [hu]; exact satLayer1_apply p σ₁ lam₁ mgn (p j) r c
    -- Always `c₁ ≤ u(r,c)`.
    have hu_ge : ∀ r : Fin n, ∀ c : Fin d, c₁ ≤ u (finProdFinEquiv (r, c)) := by
      intro r c; rw [hu_apply]; exact hc₁le _
    -- Below/inside: `(p j) c ≤ (p r) c ⇒ |u(r,c) − c₁| ≤ δ₁`.
    have hu_below : ∀ r : Fin n, ∀ c : Fin d, (p j) c ≤ (p r) c →
        |u (finProdFinEquiv (r, c)) - c₁| ≤ δ₁ := by
      intro r c hle
      rw [hu_apply]
      exact hL1below lam₁ hlam₁b ((p j) c - (p r) c) (by linarith)
    -- Above/outside coordinate: `(p r) c < (p j) c ⇒ c₁ + m₁ ≤ u(r,c)`.
    have hu_above : ∀ r : Fin n, ∀ c : Fin d, (p r) c < (p j) c →
        c₁ + m₁ ≤ u (finProdFinEquiv (r, c)) := by
      intro r c hlt
      rw [hu_apply]
      have hgapc : m ≤ |(p j) c - (p r) c| :=
        hgap j r c (by intro h; rw [h] at hlt; exact lt_irrefl _ hlt)
      have habs : |(p j) c - (p r) c| = (p j) c - (p r) c := abs_of_pos (by linarith)
      have ht : mgn * 2 ≤ (p j) c - (p r) c := by
        rw [hmgn]; rw [habs] at hgapc; linarith
      exact hL1above lam₁ hlam₁a ((p j) c - (p r) c) ht
    -- L2 per-neuron closed form: `D r = σ₂ (lam₂ · (s r) + b₂)` with `s r = ∑_c (u(r,c) − c₁)`.
    set s : Fin n → ℝ := fun r => ∑ c : Fin d, (u (finProdFinEquiv (r, c)) - c₁) with hs
    have hD_arg : ∀ r : Fin n,
        lam₂ * (∑ c : Fin d, u (finProdFinEquiv (r, c))) + bsh₂ = lam₂ * (s r) + b₂ := by
      intro r
      have hsr : s r = (∑ c : Fin d, u (finProdFinEquiv (r, c))) - d * c₁ := by
        rw [hs]; simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [hsr, hbsh₂]; ring
    have hD_apply : ∀ r : Fin n, D r = σ₂ (lam₂ * (s r) + b₂) := by
      intro r; rw [hD, satLayer2_apply lam₂ bsh₂ σ₂ u r, hD_arg r]
    -- `lam₂ · d · δ₁ ≤ δ₂` (from the choice of `δ₁`).
    have hdenpos : (0 : ℝ) < lam₂ * (d + 1) := by positivity
    have hlam₂dδ₁ : lam₂ * (d : ℝ) * δ₁ ≤ δ₂ := by
      rw [hδ₁def, ← mul_div_assoc, div_le_iff₀ hdenpos]
      have hdd : (d : ℝ) ≤ d + 1 := by linarith
      nlinarith [hδ₂pos.le, hlam₂pos.le, Nat.cast_nonneg (α := ℝ) d]
    -- Inside: each term `∈ [0, δ₁]`, so `s r ∈ [0, d·δ₁]` and `|D r − σ₂ b₂| ≤ ε₂`.
    have hD_inside : ∀ r : Fin n, p j ≤ p r → |D r - σ₂ b₂| ≤ ε₂ := by
      intro r hle
      rw [hD_apply]
      -- `s r` is within `d·δ₁` of `0`.
      have hterm_lo : ∀ c : Fin d, 0 ≤ u (finProdFinEquiv (r, c)) - c₁ := by
        intro c; linarith [hu_ge r c]
      have hterm_hi : ∀ c : Fin d, u (finProdFinEquiv (r, c)) - c₁ ≤ δ₁ := by
        intro c
        have := hu_below r c (hle c)
        rw [abs_le] at this; linarith [this.2]
      have hsr_lo : 0 ≤ s r := Finset.sum_nonneg (fun c _ => hterm_lo c)
      have hsr_hi : s r ≤ (d : ℝ) * δ₁ := by
        calc s r ≤ ∑ _c : Fin d, δ₁ := Finset.sum_le_sum (fun c _ => hterm_hi c)
          _ = (d : ℝ) * δ₁ := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      -- pre-activation within `δ₂` of `b₂`.
      have hpre : |lam₂ * (s r) + b₂ - b₂| ≤ δ₂ := by
        have h0 : lam₂ * (s r) + b₂ - b₂ = lam₂ * (s r) := by ring
        rw [h0, abs_of_nonneg (mul_nonneg hlam₂pos.le hsr_lo)]
        calc lam₂ * (s r) ≤ lam₂ * ((d : ℝ) * δ₁) :=
              mul_le_mul_of_nonneg_left hsr_hi hlam₂pos.le
          _ = lam₂ * (d : ℝ) * δ₁ := by ring
          _ ≤ δ₂ := hlam₂dδ₁
      exact hδ₂ _ hpre
    -- Outside: some coord above ⇒ `s r ≥ m₁` and `|D r − c₂| ≤ ε₂`.
    have hD_outside : ∀ r : Fin n, ¬ (p j ≤ p r) → |D r - c₂| ≤ ε₂ := by
      intro r hnle
      rw [hD_apply]
      -- extract the distinguished coordinate.
      rw [Pi.le_def] at hnle
      push Not at hnle
      obtain ⟨c₀, hc₀⟩ := hnle
      have hterm_nonneg : ∀ c : Fin d, 0 ≤ u (finProdFinEquiv (r, c)) - c₁ := by
        intro c; linarith [hu_ge r c]
      have hsr_ge : m₁ ≤ s r := by
        rw [hs]
        refine sum_ge_of_single Finset.univ _ (Finset.mem_univ c₀) ?_
          (fun c _ => hterm_nonneg c)
        linarith [hu_above r c₀ hc₀]
      exact hL2out lam₂ (le_refl lam₂) (s r) hsr_ge
    -- In all cases `D r − c₂ ≤ ε₂`.
    have hD_above : ∀ r : Fin n, D r - c₂ ≤ ε₂ := by
      intro r
      by_cases hle : p j ≤ p r
      · have := hD_inside r hle
        rw [abs_le] at this
        have : D r ≤ σ₂ b₂ + ε₂ := by linarith [this.2]
        rw [hγ₂] at hγ₂neg; linarith
      · have := hD_outside r hle
        rw [abs_le] at this; linarith [this.2]
    -- Global tolerance facts used by L3.
    have hnε₂ : (n : ℝ) * ε₂ ≤ m₃ := by
      have := hε₂le1
      rw [le_div_iff₀ hnp] at this
      nlinarith [hε₂pos.le, hm₃pos.le]
    have hlam₃nε₂ : lam₃ * ((n : ℝ) * ε₂) ≤ δ₃ := by
      have := hε₂le2
      rw [le_div_iff₀ (by positivity)] at this
      have hnn : (n : ℝ) ≤ n + 1 := by linarith
      nlinarith [hε₂pos.le, hlam₃pos.le, Nat.cast_nonneg (α := ℝ) n]
    -- L3 per-neuron closed form: `V i = σ₃ (lam₃ · (T i) + b₃)`,
    -- `T i = ∑_r (if r < i then (D r − c₂) else 0)`.
    set T : Fin n → ℝ := fun i => ∑ r : Fin n, (if r < i then D r - c₂ else 0) with hT
    have hcount : ∀ i : Fin n, (∑ r : Fin n, if r < i then (c₂ : ℝ) else 0) = (i : ℝ) * c₂ := by
      intro i
      have hcard : (∑ r : Fin n, if r < i then (1 : ℝ) else 0) = (i : ℝ) := by
        rw [Finset.sum_boole]
        have heq : (Finset.univ.filter (fun r : Fin n => r < i)) = Finset.Iio i := by
          ext r; simp [Finset.mem_Iio]
        rw [heq, Fin.card_Iio]
      calc (∑ r : Fin n, if r < i then (c₂ : ℝ) else 0)
          = ∑ r : Fin n, c₂ * (if r < i then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl; intro r _; split_ifs <;> ring
        _ = c₂ * (∑ r : Fin n, if r < i then (1 : ℝ) else 0) := by rw [Finset.mul_sum]
        _ = (i : ℝ) * c₂ := by rw [hcard]; ring
    have hV_apply : ∀ i : Fin n, V i = σ₃ (lam₃ * (T i) + b₃) := by
      intro i
      rw [hV, satLayer3_apply lam₃ bsh₃ σ₃ D i, hbsh₃]
      congr 1
      have hsplit : (∑ r : Fin n, if r < i then D r else 0)
          = T i + (i : ℝ) * c₂ := by
        simp only [hT]
        rw [← hcount i, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _; split_ifs <;> ring
      rw [hsplit]; ring
    -- Now the per-neuron bound, by case on `i ≤ j`.
    rw [hV_apply i]
    by_cases hij : i ≤ j
    · -- Interior case: every `r < i` is outside, so `|T i| ≤ n·ε₂`, and `V i ≈ σ₃ b₃`.
      rw [if_pos hij, mul_one]
      have hT_bound : |T i| ≤ (n : ℝ) * ε₂ := by
        simp only [hT]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hterm : ∀ r : Fin n, |if r < i then D r - c₂ else 0| ≤ ε₂ := by
          intro r
          by_cases hr : r < i
          · rw [if_pos hr, abs_le]
            have hlt : r < j := lt_of_lt_of_le hr hij
            have hnle : ¬ (p j ≤ p r) := by
              intro hle
              exact absurd (satReindex_linear_extension x y hmono hinj hle)
                (not_le.mpr hlt)
            have := hD_outside r hnle; rw [abs_le] at this
            exact ⟨by linarith [this.1], by linarith [this.2]⟩
          · rw [if_neg hr, abs_zero]; exact hε₂pos.le
        calc (∑ r : Fin n, |if r < i then D r - c₂ else 0|)
            ≤ ∑ _r : Fin n, ε₂ := Finset.sum_le_sum (fun r _ => hterm r)
          _ = (n : ℝ) * ε₂ := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hpre : |lam₃ * (T i) + b₃ - b₃| ≤ δ₃ := by
        have h0 : lam₃ * (T i) + b₃ - b₃ = lam₃ * (T i) := by ring
        rw [h0, abs_mul, abs_of_pos hlam₃pos]
        calc lam₃ * |T i| ≤ lam₃ * ((n : ℝ) * ε₂) :=
              mul_le_mul_of_nonneg_left hT_bound hlam₃pos.le
          _ ≤ δ₃ := hlam₃nε₂
      have hVi := hδ₃ _ hpre
      -- target `c₃ + γ₃ = σ₃ b₃`.
      have htgt : c₃ + γ₃ = σ₃ b₃ := by rw [hγ₃]; ring
      rw [htgt]; exact hVi
    · -- Outside case `j < i`: `T i ≤ −m₃`, so `V i ≈ c₃`.
      rw [if_neg hij, mul_zero, add_zero]
      have hji : j < i := not_le.mp hij
      have hjlt : j < i := hji
      have hT_le : T i ≤ -m₃ := by
        simp only [hT]
        -- separate the `r = j` term.
        rw [← Finset.add_sum_erase Finset.univ (fun r => if r < i then D r - c₂ else 0)
          (Finset.mem_univ j)]
        rw [if_pos hjlt]
        -- `D j − c₂ ≤ γ₂ + ε₂`.
        have hDj : D j - c₂ ≤ γ₂ + ε₂ := by
          have := hD_inside j (le_refl (p j)); rw [abs_le] at this
          rw [hγ₂]; linarith [this.2]
        -- rest terms `≤ ε₂` each.
        have hrest : (∑ r ∈ Finset.univ.erase j, if r < i then D r - c₂ else 0)
            ≤ ((n : ℝ) - 1) * ε₂ := by
          have hbound : ∀ r ∈ Finset.univ.erase j,
              (if r < i then D r - c₂ else 0) ≤ ε₂ := by
            intro r _; by_cases hr : r < i
            · rw [if_pos hr]; exact hD_above r
            · rw [if_neg hr]; exact hε₂pos.le
          refine le_trans (Finset.sum_le_sum hbound) ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : (Finset.univ.erase j).card = n - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
              Fintype.card_fin]
          rw [hcard]
          have hn1 : 1 ≤ n := Nat.one_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
          rw [Nat.cast_sub hn1, Nat.cast_one]
        -- combine: `T i ≤ (γ₂ + ε₂) + (n−1)·ε₂ = γ₂ + n·ε₂ ≤ γ₂ + m₃ = −m₃`.
        have hsum : (D j - c₂) + ((n : ℝ) - 1) * ε₂ ≤ -m₃ := by
          have hexp : (D j - c₂) + ((n : ℝ) - 1) * ε₂
              ≤ (γ₂ + ε₂) + ((n : ℝ) - 1) * ε₂ := by linarith [hDj]
          have hnexp : (γ₂ + ε₂) + ((n : ℝ) - 1) * ε₂ = γ₂ + (n : ℝ) * ε₂ := by ring
          have hfin : γ₂ + (n : ℝ) * ε₂ ≤ -m₃ := by
            rw [hm₃def]; linarith [hnε₂, hm₃def]
          linarith [hexp, hnexp ▸ le_refl (γ₂ + (n : ℝ) * ε₂)]
        linarith [hrest, hsum, hDj]
      have hVi := hL3out lam₃ (le_refl lam₃) (T i) hT_le
      rw [abs_le] at hVi ⊢
      exact ⟨by linarith [hVi.1], by linarith [hVi.2]⟩

end UniversalApproximation.Monotone
