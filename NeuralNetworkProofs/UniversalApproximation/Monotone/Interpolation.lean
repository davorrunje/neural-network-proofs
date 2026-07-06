/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Indicator
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic

/-!
# Monotone interpolation (Theorem 1)

This file proves that any monotone, injective finite dataset can be interpolated exactly by a
depth-`4` monotone threshold network (Mikulincer–Reichman, arXiv:2207.05275, Result 1, paper
layers 3–4 plus the essential reindexing).

The construction is a depth-`4` `MonoNet`: an ε-indicator gadget for the reindexed points (paper
layers 1–2, supplied by `Indicator.dominationStack`), a reverse-prefix-sum level-set layer
(`revPrefixLayer`, layer 3, built with `heaviside`), and a telescoping non-negative linear read-out
(layer 4).  The interpolation identity is obtained by *routing the domination step through the
shared ε-indicator infrastructure* (`IsEpsIndicator`, `dominationStack_apply`): the gadget supplies
the exact (`ε = 0`) domination indicators consumed by the level-set layer.

* `readout_error_bound` — the *sound* general engine step: for any pre-read-out level-set vector
  approximating the prefix indicator `𝟙(i ≤ j)` to accuracy `η`, the telescoping read-out
  reproduces the reindexed target `y' j` to accuracy `(∑ i, |readW i|) · η`.  (The gadget's `ε` does
  *not* propagate through the discontinuous `heaviside` level-set layer 3, so the engine is stated
  at the pre-read-out boundary, where the error is genuinely linear; see the note below.)
* `monotone_interpolation` — the headline: given points `x` and targets `y` with `y` monotone
  along the coordinatewise order and `x` injective, there is a monotone `MonoNet` of depth `4`
  agreeing with `y` on every `x i`.  Derived through the exact (`ε = 0`) engine instance, so the
  level-set vector is `𝟙(i ≤ j)` on the nose (`η = 0`) and the read-out is exact.
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

section Reindex

variable {d n : ℕ}

/-- The sorting key: pair the target `y i` with the point `x i` viewed in a linear extension of
the coordinatewise order.  Sorting by this lexicographic key yields an order that both makes `y`
nondecreasing and refines the coordinatewise order on the points. -/
private noncomputable def sortKey (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    Fin n → (ℝ ×ₗ LinearExtension (Fin d → ℝ)) :=
  fun i => toLex (y i, toLinearExtension (x i))

/-- The reindexing permutation: sort the indices by `sortKey`. -/
private noncomputable def reindex (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    Equiv.Perm (Fin n) :=
  Tuple.sort (sortKey x y)

/-- Along the reindexing, the key is monotone. -/
private theorem sortKey_comp_reindex_monotone (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    Monotone (sortKey x y ∘ reindex x y) :=
  Tuple.monotone_sort (sortKey x y)

/-- Along the reindexing, `y` is nondecreasing. -/
private theorem reindex_y_monotone (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) {a b : Fin n}
    (hab : a ≤ b) : y (reindex x y a) ≤ y (reindex x y b) := by
  have h := sortKey_comp_reindex_monotone x y hab
  simp only [Function.comp_apply, sortKey, Prod.Lex.le_iff, ofLex_toLex] at h
  rcases h with h | h
  · exact le_of_lt h
  · exact le_of_eq h.1

/-- The reindexing is a linear extension: comparability of the reindexed points forces the
index order.  This is the general `sort_key_linear_extension` (from `Basic`) instantiated with
the targets `y` and the points `x`. -/
private theorem reindex_linear_extension (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) {a b : Fin n}
    (hx : x (reindex x y a) ≤ x (reindex x y b)) : a ≤ b :=
  sort_key_linear_extension y x hmono hinj hx

end Reindex

section Construction

variable {d n : ℕ}

/-- Layer 3 of the interpolation network (reverse prefix sum): `Layer n n`.  Neuron `i` sums the
domination indicators `E r` for `r ≥ i` (weights `if i ≤ r then 1 else 0`, all `≥ 0`) and
thresholds at `1` (bias `-1`), so under `heaviside` it fires iff some point `r ≥ i` is
dominated. -/
noncomputable def revPrefixLayer (n : ℕ) : NeuralNetwork.Layer n n where
  W := fun i r => if i ≤ r then 1 else 0
  c := fun _ => -1

/-- The reverse-prefix layer has non-negative weights. -/
private theorem revPrefixLayer_nonneg (n : ℕ) (i r : Fin n) : 0 ≤ (revPrefixLayer n).W i r := by
  unfold revPrefixLayer; dsimp only; split_ifs <;> norm_num

/-- The depth-`3` threshold stack: the two-layer domination gadget for the reindexed points
followed by the reverse-prefix-sum layer, all activations `heaviside`.  Sharing the gadget from
`Indicator.dominationStack` is what routes the domination step through the ε-indicator
infrastructure. -/
noncomputable def stack₃ (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ActStack d n :=
  .cons (dominationLayer1 (x ∘ reindex x y)) heaviside
    (.cons (dominationLayer2 d) heaviside
      (.cons (revPrefixLayer n) heaviside (.nil n)))

/-- The reindexed targets `y' i = y (π i)` along the reindexing permutation `π = reindex x y`. -/
noncomputable def reTarget (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  y (reindex x y i)

/-- The telescoping potential: `Y k = y' (k − 1)` at index `k − 1` when it is in range, and `0`
otherwise (`Nat` subtraction makes `Y 0 = y' 0`).  The read-out weight of neuron `i` is the
forward difference `Y (i+1) − Y i`, and the read-out bias is `Y 0`.  With this shift the prefix
sum over `i ≤ j` telescopes (via `Finset.sum_range_sub`) to `Y (j+1) − Y 0 = y' j − y' 0`, so
adding the bias recovers `y' j` exactly. -/
noncomputable def potential (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if hk : k - 1 < n then reTarget x y ⟨k - 1, hk⟩ else 0

/-- On the range that the read-out actually samples, the potential reads the reindexed target
`y' k` at shift `k + 1`. -/
private theorem potential_succ (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (k : Fin n) :
    potential x y (k + 1) = reTarget x y k := by
  unfold potential
  have hk' : (k : ℕ) + 1 - 1 < n := by simp only [Nat.add_sub_cancel]; exact k.2
  rw [dif_pos hk']
  congr 1

/-- The read-out weights: forward differences `Y (i+1) − Y i` of the potential.  These are
non-negative because the potential is nondecreasing (`y'` is nondecreasing along the
reindexing). -/
private noncomputable def readW (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => potential x y ((i : ℕ) + 1) - potential x y (i : ℕ)

/-- The read-out bias: the potential base `Y 0`, i.e. the smallest reindexed target `y' 0`
(or `0` if the dataset is empty). -/
private noncomputable def readBias (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℝ :=
  potential x y 0

/-- The interpolation network: the depth-`3` stack with the forward-difference read-out. -/
noncomputable def interpNet (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : MonoNet d :=
  ⟨n, stack₃ x y, readW x y, readBias x y⟩

/-- The read-out weights are non-negative: the forward difference `Y (i+1) − Y i` is the target
gap `y' i − y' (i−1)` (with `y' (i−1) = y' 0` at `i = 0`, giving `0`), which is `≥ 0` because `y'`
is nondecreasing along the reindexing. -/
private theorem readW_nonneg (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (i : Fin n) :
    0 ≤ readW x y i := by
  unfold readW
  rw [sub_nonneg, potential_succ]
  -- `Y i = y' (i−1)` (with `y' (i−1) = y' 0` at `i = 0`), which is `≤ y' i`
  unfold potential reTarget
  have hi' : (i : ℕ) - 1 < n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
  rw [dif_pos hi']
  apply reindex_y_monotone
  simp only [Fin.le_def]; omega

/-- The output of `stack₃` equals the reverse-prefix-sum layer applied to the domination
gadget output for the reindexed points.  This is what makes the shared `dominationStack` (and its
`dominationStack_apply` indicator identity) available to the level-set layer. -/
private theorem stack₃_toFun (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (z : Fin d → ℝ) :
    (stack₃ x y).toFun z =
      (revPrefixLayer n).toFun heaviside ((dominationStack (x ∘ reindex x y)).toFun z) := by
  rfl

open Classical in
/-- Lemma 5 (reverse prefix sum): at the reindexed input `x' j`, the depth-`3` stack outputs the
prefix indicator `𝟙(i ≤ j)`.  This routes the exact (`ε = 0`) domination indicators of the shared
gadget (`dominationStack_apply`, the concrete face of `dominationStack_isEpsIndicator … 0`) through
the level-set layer, using the linear-extension property of the reindexing: no point `r > j` is
dominated by `x' j`. -/
private theorem revPrefix_apply (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) (i j : Fin n) :
    (stack₃ x y).toFun (x (reindex x y j)) i = if i ≤ j then 1 else 0 := by
  rw [stack₃_toFun]
  -- the domination output at `x' j`
  have hE : ∀ r, (dominationStack (x ∘ reindex x y)).toFun (x (reindex x y j)) r
      = if x (reindex x y r) ≤ x (reindex x y j) then 1 else 0 := by
    intro r
    have h := dominationStack_apply (x ∘ reindex x y) (x (reindex x y j)) r
    simp only [Function.comp_apply] at h
    exact h
  -- unfold the reverse-prefix layer at neuron `i`
  change heaviside ((Matrix.mulVec (revPrefixLayer n).W
      ((dominationStack (x ∘ reindex x y)).toFun (x (reindex x y j)))) i
      + (revPrefixLayer n).c i) = _
  have hsum : (Matrix.mulVec (revPrefixLayer n).W
        ((dominationStack (x ∘ reindex x y)).toFun (x (reindex x y j)))) i
      = ∑ r, (if i ≤ r then (1 : ℝ) else 0)
          * (if x (reindex x y r) ≤ x (reindex x y j) then 1 else 0) := by
    rw [Matrix.mulVec]
    simp only [dotProduct, revPrefixLayer]
    exact Finset.sum_congr rfl (fun r _ => by rw [hE r])
  rw [hsum]
  simp only [revPrefixLayer]
  by_cases hij : i ≤ j
  · -- some `r = j ≥ i` is dominated, so the sum is `≥ 1`, output `1`
    have hterm : (if i ≤ j then (1 : ℝ) else 0)
        * (if x (reindex x y j) ≤ x (reindex x y j) then 1 else 0) = 1 := by
      rw [if_pos hij, if_pos le_rfl]; ring
    have hle : (if i ≤ j then (1 : ℝ) else 0)
        * (if x (reindex x y j) ≤ x (reindex x y j) then 1 else 0)
        ≤ ∑ r, (if i ≤ r then (1 : ℝ) else 0)
          * (if x (reindex x y r) ≤ x (reindex x y j) then 1 else 0) :=
      Finset.single_le_sum (f := fun r => (if i ≤ r then (1 : ℝ) else 0)
          * (if x (reindex x y r) ≤ x (reindex x y j) then 1 else 0))
        (fun r _ => by positivity) (Finset.mem_univ j)
    rw [hterm] at hle
    rw [if_pos hij, heaviside, if_pos (by linarith)]
  · -- every `r ≥ i > j` fails domination (linear extension), so the sum is `0`, output `0`
    have hzero : ∀ r, (if i ≤ r then (1 : ℝ) else 0)
        * (if x (reindex x y r) ≤ x (reindex x y j) then 1 else 0) = 0 := by
      intro r
      by_cases hir : i ≤ r
      · rw [if_pos hir, one_mul, if_neg]
        intro hdom
        have : r ≤ j := reindex_linear_extension x y hmono hinj hdom
        exact hij (le_trans hir this)
      · rw [if_neg hir, zero_mul]
    rw [Finset.sum_eq_zero (fun r _ => hzero r)]
    rw [if_neg hij, heaviside, if_neg (by norm_num)]

/-- The telescoping read-out identity on the *exact* prefix indicator: with the forward-difference
weights and base bias, `∑ i, readW i · 𝟙(i ≤ j) + readBias = y' j`.  This is the sound engine core
— it takes the *pre-read-out level-set vector* (the input to the non-negative read-out) as the
exact indicator `𝟙(i ≤ j)` and telescopes.  The gadget's ε is *not* threaded here: layer 3 is a
discontinuous `heaviside` level-set layer, so an ε-approximate domination indicator need not yield
the exact `𝟙(i ≤ j)`; the engine is therefore stated at this boundary (see `readout_error_bound`
for the linear error propagation from this boundary through the read-out). -/
private theorem readout_telescope (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (j : Fin n) :
    (∑ i, readW x y i * (if i ≤ j then (1 : ℝ) else 0)) + readBias x y = reTarget x y j := by
  -- rewrite the read-out weights via forward differences
  have hstep : (∑ i, readW x y i * (if i ≤ j then (1 : ℝ) else 0))
      = ∑ i : Fin n, (potential x y ((i : ℕ) + 1) - potential x y (i : ℕ))
          * (if (i : ℕ) ≤ (j : ℕ) then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold readW
    rfl
  rw [hstep]
  -- move to a sum over `Finset.range n`
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (potential x y (k + 1) - potential x y k) * (if k ≤ (j : ℕ) then (1 : ℝ) else 0))
      n]
  -- restrict to `range (j + 1)`: terms with `k > j` vanish
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range n :=
    Finset.range_subset_range.2 (Nat.succ_le_of_lt j.isLt)
  rw [← Finset.sum_subset hsub]
  · -- on `range (j + 1)` the indicator is `1`, then telescope forward differences
    have hind : ∀ k ∈ Finset.range ((j : ℕ) + 1),
        (potential x y (k + 1) - potential x y k) * (if k ≤ (j : ℕ) then (1 : ℝ) else 0)
        = potential x y (k + 1) - potential x y k := by
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [if_pos hk, mul_one]
    rw [Finset.sum_congr rfl hind, Finset.sum_range_sub (potential x y) ((j : ℕ) + 1)]
    -- the bias supplies `Y 0`, and `Y (j+1) = y' j`
    rw [potential_succ x y j]
    unfold readBias reTarget
    ring
  · intro k _ hk
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
    rw [if_neg (by omega), mul_zero]

/-- **General engine step (sound `η`-boundary).**  For *any* pre-read-out level-set vector
`v : Fin n → ℝ` that approximates the exact prefix indicator `𝟙(i ≤ j)` to accuracy `η`, the
telescoping non-negative read-out reproduces the reindexed target `y' j` to accuracy
`(∑ i, |readW i|) · η`.  This is the engine boundary at which error propagates *soundly*: it is the
input to the linear read-out.  It is deliberately *not* stated on the gadget's domination output —
layer 3 (`revPrefixLayer`) is a discontinuous `heaviside` level-set layer, so an ε-approximate
domination indicator can flip the level set and need not keep `v` within `O(ε)` of `𝟙(i ≤ j)`; the
error control across all layers is a Phase-2 co-design with the saturating construction.  The exact
interpolation is the `η = 0` instance (`v = 𝟙(i ≤ j)`, from `revPrefix_apply`). -/
theorem readout_error_bound (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (j : Fin n)
    {v : Fin n → ℝ} {η : ℝ} (hv : ∀ i, |v i - (if i ≤ j then (1 : ℝ) else 0)| ≤ η) :
    |((∑ i, readW x y i * v i) + readBias x y) - reTarget x y j|
      ≤ (∑ i, |readW x y i|) * η := by
  -- rewrite the target via the exact telescoping identity, then bound the linear read-out error
  rw [← readout_telescope x y j]
  have hdiff : ((∑ i, readW x y i * v i) + readBias x y)
      - ((∑ i, readW x y i * (if i ≤ j then (1 : ℝ) else 0)) + readBias x y)
      = ∑ i, readW x y i * (v i - (if i ≤ j then (1 : ℝ) else 0)) := by
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [mul_sub])
  rw [hdiff, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)

/-- The interpolation network reproduces the reindexed target at every reindexed point:
`N.toFun (x' j) = y' j`.  This is the exact (`η = 0`) instance of `readout_error_bound`: the shared
gadget makes the pre-read-out level-set vector the exact prefix indicator `𝟙(i ≤ j)`
(`revPrefix_apply`), so the read-out error is `≤ 0` and the identity holds on the nose. -/
private theorem interpNet_toFun_reindex (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) (j : Fin n) :
    (interpNet x y).toFun (x (reindex x y j)) = y (reindex x y j) := by
  -- the pre-read-out level-set vector is the exact prefix indicator
  have hv : ∀ i, |(stack₃ x y).toFun (x (reindex x y j)) i - (if i ≤ j then (1 : ℝ) else 0)| ≤ 0 :=
    fun i => by rw [revPrefix_apply x y hmono hinj i j, sub_self, abs_zero]
  -- feed it to the engine at `η = 0`
  have hbound := readout_error_bound x y j (v := (stack₃ x y).toFun (x (reindex x y j)))
    (η := 0) hv
  rw [mul_zero] at hbound
  have heq : (interpNet x y).toFun (x (reindex x y j)) = reTarget x y j := by
    have := abs_nonpos_iff.1 hbound
    unfold interpNet MonoNet.toFun
    simp only
    linarith [sub_eq_zero.1 this]
  rw [heq]; rfl

/-- The interpolation network has depth `4`. -/
theorem interpNet_depth (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    (interpNet x y).depth = 4 := rfl

/-- The interpolation network is monotone: hidden weights and read-out weights are non-negative
and every layer activation (`heaviside`) is monotone.  The two domination layers reuse
`dominationStack_isMonotone`; the reverse-prefix layer and the read-out are checked directly. -/
private theorem interpNet_isMonotone (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    (interpNet x y).IsMonotone := by
  refine ⟨?_, readW_nonneg x y⟩
  -- the first two layers ARE the domination gadget for `x'`, so reuse its monotonicity
  have hdom := dominationStack_isMonotone (x ∘ reindex x y)
  exact ⟨hdom.1, hdom.2.1, ⟨heaviside_monotone, revPrefixLayer_nonneg n⟩, trivial⟩

end Construction

section Main

variable {d n : ℕ}

/-- **Monotone interpolation (Theorem 1).**  Any finite dataset `(x i, y i)` whose targets are
monotone along the coordinatewise order of the points (`x i ≤ x j → y i ≤ y j`) and whose points
are distinct (`x` injective) can be interpolated *exactly* by a monotone threshold network of
depth `4`: there is a monotone `MonoNet d` of depth `4` whose denotation equals `y i` at every
`x i`.  This is Mikulincer–Reichman (arXiv:2207.05275) Result 1.

The proof now routes the domination step through the shared ε-indicator infrastructure: the
depth-`2` `dominationStack` gadget supplies the exact (`ε = 0`) domination indicators
(`dominationStack_apply`), and the exact interpolation is the `η = 0` instance of the sound
pre-read-out engine step `readout_error_bound`. -/
theorem monotone_interpolation (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) :
    ∃ N : MonoNet d, N.IsMonotone ∧ N.depth = 4 ∧ ∀ i, N.toFun (x i) = y i := by
  refine ⟨interpNet x y, interpNet_isMonotone x y, interpNet_depth x y, ?_⟩
  intro k
  -- transport the reindexed value identity back to the original index via `π⁻¹ k`
  have hval := interpNet_toFun_reindex x y hmono hinj ((reindex x y).symm k)
  rw [Equiv.apply_symm_apply] at hval
  exact hval

end Main

end UniversalApproximation.Monotone
