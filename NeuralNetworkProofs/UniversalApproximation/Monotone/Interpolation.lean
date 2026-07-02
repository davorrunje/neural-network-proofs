/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Domination

/-!
# Monotone interpolation (Theorem 1)

This file proves that any monotone, injective finite dataset can be interpolated exactly by a
depth-`4` monotone threshold network (Mikulincer–Reichman, arXiv:2207.05275, Result 1, paper
layers 3–4 plus the essential reindexing).

* `monotone_interpolation` — the headline: given points `x` and targets `y` with `y` monotone
  along the coordinatewise order and `x` injective, there is a monotone `MonoNet` of depth `4`
  agreeing with `y` on every `x i`.
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
index order. -/
private theorem reindex_linear_extension (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) {a b : Fin n}
    (hx : x (reindex x y a) ≤ x (reindex x y b)) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  -- from `b < a` and monotone sort we get `key (reindex b) ≤ key (reindex a)`
  have hkey : (sortKey x y ∘ reindex x y) b ≤ (sortKey x y ∘ reindex x y) a :=
    sortKey_comp_reindex_monotone x y hab.le
  -- but the assumed comparability gives the reverse
  have hy : y (reindex x y a) ≤ y (reindex x y b) := hmono _ _ hx
  have hxle : toLinearExtension (x (reindex x y a)) ≤ toLinearExtension (x (reindex x y b)) :=
    toLinearExtension.monotone hx
  have hkey' : (sortKey x y ∘ reindex x y) a ≤ (sortKey x y ∘ reindex x y) b := by
    simp only [Function.comp_apply, sortKey, Prod.Lex.le_iff, ofLex_toLex]
    rcases lt_or_eq_of_le hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hxle⟩
  have hEq : (sortKey x y ∘ reindex x y) a = (sortKey x y ∘ reindex x y) b :=
    le_antisymm hkey' hkey
  -- equal keys force equal points, contradicting injectivity of `x ∘ reindex`
  simp only [Function.comp_apply, sortKey] at hEq
  have hxeq : x (reindex x y a) = x (reindex x y b) := by
    have := (Prod.ext_iff.1 (toLex.injective hEq)).2
    exact this
  have : reindex x y a = reindex x y b := hinj hxeq
  exact absurd ((reindex x y).injective this) (ne_of_gt hab)

end Reindex

section Construction

variable {d n : ℕ}

/-- Layer 3 of the interpolation network (reverse prefix sum): `Layer n n`.  Neuron `i` sums the
domination indicators `E r` for `r ≥ i` (weights `if i ≤ r then 1 else 0`, all `≥ 0`) and
thresholds at `1` (bias `-1`), so under `θ` it fires iff some point `r ≥ i` is dominated. -/
noncomputable def revPrefixLayer (n : ℕ) : NeuralNetwork.Layer n n where
  W := fun i r => if i ≤ r then 1 else 0
  c := fun _ => -1

/-- The depth-`3` threshold stack: the two-layer domination gadget for the reindexed points
followed by the reverse-prefix-sum layer. -/
noncomputable def stack₃ (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ThreshStack d n :=
  .cons (dominationLayer1 (x ∘ reindex x y))
    (.cons (dominationLayer2 d) (.cons (revPrefixLayer n) (.nil n)))

/-- The read-out weights: successive differences of the reindexed targets, with `readW 0 = 0`
(the base value `y' 0` is carried in the bias instead).  These are non-negative because `y'` is
nondecreasing. -/
noncomputable def readW (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if _h : (i : ℕ) = 0 then 0
    else y (reindex x y i) -
      y (reindex x y ⟨i - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩)

/-- The read-out bias: the smallest reindexed target `y' 0` (or `0` if the dataset is empty). -/
noncomputable def readBias (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℝ :=
  if h : 0 < n then y (reindex x y ⟨0, h⟩) else 0

/-- The interpolation network: the depth-`3` stack with the successive-difference read-out. -/
noncomputable def interpNet (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : MonoNet d :=
  ⟨n, stack₃ x y, readW x y, readBias x y⟩

/-- The read-out weights are non-negative (from `y'` nondecreasing). -/
private theorem readW_nonneg (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (i : Fin n) :
    0 ≤ readW x y i := by
  unfold readW
  split_ifs with h
  · exact le_refl 0
  · rw [sub_nonneg]
    apply reindex_y_monotone x y
    have : (⟨i - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩ : Fin n) ≤ i := by
      simp only [Fin.le_def]
      exact Nat.sub_le _ _
    exact this

/-- The output of `stack₃` equals the reverse-prefix-sum layer applied to the domination
output for the reindexed points. -/
private theorem stack₃_toFun (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (z : Fin d → ℝ) :
    (stack₃ x y).toFun z =
      (revPrefixLayer n).toFun θ ((dominationStack (x ∘ reindex x y)).toFun z) := by
  rfl

open Classical in
/-- Lemma 5 (reverse prefix sum): at the reindexed input `x' j`, the depth-`3` stack outputs the
prefix indicator `𝟙(i ≤ j)`.  This uses the linear-extension property of the reindexing: no point
`r > j` is dominated by `x' j`. -/
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
  change θ ((Matrix.mulVec (revPrefixLayer n).W
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
    rw [if_pos hij, θ, if_pos (by linarith)]
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
    rw [if_neg hij, θ, if_neg (by norm_num)]

/-- The reindexed targets extended to `ℕ` (junk value `0` outside range): `Ycum k = y' k` for
`k < n`.  Used as the telescoping potential for the read-out. -/
private noncomputable def Ycum (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if h : k < n then y (reindex x y ⟨k, h⟩) else 0

/-- The read-out weight `readW i` is the successive difference `Ycum i − Ycum (i − 1)` (with the
`i = 0` term collapsing to `0` because `Nat` subtraction gives `0 - 1 = 0`). -/
private theorem readW_eq (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) (i : Fin n) :
    readW x y i = Ycum x y i - Ycum x y ((i : ℕ) - 1) := by
  have hi : Ycum x y (i : ℕ) = y (reindex x y i) := by
    unfold Ycum; rw [dif_pos i.2, Fin.eta]
  have hpred : ((i : ℕ) - 1) < n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
  have hip : Ycum x y ((i : ℕ) - 1) = y (reindex x y ⟨(i : ℕ) - 1, hpred⟩) := by
    unfold Ycum; rw [dif_pos hpred]
  rw [hi, hip]
  unfold readW
  split_ifs with h
  · have h0 : ((i : ℕ) - 1) = 0 := by omega
    have hcong : (⟨(i : ℕ) - 1, hpred⟩ : Fin n) = i := by
      apply Fin.ext; simp [h]
    rw [hcong]; ring
  · rfl

/-- A telescoping identity: the prefix sum of successive differences of `Y` equals `Y m − Y 0`. -/
private theorem telescope_pred (Y : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (Y k - Y (k - 1)) = Y m - Y 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have : (m + 1 - 1) = m := by omega
    rw [this]; ring

/-- The interpolation network reproduces the reindexed target at every reindexed point:
`N.toFun (x' j) = y' j`.  Combines Lemma 5, the successive-difference read-out, and telescoping. -/
private theorem interpNet_toFun_reindex (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ)
    (hmono : ∀ i j, x i ≤ x j → y i ≤ y j) (hinj : Function.Injective x) (j : Fin n) :
    (interpNet x y).toFun (x (reindex x y j)) = y (reindex x y j) := by
  unfold interpNet MonoNet.toFun
  simp only
  -- rewrite the stack output via Lemma 5 and the read-out weights via successive differences
  have hstep : (∑ i, readW x y i * (stack₃ x y).toFun (x (reindex x y j)) i)
      = ∑ i : Fin n, (Ycum x y i - Ycum x y ((i : ℕ) - 1))
          * (if (i : ℕ) ≤ (j : ℕ) then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [revPrefix_apply x y hmono hinj i j, readW_eq]
    rfl
  rw [hstep]
  -- move to a sum over `Finset.range n`
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (Ycum x y k - Ycum x y (k - 1)) * (if k ≤ (j : ℕ) then (1 : ℝ) else 0)) n]
  -- restrict to `range (j + 1)`: terms with `k > j` vanish
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range n :=
    Finset.range_subset_range.2 (Nat.succ_le_of_lt j.isLt)
  rw [← Finset.sum_subset hsub]
  · -- on `range (j + 1)` the indicator is `1`, then telescope
    have : ∀ k ∈ Finset.range ((j : ℕ) + 1),
        (Ycum x y k - Ycum x y (k - 1)) * (if k ≤ (j : ℕ) then (1 : ℝ) else 0)
        = Ycum x y k - Ycum x y (k - 1) := by
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [if_pos hk, mul_one]
    rw [Finset.sum_congr rfl this, telescope_pred]
    -- the bias supplies `Ycum 0 = y' 0`
    have hbias : readBias x y = Ycum x y 0 := by
      have hpos : 0 < n := j.pos
      unfold readBias Ycum
      simp only [dif_pos hpos]
    rw [hbias]
    have hj : Ycum x y (j : ℕ) = y (reindex x y j) := by
      unfold Ycum
      rw [dif_pos j.2, Fin.eta]
    rw [hj]; ring
  · intro k _ hk
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
    rw [if_neg (by omega), mul_zero]

/-- The interpolation network has depth `4`. -/
theorem interpNet_depth (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    (interpNet x y).depth = 4 := rfl

/-- The interpolation network is monotone: hidden weights and read-out weights are non-negative. -/
private theorem interpNet_isMonotone (x : Fin n → (Fin d → ℝ)) (y : Fin n → ℝ) :
    (interpNet x y).IsMonotone := by
  refine ⟨?_, readW_nonneg x y⟩
  -- the stack is the domination gadget for `x'` followed by the reverse-prefix layer
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro q k
    unfold dominationLayer1; dsimp only; split_ifs <;> norm_num
  · intro i q
    unfold dominationLayer2; dsimp only; split_ifs <;> norm_num
  · intro i r
    unfold revPrefixLayer; dsimp only; split_ifs <;> norm_num

end Construction

section Main

variable {d n : ℕ}

/-- **Monotone interpolation (Theorem 1).**  Any finite dataset `(x i, y i)` whose targets are
monotone along the coordinatewise order of the points (`x i ≤ x j → y i ≤ y j`) and whose points
are distinct (`x` injective) can be interpolated *exactly* by a monotone threshold network of
depth `4`: there is a monotone `MonoNet d` of depth `4` whose denotation equals `y i` at every
`x i`.  This is Mikulincer–Reichman (arXiv:2207.05275) Result 1. -/
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
