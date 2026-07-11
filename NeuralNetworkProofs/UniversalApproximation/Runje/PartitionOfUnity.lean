/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Normalized tent partition of unity on the unit cube (Runje et al.)

A tensor-product "tent" partition of unity on the unit cube `[0,1]^df`, used by the
partial-monotone construction — a secondary result of the Deep Constrained Monotonic Neural
Networks development of Runje et al.

The design is the **normalization trick**: build unnormalized tensor-product tents
`tent m k u = ∏ c, hat1 m (k c) (u c)` from 1-D hats centred at the grid nodes `k/m`, then
normalize `psi m k u = tent m k u / tentDenom m u` where `tentDenom = ∑ k, tent`.  With this
definition `∑ k, psi = 1` is essentially free (`Finset.sum_div` + `div_self`), so the only
analytic content is that the denominator is strictly positive on the cube (`tentDenom_pos`),
which follows from exhibiting a single positive tent at the rounded multi-index.

Main definitions:
* `hat1` — the 1-D hat centred at `k/m` of width `1/m`;
* `tentNode`, `tent`, `tentDenom`, `psi` — the tensor-product tents and their normalization.

Main results:
* `sum_psi_eq_one` — the `psi m · u` sum to `1` on the cube;
* `psi_nonneg`, `psi_le_one` — the `psi` take values in `[0,1]`;
* `psi_support` — `psi m k` vanishes outside the sup-ball of radius `1/m` about the node;
* `psi_continuousOn` — each `psi m k` is continuous on the cube.
-/

namespace UniversalApproximation.Runje

variable {df : ℕ}

/-! ### The 1-D hat -/

/-- 1-D hat centred at node `k/m`, width `1/m`. -/
noncomputable def hat1 (m k : ℕ) (t : ℝ) : ℝ := max 0 (1 - m * |t - k / m|)

lemma hat1_nonneg (m k : ℕ) (t : ℝ) : 0 ≤ hat1 m k t := le_max_left _ _

/-- Off its support the hat is zero. (Uses `1 ≤ m`; for `m = 0` the hat is constantly `1`.) -/
lemma hat1_eq_zero_of_far {m k : ℕ} (hm : 1 ≤ m) {t : ℝ}
    (h : 1 / m ≤ |t - k / m|) : hat1 m k t = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ m * |t - k / m| := by
    have hid : (m : ℝ) * (1 / m) = 1 := by rw [mul_one_div, div_self hmpos.ne']
    calc (1 : ℝ) = m * (1 / m) := hid.symm
      _ ≤ m * |t - k / m| := mul_le_mul_of_nonneg_left h hmpos.le
  unfold hat1
  exact max_eq_left (by linarith)

/-- On its support the argument is close to the node. (Uses `1 ≤ m`.) -/
lemma hat1_support {m k : ℕ} (hm : 1 ≤ m) {t : ℝ} (h : hat1 m k t ≠ 0) :
    |t - k / m| < 1 / m := by
  by_contra hcon
  exact h (hat1_eq_zero_of_far hm (not_lt.mp hcon))

lemma hat1_continuous (m k : ℕ) : Continuous (hat1 m k) := by
  unfold hat1
  fun_prop

/-- The rounded node makes the hat strictly positive (used for denominator positivity). -/
lemma hat1_pos_at_round {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k : Fin (m + 1), 0 < hat1 m k t := by
  obtain ⟨ht0, ht1⟩ := ht
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmt0 : (0 : ℝ) ≤ (m : ℝ) * t := mul_nonneg hmpos.le ht0
  set n : ℕ := ⌊(m : ℝ) * t⌋₊ with hn
  have hn_le : (n : ℝ) ≤ (m : ℝ) * t := Nat.floor_le hmt0
  have hn_lt : (m : ℝ) * t < n + 1 := Nat.lt_floor_add_one _
  have hnm : n ≤ m := by
    have : (n : ℝ) ≤ m := le_trans hn_le (by nlinarith)
    exact_mod_cast this
  refine ⟨⟨n, by omega⟩, ?_⟩
  have hdist_nonneg : (0 : ℝ) ≤ t - (n : ℝ) / m := by
    have : (n : ℝ) / m ≤ t := by
      rw [div_le_iff₀ hmpos]; nlinarith [hn_le]
    linarith
  have hval : (m : ℝ) * |t - (n : ℝ) / m| = (m : ℝ) * t - n := by
    rw [abs_of_nonneg hdist_nonneg, mul_sub, mul_div_cancel₀ _ hmpos.ne']
  have hpos : (0 : ℝ) < 1 - (m : ℝ) * |t - (n : ℝ) / m| := by rw [hval]; linarith
  refine lt_of_lt_of_le hpos ?_
  simp only [hat1]
  exact le_max_right _ _

/-! ### The tensor-product tents and their normalization -/

/-- The grid node indexed by the multi-index `k`, i.e. the point `(k c / m)_c`. -/
noncomputable def tentNode (m : ℕ) (k : Fin df → Fin (m + 1)) : Fin df → ℝ :=
  fun c => (k c : ℝ) / m

/-- The unnormalized tensor-product tent at multi-index `k`. -/
noncomputable def tent (m : ℕ) (k : Fin df → Fin (m + 1)) (u : Fin df → ℝ) : ℝ :=
  ∏ c, hat1 m (k c) (u c)

/-- The tent normalizer: the sum of all tents at a point. -/
noncomputable def tentDenom (m : ℕ) (u : Fin df → ℝ) : ℝ := ∑ k, tent m k u

/-- The normalized tent (partition-of-unity bump) at multi-index `k`. -/
noncomputable def psi (m : ℕ) (k : Fin df → Fin (m + 1)) (u : Fin df → ℝ) : ℝ :=
  tent m k u / tentDenom m u

lemma tent_nonneg (m : ℕ) (k : Fin df → Fin (m + 1)) (u : Fin df → ℝ) : 0 ≤ tent m k u :=
  Finset.prod_nonneg (fun _ _ => hat1_nonneg _ _ _)

lemma psi_nonneg (m : ℕ) (k : Fin df → Fin (m + 1)) (u : Fin df → ℝ) : 0 ≤ psi m k u :=
  div_nonneg (tent_nonneg _ _ _) (Finset.sum_nonneg fun _ _ => tent_nonneg _ _ _)

lemma tent_continuous (m : ℕ) (k : Fin df → Fin (m + 1)) : Continuous (tent m k) := by
  unfold tent
  exact continuous_finsetProd _
    (fun c _ => (hat1_continuous m (k c)).comp (continuous_apply c))

lemma tentDenom_continuous (m : ℕ) : Continuous (tentDenom (df := df) m) := by
  unfold tentDenom
  exact continuous_finsetSum _ (fun k _ => tent_continuous m k)

lemma tentDenom_pos {m : ℕ} (hm : 1 ≤ m) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : 0 < tentDenom m u := by
  have hmem : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1 := fun c => ⟨hu.1 c, hu.2 c⟩
  choose k hk using fun c => hat1_pos_at_round hm (hmem c)
  have htent_pos : 0 < tent m k u := Finset.prod_pos (fun c _ => hk c)
  unfold tentDenom
  exact Finset.sum_pos' (fun k' _ => tent_nonneg m k' u) ⟨k, Finset.mem_univ k, htent_pos⟩

lemma sum_psi_eq_one {m : ℕ} (hm : 1 ≤ m) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : (∑ k, psi m k u) = 1 := by
  have hpos := tentDenom_pos hm hu
  unfold psi
  rw [← Finset.sum_div]
  have hnum : (∑ k, tent m k u) = tentDenom m u := rfl
  rw [hnum, div_self hpos.ne']

lemma psi_le_one {m : ℕ} (hm : 1 ≤ m) (k : Fin df → Fin (m + 1)) {u : Fin df → ℝ}
    (hu : u ∈ Set.Icc (0 : Fin df → ℝ) 1) : psi m k u ≤ 1 :=
  calc psi m k u ≤ ∑ k', psi m k' u :=
        Finset.single_le_sum (fun k' _ => psi_nonneg m k' u) (Finset.mem_univ k)
    _ = 1 := sum_psi_eq_one hm hu

lemma tentNode_mem_Icc (m : ℕ) (k : Fin df → Fin (m + 1)) :
    tentNode m k ∈ Set.Icc (0 : Fin df → ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨fun c => ?_, fun c => ?_⟩
  · simp only [Pi.zero_apply, tentNode]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [Pi.one_apply, tentNode]
    exact div_le_one_of_le₀ (by exact_mod_cast (k c).is_le) (Nat.cast_nonneg _)

lemma psi_support {m : ℕ} (hm : 1 ≤ m) (k : Fin df → Fin (m + 1)) {u : Fin df → ℝ}
    (h : psi m k u ≠ 0) : dist (tentNode m k) u ≤ 1 / m := by
  have htent : tent m k u ≠ 0 := by
    intro h0
    exact h (by unfold psi; rw [h0, zero_div])
  have hfac : ∀ c, hat1 m (k c) (u c) ≠ 0 := by
    have htent' : (∏ c, hat1 m (k c) (u c)) ≠ 0 := htent
    rw [Finset.prod_ne_zero_iff] at htent'
    exact fun c => htent' c (Finset.mem_univ c)
  have hr : (0 : ℝ) ≤ 1 / m := by positivity
  rw [dist_pi_le_iff hr]
  intro c
  rw [Real.dist_eq]
  have hlt : |u c - tentNode m k c| < 1 / m := by
    have := hat1_support hm (hfac c)
    simpa [tentNode] using this
  rw [abs_sub_comm]
  exact hlt.le

lemma psi_continuousOn {m : ℕ} (hm : 1 ≤ m) (k : Fin df → Fin (m + 1)) :
    ContinuousOn (psi m k) (Set.Icc (0 : Fin df → ℝ) 1) := by
  unfold psi
  exact ContinuousOn.div₀ (tent_continuous m k).continuousOn
    (tentDenom_continuous m).continuousOn (fun u hu => (tentDenom_pos hm hu).ne')

end UniversalApproximation.Runje
