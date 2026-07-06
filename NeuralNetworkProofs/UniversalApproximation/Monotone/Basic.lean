/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Extension.Linear
import Mathlib.Tactic

/-!
# General lemmas for the monotone-network development

Three model-independent lemmas extracted from the monotone neural-network development so that the
domination, approximation, and interpolation files can share a single proof instead of carrying
inline copies.

* `sum_le_one_card_le_iff` — for a `Fintype ι` and `g : ι → ℝ` with each `g i ≤ 1`, the sum reaches
  the cardinality iff every summand equals `1`.  (Generalizes the threshold-sum bound in the
  domination gadget.)
* `dist_le_of_coord` — a per-coordinate bound on `Fin d → ℝ` transfers to a sup-metric `dist`
  bound.  (Used to turn grid gaps into distance bounds in the approximation proof.)
* `sort_key_linear_extension` — sorting indices by the lexicographic key
  `fun i => (a i, toLinearExtension (b i))` yields a permutation that linearly extends the
  coordinatewise order on the sorted points.  (Generalizes the reindexing lemma of the
  interpolation proof.)
-/

namespace UniversalApproximation.Monotone

open scoped BigOperators

/-- If every summand `g i` of a finite family of reals is at most `1`, then the sum is at least the
cardinality of the index type exactly when every summand equals `1`.  Forward: any summand strictly
below `1` makes the sum strictly below the cardinality; backward: all summands equal to `1` sum to
the cardinality. -/
theorem sum_le_one_card_le_iff {ι : Type*} [Fintype ι] {g : ι → ℝ} (hg : ∀ i, g i ≤ 1) :
    (Fintype.card ι : ℝ) ≤ ∑ i, g i ↔ ∀ i, g i = 1 := by
  constructor
  · intro hsum i
    by_contra hne
    have hlt : g i < 1 := lt_of_le_of_ne (hg i) hne
    have hbound : ∑ j, g j < (Fintype.card ι : ℝ) := by
      calc ∑ j, g j
          < ∑ _j : ι, (1 : ℝ) := by
            apply Finset.sum_lt_sum
            · intro j _; exact hg j
            · exact ⟨i, Finset.mem_univ i, hlt⟩
        _ = (Fintype.card ι : ℝ) := by simp [Finset.card_univ]
    linarith
  · intro hone
    have heq : (Fintype.card ι : ℝ) = ∑ i, g i := by
      rw [Finset.sum_congr rfl (fun i _ => hone i)]
      simp [Finset.card_univ]
    exact heq.le

/-- If two points of `Fin d → ℝ` agree per coordinate to within `c ≥ 0`, then their sup-metric
distance is at most `c`.  The distance on `Fin d → ℝ` is the sup metric, so this is `dist_pi_le_iff`
combined with `Real.dist_eq`. -/
theorem dist_le_of_coord {d : ℕ} {x y : Fin d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |x i - y i| ≤ c) : dist x y ≤ c := by
  rw [dist_pi_le_iff hc]
  intro i
  rw [Real.dist_eq]
  exact h i

/-- Sorting the indices by the lexicographic key `fun i => (a i, toLinearExtension (b i))` produces
a permutation that linearly extends the partial order on the sorted points.

Given a family of points `b : ι → β` in a partial order and real targets `a : ι → ℝ` that are
monotone along `b` (`b i ≤ b j → a i ≤ a j`) with `b` injective, `Tuple.sort` of the key yields a
permutation `π` such that comparability of the sorted points, `b (π s) ≤ b (π t)`, forces the index
order `s ≤ t`.  The `LinearExtension` second component makes the key injective, so equal keys force
equal points and hence equal indices; monotonicity of the sort then pins down the order. -/
theorem sort_key_linear_extension {n : ℕ} {β : Type*} [PartialOrder β]
    (a : Fin n → ℝ) (b : Fin n → β)
    (hmono : ∀ i j, b i ≤ b j → a i ≤ a j) (hinj : Function.Injective b) {s t : Fin n}
    (hb : b (Tuple.sort (fun i => toLex (a i, toLinearExtension (b i))) s) ≤
      b (Tuple.sort (fun i => toLex (a i, toLinearExtension (b i))) t)) :
    s ≤ t := by
  set key : Fin n → (ℝ ×ₗ LinearExtension β) :=
    fun i => toLex (a i, toLinearExtension (b i)) with hkey
  set π : Equiv.Perm (Fin n) := Tuple.sort key
  have hsort : Monotone (key ∘ π) := Tuple.monotone_sort key
  by_contra hst
  rw [not_le] at hst
  -- from `t < s` and the monotone sort we get `key (π t) ≤ key (π s)`
  have hkey_ts : (key ∘ π) t ≤ (key ∘ π) s := hsort hst.le
  -- from comparability of the points we get `key (π s) ≤ key (π t)`
  have ha : a (π s) ≤ a (π t) := hmono _ _ hb
  have hble : toLinearExtension (b (π s)) ≤ toLinearExtension (b (π t)) :=
    toLinearExtension.monotone hb
  have hkey_st : (key ∘ π) s ≤ (key ∘ π) t := by
    simp only [Function.comp_apply, hkey, Prod.Lex.le_iff, ofLex_toLex]
    rcases lt_or_eq_of_le ha with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hble⟩
  -- equal keys force equal points, contradicting injectivity of `b ∘ π`
  have hEq : (key ∘ π) s = (key ∘ π) t := le_antisymm hkey_st hkey_ts
  simp only [Function.comp_apply, hkey] at hEq
  have hbeq : b (π s) = b (π t) := (Prod.ext_iff.1 (toLex.injective hEq)).2
  have : π s = π t := hinj hbeq
  exact absurd (π.injective this) (ne_of_gt hst)

end UniversalApproximation.Monotone
