import Mathlib

/-- A tiny worked example: the sum of two even naturals is even. -/
theorem LeanPlayground.add_even {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  hm.add hn

#eval "Lean + Mathlib are working!"
