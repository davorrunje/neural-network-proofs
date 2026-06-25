import Mathlib

#check 2 + 2 = 4
#eval 2 + 2 = 4

def f (x : ℕ) : ℕ :=
  x + 3

theorem easy_example : f 2 = 5 := by
  rfl
