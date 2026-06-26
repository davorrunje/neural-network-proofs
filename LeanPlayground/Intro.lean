import Mathlib

#check 2 + 2 = 4
#eval 2 + 2 = 4

def f (x : ℕ) : ℕ :=
  x + 3

#check f

def add_2_and_3 := f 2

#check add_2_and_3

theorem easy_example : add_2_and_3 = 5 := by
  rfl

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intro m n h
  exact h.mul_left m

-- We define a basic property: a number is a multiple of 3
def IsMultipleOfThree (n : Nat) : Prop :=
  ∃ k : Nat, n = 3 * k

-- A simple test case for Claude
theorem nine_is_multiple_of_three : IsMultipleOfThree 9 := by
  use 3

-- A slightly more interesting logic puzzle for Claude
theorem multiple_of_three_add (a b : Nat)
    (ha : IsMultipleOfThree a) (hb : IsMultipleOfThree b) :
    IsMultipleOfThree (a + b) := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  use ka + kb
  rw [hka, hkb]
  ring
