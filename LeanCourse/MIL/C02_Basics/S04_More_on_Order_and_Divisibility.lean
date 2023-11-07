import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply ge_antisymm
  apply max_le
  exact le_max_right a b
  exact le_max_left a b
  apply max_le
  exact le_max_right b a
  exact le_max_left b a

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · exact le_trans (min_le_left (min a b) c) (min_le_left a b)
    · apply le_min
      · exact le_trans (min_le_left (min a b) c) (min_le_right a b)
      · exact min_le_right (min a b) c
  · apply le_min
    · apply le_min
      · exact min_le_left a (min b c)
      · exact le_trans (min_le_right a (min b c)) (min_le_left b c)
    · exact le_trans (min_le_right a (min b c)) (min_le_right b c)


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · gcongr
    exact min_le_left a b
  · gcongr
    exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · have : min (a + c) (b + c) - c ≤ min a b := by
      apply le_min
      calc min (a + c) (b + c) - c
        _ ≤ a + c - c := sub_le_sub_right (min_le_left (a + c) (b + c)) c
        _ = a := by ring
      calc min (a + c) (b + c) - c
        _ ≤ b + c - c := sub_le_sub_right (min_le_right (a + c) (b + c)) c
        _ = b := by ring
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have : |a| ≤ |b| + |a - b| := by
    calc |a|
      _ = |b + (a - b)| := by ring
      _ ≤ |b| + |a - b| := abs_add b (a - b)
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    · rw [pow_two]
      apply dvd_mul_left
  · rw [pow_two]
    apply dvd_mul_of_dvd_right
    exact h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := Nat.gcd_comm m n
