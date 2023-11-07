import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h]
  rw [abs_of_neg h]
  linarith [h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  calc -x
    _ ≤ |-x| := le_abs_self (-x)
    _ = |x| := (abs_eq_abs.2) (Or.inr rfl)


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  rw [abs_of_nonneg h]
  linarith [le_abs_self x, le_abs_self y]
  rw [abs_of_neg h]
  have h : -(x + y) = -x + -y := by ring
  have : -x + -y ≤ |x| + |y| := by linarith [neg_le_abs_self x, neg_le_abs_self y]
  rw [h]
  exact this

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro h0
  rcases le_or_gt 0 y with h | h
  left
  rw [abs_of_nonneg h] at h0
  exact h0
  right
  rw [abs_of_neg h] at h0
  exact h0
  intro h0
  rcases h0 with h | h
  exact lt_of_lt_of_le h (le_abs_self y)
  exact lt_of_lt_of_le h (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  intro h0
  constructor
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h] at h0
  have : -y < 0 := by
    simp
    exact lt_of_le_of_lt h h0
  calc -y
    _ < 0 := this
    _ ≤ x := h
  rw [abs_of_neg h] at h0
  linarith
  exact lt_of_le_of_lt (le_abs_self x) h0
  intro h0
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h]
  exact h0.2
  rw [abs_of_neg h]
  linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h1 | h2⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : 0 = (x - 1) * (x + 1) := by
    calc (0 : ℝ)
      _ = 1 - 1 := by ring
      _ = x ^ 2 - 1 := by rw [h]
      _ = (x - 1) * (x + 1) := by ring
  have : x - 1 = 0 ∨ x + 1 = 0 := by
    exact eq_zero_or_eq_zero_of_mul_eq_zero (symm this)
  rcases this with h0 | h0
  left
  linarith
  right
  linarith



example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : 0 = (x - y) * (x + y) := by
    calc (0 : ℝ)
      _ = x ^ 2 - x ^ 2 := by ring
      _ = x ^ 2 - y ^ 2 := by rw [h]
      _ = (x - y) * (x + y) := by ring
  have : x - y = 0 ∨ x + y = 0 :=
    eq_zero_or_eq_zero_of_mul_eq_zero (symm this)
  rcases this with h | h
  left
  linarith
  right
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : 0 = (x - 1) * (x + 1) := by
    calc 0
      _ = x ^ 2 - x ^ 2 := by ring
      _ = x ^ 2 - 1 := by rw [h]
      _ = (x - 1) * (x + 1) := by ring
  have : x - 1 = 0 ∨ x + 1 = 0 := by
    exact eq_zero_or_eq_zero_of_mul_eq_zero (symm this)
  rcases this with h0 | h0
  left
  calc x
    _ = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h0]
    _ = 1 := by ring
  right
  calc x
    _ = x + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h0]
    _ = -1 := by ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : 0 = (x - y) * (x + y) := by
    calc 0
      _ = x ^ 2 - x ^ 2 := by ring
      _ = x ^ 2 - y ^ 2 := by rw [h]
      _ = (x - y) * (x + y) := by ring
  have : x - y = 0 ∨ x + y = 0 :=
    eq_zero_or_eq_zero_of_mul_eq_zero (symm this)
  rcases this with h | h
  left
  calc x
    _ = x - y + y := by ring
    _ = 0 + y := by rw [h]
    _ = y := by ring
  right
  calc x
    _ = x + y - y := by ring
    _ = 0 - y := by rw [h]
    _ = -y := by ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h0
  by_cases h : P
  right
  exact h0 h
  left
  exact h
  intro h0 h1
  rcases h0 with h | h
  contradiction
  exact h
