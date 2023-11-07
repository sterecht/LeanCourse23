import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by
  induction' n with n h
  · simp
  rw [sum_range_succ, h, sum_range_succ _ (n + 1)]
  have : ∑ x in range (n + 1), (x : ℚ) = n * (n + 1) / 2 := by
    clear h
    induction' n with n h
    · simp
    rw [sum_range_succ, h]
    field_simp
    ring
  rw [this]
  field_simp
  ring

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  constructor
  · intro i j hij s hsi hsj x hx
    simp
    specialize hsi hx
    specialize hsj hx
    wlog hi : i < j generalizing i j
    · exact this hij.symm hsj hsi (Ne.lt_of_le hij.symm (not_lt.1 hi))
    have hxi : x ∈ A i := by rw [hC i] at hsi; exact hsi.1
    have : x ∉ A i := by
      rw [hC j] at hsj
      simp at hsj
      exact hsj.2 i hi
    exact this hxi
  · ext x
    constructor
    · intro hc
      simp at hc
      obtain ⟨i, hi⟩ := hc
      simp
      use i
      rw [hC i] at hi
      exact hi.1
    · intro ha
      simp
      simp at ha
      obtain ⟨i, hi⟩ := ha
      set S := {i : ι | x ∈ A i}
      obtain ⟨j, hj⟩ := h S ⟨i, hi⟩
      use j
      rw [hC j]
      constructor; exact hj.1
      simp
      exact fun k hk hA ↦ hj.2 k hA hk

/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by exact Real.mul_pos ha hb

lemma exercise4_3 : Group PosReal where
  mul := fun x y ↦ ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  mul_assoc := by
    intro x y z
    have : x.1 * y.1 * z.1 = x.1 * (y.1 * z.1) := mul_assoc x.1 y.1 z.1
    apply PosReal.ext
    norm_cast
  one := ⟨1, by norm_num⟩
  one_mul := by
    intro x
    apply PosReal.ext
    have : 1 * x.1 = x.1 := one_mul x.1
    norm_cast
  mul_one := by
    intro x
    apply PosReal.ext
    have : x.1 * 1 = x.1 := mul_one x.1
    norm_cast
  inv := fun x ↦ ⟨x.1⁻¹, inv_pos.2 x.2⟩
  mul_left_inv := by
    intro x
    apply PosReal.ext
    have : x.1⁻¹ * x.1 = 1 := inv_mul_cancel (ne_of_gt x.2)
    norm_cast

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
  constructor
  · intro h
    cases n; left; rfl
    case succ n hn =>
      cases n; right; left; simp
      case succ n hn' =>
        right; right
        rw [prime_def_lt] at h
        push_neg at h
        simp at h
        ring at h
        obtain ⟨m, hm⟩ := h (by norm_num)
        use m, (n + 2) / m
        constructor
        by_contra H
        simp at H
        interval_cases m
        linarith [zero_dvd_iff.1 hm.2.1]
        exact hm.2.2 rfl
        constructor
        by_contra H
        simp at H
        interval_cases h : (n + 2) / m
        have : m > 0 := by
          by_contra h
          simp at h
          subst h
          linarith [zero_dvd_iff.1 hm.2.1]
        have : n + 2 < m := (Nat.div_eq_zero_iff this).1 h
        linarith [this, hm.1]
        ring at h
        have : m = 2 + n := eq_of_dvd_of_div_eq_one hm.2.1 h
        linarith [this, hm.1]
        ring
        exact Nat.eq_mul_of_div_eq_right hm.2.1 rfl
  · rintro (rfl | rfl | ⟨a, b, H⟩)
    simp; simp
    intro h
    have : a = 1 := (Nat.prime_def_lt.1 h).2 a ?_ (Dvd.intro b (id H.2.2.symm))
    linarith [this, H.1]
    calc a
      _ = a * 1 := (mul_one a).symm
      _ < a * 2 := Nat.mul_lt_mul_of_pos_left (by norm_num) (by linarith [H.1])
      _ ≤ a * b := Nat.mul_le_mul_left a H.2.1
      _ = n := H.2.2.symm


lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · simp at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by ring; rfl
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := Int.ModEq.sub_right 1 (Int.ModEq.pow b (Int.modEq_sub ((2 : ℤ) ^ a) 1))
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by ring; rfl
  have h2 : 2 ^ 2 ≤ 2 ^ a := (Nat.pow_le_iff_le_right (by norm_num)).2 ha
  have h3 : 1 ≤ 2 ^ a := le_trans (by norm_num) h2
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    apply (Nat.pow_lt_iff_lt_right (by norm_num)).2
    calc a
      _ = a * 1 := (mul_one a).symm
      _ < a * 2 := mul_lt_mul_of_pos_left (by norm_num) (by linarith [ha])
      _ ≤ a * b := Nat.mul_le_mul (by linarith) hb
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    apply (Nat.pow_le_iff_le_right (by norm_num)).2
    exact Nat.zero_le (a * b)
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  exact h4 (hn.2 (2 ^ a - 1) h5 h')

/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
  by_contra h
  push_neg at h
  wlog hab : a ≤ b
  · exact this b a hb ha ⟨h.2, h.1⟩ (le_of_lt (not_le.1 hab))
  have h1 : b ^ 2 < b ^ 2 + a := Nat.lt_add_of_pos_right ha
  have h2 : b ^ 2 + a < (b + 1) ^ 2 := by
    calc b ^ 2 + a
      _ ≤ b ^ 2 + b := add_le_add_left hab (b ^ 2)
      _ < b ^ 2 + b + (b + 1) := Nat.lt_add_of_pos_right (by linarith)
      _ = (b + 1) ^ 2 := by ring
  obtain ⟨c, hc⟩ := h.2
  rw [← sq c] at hc
  rw [hc] at h1
  rw [hc] at h2
  linarith [lt_of_pow_lt_pow' 2 h1, lt_of_pow_lt_pow' 2 h2]
