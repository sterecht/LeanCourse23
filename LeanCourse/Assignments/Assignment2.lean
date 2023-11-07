import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  rintro ⟨x, hx⟩
  obtain hp | hq := hx
  left
  use x
  right
  use x
  intro h
  obtain ⟨x, hp⟩ | ⟨x, hq⟩ := h <;> use x
  left
  assumption
  right
  assumption


section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨f y, hy⟩

/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  exact exercise2_2
  intro h x
  obtain ⟨y, hy⟩ := h x
  obtain ⟨z, hz⟩ := hf y
  use z
  rw [← hy, ← hz]
  rfl

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  have h1 : SurjectiveFunction (fun x ↦ 3 * (x + 4)) := by
    intro x
    use x/3-4
    simp
    ring
  have h2 : SurjectiveFunction (fun x ↦ 2 * x + 1) := by
    intro x
    use (x-1)/2
    simp
    ring
  apply (exercise2_3 ((exercise2_3 h1).2 hf)).2 h2

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  simp
  exact mul_le_mul_right (s n) hn

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  obtain ⟨N₁, H₁⟩ := h₁ k
  obtain ⟨N₂, H₂⟩ := h₂ k
  use max N₁ N₂
  intro n hn
  simp
  specialize H₁ n ((useful_fact N₁ N₂ n).1 hn).1
  specialize H₂ n ((useful_fact N₁ N₂ n).1 hn).2
  calc k * (t₁ n + t₂ n)
    _ = k * t₁ n + k * t₂ n := by ring
    _ ≤ s₁ n + s₂ n := Nat.add_le_add H₁ H₂


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use (fun n ↦ n ^ n)
  constructor
  · intro k
    use k
    intro n hn
    simp
    calc k * n ^ n
      _ ≤ n * n ^ n := mul_le_mul_right (n ^ n) hn
      _ = n ^ (n + 1) := by ring
      _ ≤ (n + 1) ^ (n + 1) := (Nat.pow_le_iff_le_left (by simp)).2 (by linarith)
  · intro n h
    rcases Nat.eq_zero_or_pos n with h₀ | h₁
    rw [h₀] at h
    contradiction
    have h₁ : n ≥ 1 := h₁
    have : 0 > 0 := by
      calc 0
        _ = n ^ n := by rw [h]
        _ ≥ 1 ^ n := (Nat.pow_le_iff_le_left h₁).2 h₁
        _ > 0 := by simp
    contradiction


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact?
  · have : 1 ≤ n := by exact?
    exact?

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)
  intro k
  obtain ⟨N, hN⟩ := hs k
  use N + 1
  intro n hn
  have hn' : n ≥ 1 := le_trans (by simp) hn
  have aaaaah : n = (n - 1) + 1 := Nat.eq_add_of_sub_eq hn' rfl
  calc s n
    _ = s ((n - 1) + 1) := by rw [← aaaaah]
    _ ≥ k * s (n - 1) := hN (n - 1) (le_pred_of_lt hn)
    _ ≥ k * 1 := Nat.mul_le_mul_left k (h3s (n - 1))
    _ = k := by ring

end Growth
