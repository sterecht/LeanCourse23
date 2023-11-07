import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
  by_contra H
  have : p ∧ ¬p := by
    constructor
    · by_contra h
      apply H
      right
      exact h
    · intro h
      apply H
      left
      exact h
  exact this.2 this.1


/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  obtain ⟨N', hN'⟩ := hr N
  use N'
  intro n hn
  exact hN (r n) (hN' n hn)


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hs₁ (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hs₃ (ε / 3) (by linarith)
  use max N₁ N₂
  intro n hn
  specialize hs₁s₂ n
  specialize hs₂s₃ n
  specialize hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  specialize hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  have : s₃ n - s₁ n < 2 * ε / 3 :=
    calc s₃ n - s₁ n
      _ = s₃ n - a + (a - s₁ n) := by ring
      _ ≤ |s₃ n - a| + (a - s₁ n) := add_le_add_right (le_abs_self (s₃ n - a)) (a - s₁ n)
      _ ≤ |s₃ n - a| + |a - s₁ n| := add_le_add_left (le_abs_self (a - s₁ n)) |s₃ n - a|
      _ < ε / 3 + |a - s₁ n| := add_lt_add_right hN₂ |a - s₁ n|
      _ = ε / 3 + |s₁ n - a| := by rw [abs_sub_comm a (s₁ n)]
      _ < ε / 3 + ε / 3 := add_lt_add_left hN₁ (ε / 3)
      _ = 2 * ε / 3 := by ring
  calc |s₂ n - a|
    _ = |s₂ n - s₁ n + (s₁ n - a)| := by ring
    _ ≤ |s₂ n - s₁ n| + |s₁ n - a| := abs_add (s₂ n - s₁ n) (s₁ n - a)
    _ = s₂ n - s₁ n + |s₁ n - a| := by rw [abs_eq_self.2 (sub_nonneg.2 hs₁s₂)]
    _ = s₂ n - (s₁ n - |s₁ n - a|) := by ring
    _ ≤ s₃ n - (s₁ n - |s₁ n - a|) := by exact sub_le_sub_right hs₂s₃ (s₁ n - |s₁ n - a|)
    _ = s₃ n - s₁ n + |s₁ n - a| := by ring
    _ < 2 * ε / 3 + |s₁ n - a| := add_lt_add_right this |s₁ n - a|
    _ < 2 * ε / 3 + ε / 3 :=  add_lt_add_left hN₁ (2 * ε / 3)
    _ = ε := by ring


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
  intro ε hε
  use ⌈ε⁻¹⌉₊
  intro n hn
  simp
  rw [abs_inv, abs_eq_self.2 (le_of_lt (cast_add_one_pos n))]
  apply (inv_lt (cast_add_one_pos n) hε).2
  calc ε⁻¹
    _ ≤ ⌈ε⁻¹⌉₊ := le_ceil ε⁻¹
    _ ≤ n := cast_le.2 hn
    _ < n + 1 := by norm_num

/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  apply exercise3_3 use_me exercise3_4 <;>
  intro n <;>
  apply div_le_div_of_le (le_of_lt (cast_add_one_pos n))
  exact neg_one_le_sin ↑n
  exact sin_le_one ↑n

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := h
  obtain ⟨N, hN⟩ := h1 (u n - l) (sub_pos_of_lt hn)
  let m := max n N
  have : u n - l < u n - l := by
    calc u n - l
      _ ≤  u m - l := sub_le_sub_right (h2 n m (le_max_left n N)) l
      _ ≤ |u m - l| := le_abs_self (u m - l)
      _ < u n - l := hN m (le_max_right n N)
  exact LT.lt.false this

/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/

lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext; simp
  exact ⟨fun ⟨⟨x, hs, hf⟩, ht⟩ ↦ ⟨x, ⟨hs, mem_of_eq_of_mem hf ht⟩, hf⟩,
         fun ⟨x, ⟨hs, ht⟩, hf⟩ ↦ ⟨⟨x, hs, hf⟩, mem_of_eq_of_mem hf.symm ht⟩⟩

lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
  ext x; simp
  constructor
  · intro h
    have : 2 ^ 2 ≤ x ^ 2 := by norm_num; exact h
    have : |2| ≤ |x| := sq_le_sq.1 this
    norm_num at this
    exact le_abs'.1 this
  · intro h
    rw [← le_abs'] at h
    have : |2| ≤ |x| := by norm_num; exact h
    have : 2 ^ 2 ≤ x ^ 2 := sq_le_sq.2 this
    norm_num at this
    exact this


/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ f '' s ∪ g '' t
  let R : Set γ → Set α × Set β :=
    fun s ↦ (f⁻¹'s,g⁻¹'s)
  use L
  use R
  constructor
  · ext s x
    simp
    constructor
    · intro h
      rcases h with H | H <;>
      · obtain ⟨_, hx₁, rfl⟩ := H
        exact hx₁
    · intro h
      rcases h2' x with H₁ | H₂
      · left
        obtain ⟨y, hy⟩ := H₁
        use y
        exact ⟨mem_of_eq_of_mem hy h, hy⟩
      · right
        obtain ⟨y, hy⟩ := H₂
        use y
        exact ⟨mem_of_eq_of_mem hy h, hy⟩
  · ext ⟨s,t⟩ x <;> simp
    · constructor
      · intro h
        rcases h with h | h
        · obtain ⟨y, h₁, h₂⟩ := h
          exact mem_of_eq_of_mem (hf h₂).symm h₁
        · obtain ⟨y, _, h₂⟩ := h
          exfalso
          exact h1'' y x h₂
      · intro h
        left
        use x
    · constructor
      · intro h
        rcases h with h | h
        · obtain ⟨y, _, h₂⟩ := h
          exfalso
          exact h1' y x h₂
        · obtain ⟨y, h₁, h₂⟩ := h
          exact mem_of_eq_of_mem (hg h₂.symm) h₁
      · intro h
        right
        use x
