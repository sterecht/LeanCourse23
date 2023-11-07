import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  specialize hs n (Nat.le_trans (Nat.le_max_left Ns Nt) hn)
  specialize ht n (Nat.le_trans (Nat.le_max_right Ns Nt) hn)
  calc |s n + t n - (a + b)|
    _ = |s n - a + (t n - b)| := by ring
    _ ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)
    _ < ε := by linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε hε
  obtain ⟨N, hN⟩ := cs (ε / |c|) (div_pos hε acpos)
  use N
  intro n hn
  simp
  calc |c * s n - c * a|
    _ = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := by gcongr; exact hN n hn
    _ = ε := by rw [← inv_mul_eq_div, ← mul_assoc, mul_inv_cancel (ne_of_gt acpos), one_mul]


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n|
    _ = |a + (s n - a)| := by ring
    _ ≤ |a| + |s n - a| := abs_add a (s n - a)
    _ < |a| + 1 := by linarith [h n hn]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp
  simp at h₁
  calc |s n * t n|
   _ = |s n| * |t n| := abs_mul (s n) (t n)
   _ ≤ B * |t n| := mul_le_mul_of_nonneg_right (le_of_lt (h₀ n (le_trans (le_max_left N₀ N₁) hn))) (abs_nonneg (t n))
   _ < B * (ε / B) := (mul_lt_mul_left Bpos).2 (h₁ n (le_trans (le_max_right N₀ N₁) hn))
   _ = ε := by rw [← inv_mul_eq_div, ← mul_assoc, mul_inv_cancel (ne_of_gt Bpos), one_mul]

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_pos.2 (sub_ne_zero.2 abne)
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := by
    calc |a - b|
      _ = |a - s N + (s N - b)| := by ring
      _ ≤ |a - s N| + |s N - b| := abs_add (a - s N) (s N - b)
      _ = |s N - a| + |s N - b| := by rw [abs_sub_comm a (s N)]
      _ < ε + ε := add_lt_add absa absb
      _ = |a - b| := by ring
  exact lt_irrefl _ this


section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
