import LeanCourse.Common
import Mathlib.AlgebraicGeometry.EllipticCurve.Point

open Nat Int BigOperators
/-
  Mostly helper functions that I couldn't find in mathlib.
  Some of these, or at least equivalent statements, probably exist somewhere,
  but it would have taken longer to find them than to prove them here.
-/
lemma eq_abs_of_lin_dep {a b c d : ℤ} (h : a * b + c * d = 0)
    (hac : Int.gcd c a = 1) (hbd : Int.gcd b d = 1) : natAbs b = natAbs c := by
  have : natAbs a * natAbs b = natAbs c * natAbs d := by
    rw [← natAbs_mul, ← natAbs_mul]
    rw [add_eq_zero_iff_eq_neg.1 h]
    simp
  apply Nat.dvd_antisymm
  rw [← Coprime.dvd_mul_right hbd]
  use natAbs a; rw [← this, mul_comm]
  rw [← Coprime.dvd_mul_right hac]
  use natAbs d; rw[← this, mul_comm]

lemma finsuppprod_pow (f : ℕ →₀ ℕ) (g : ℕ → ℕ → ℕ) (m : ℕ) :
    (Finsupp.prod f g) ^ m = Finsupp.prod f fun x y ↦ (g x y) ^ m := by
  unfold Finsupp.prod
  simp
  exact (Finset.prod_pow f.support m fun x ↦ g x (f x)).symm

lemma gcd_pow_left {a b : ℤ} (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd (a ^ n) b = 1 := by
  unfold Int.gcd at *
  have : Coprime (natAbs a ^ n) (natAbs b ^ 1) := Nat.Coprime.pow n 1 h
  rw [natAbs_pow a n]
  simp at *
  exact this

lemma gcd_pow_right {a b : ℤ} (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd a (b ^ n) = 1 := by
  rw [Int.gcd_comm] at *
  exact gcd_pow_left n h

-- This lemma is more complicated: If ab^n+c^md with everything coprime, b is an m-th power and c an n-th power.
lemma root_of_copr_exp {a d : ℤ} {b c n m : ℕ} (hb : b ≠ 0) (hc : c ≠ 0) (h : a * (b : ℤ) ^ n + (c : ℤ) ^ m * d = 0)
    (hac : Int.gcd c a = 1) (hbd : Int.gcd b d = 1) (hmn : Nat.gcd m n = 1) (hm : 0 < m) (hn : 0 < n) :
    ∃ e : ℕ, e ^ m = b ∧ e ^ n = c := by
  have : natAbs ((b : ℤ) ^ n) = natAbs ((c : ℤ) ^ m) :=
    eq_abs_of_lin_dep h (gcd_pow_left m hac) (gcd_pow_left n hbd)
  simp at this
  norm_cast at this
  have hp : ∀ p : ℕ, Nat.Prime p → m ∣ (Nat.factorization (b ^ n) p) := by
    intro p _
    use c.factorization p
    rw [this]
    simp
  have hp2 : ∀ p : ℕ, Nat.Prime p → m ∣ (b.factorization p) := by
    intro p h
    have : m ∣ (b ^ n).factorization p := hp p h
    simp at this
    rw [mul_comm] at this
    exact (Coprime.dvd_mul_right hmn).1 this
  use Finsupp.prod (Nat.factorization b) (fun x y ↦ x ^ (y / m))
  constructor
  let xy := Nat.factorization b
  have xyz : xy = Nat.factorization b := rfl
  rw [← xyz, ← factorization_prod_pow_eq_self hb, xyz]
  rw [finsuppprod_pow (Nat.factorization b) (fun x y ↦ x ^ (y / m)) m]
  apply Finsupp.prod_congr
  intro p h
  rw [← Nat.pow_mul]
  apply congrArg (HPow.hPow p)
  rw [mul_comm]
  exact Nat.mul_div_cancel' (hp2 p <| prime_of_mem_factorization h)
  rw [← factorization_prod_pow_eq_self hc]
  unfold Finsupp.prod
  dsimp
  have hh : n • b.factorization = m • c.factorization := by
    rw [← Nat.factorization_pow, ← Nat.factorization_pow, this]
  have hs : b.factorization.support = c.factorization.support := by
    have : b.factorization.support = (n • b.factorization).support := by
      ext y; constructor <;> rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff] <;> intro hy
      simp; push_neg; exact ⟨(Nat.ne_of_lt hn).symm, hy⟩
      intro h; simp at hy; rw [h] at hy; simp at hy
    rw [this, hh]
    ext y; constructor <;> rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff] <;> intro hy
    intro h; simp at hy; rw [h] at hy; simp at hy
    simp; push_neg; exact ⟨(Nat.ne_of_lt hm).symm, hy⟩
  rw [hs, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro x hx
  rw [← Nat.pow_mul]
  apply congrArg (HPow.hPow x)
  have hx : x.Prime := prime_of_mem_factorization hx
  rw [← Nat.mul_div_cancel (c.factorization x) hm, mul_comm _ n, ← Nat.mul_div_assoc n <| hp2 x hx]
  apply (Nat.div_left_inj (Dvd.dvd.mul_left (hp2 x hx) n) ⟨c.factorization x, mul_comm (c.factorization x) m⟩).2
  rw [mul_comm _ m]
  calc n * b.factorization x
    _ = (n • b.factorization) x := rfl
    _ = (m • c.factorization) x := by rw [hh]
    _ = m * c.factorization x   := rfl

lemma Rat.reduced' (x : ℚ) : Int.gcd (x.den : ℤ) x.num = 1 := by
  unfold Int.gcd
  simp
  rw [Nat.gcd_comm]
  exact x.reduced

lemma Int.gcd_add_mul_self (a b c : ℤ) : Int.gcd a (b + c * a) = Int.gcd a b := by
  unfold gcd; apply (Nat.gcd_eq_iff (natAbs a) (natAbs (b + c * a))).2
  constructor; exact Nat.gcd_dvd_left (natAbs a) (natAbs b)
  constructor
  rw [← ofNat_dvd_left]; apply Int.dvd_add; rw [ofNat_dvd_left]
  exact Nat.gcd_dvd_right (natAbs a) (natAbs b)
  apply Dvd.dvd.mul_left _ c; rw [ofNat_dvd_left]
  exact Nat.gcd_dvd_left (natAbs a) (natAbs b)
  intro d hd hd2
  apply Nat.dvd_gcd; exact hd
  rw [← ofNat_dvd_left] at *
  have : b = b + c * a - c * a := by ring
  rw [this]; apply Int.dvd_sub; exact hd2
  exact Dvd.dvd.mul_left hd c

lemma Nat.max_sq {a b : ℕ} : max a b ^ 2 = max (a ^ 2) (b ^ 2) := by
  wlog h : a ≤ b generalizing a b
  · simp at h; rw [max_comm, max_comm (a ^ 2)]
    exact this (le_of_lt h)
  rw [max_eq_right h, max_eq_right (pow_le_pow_of_le_left h 2)]

lemma Nat.max_pow {a b n : ℕ} : max a b ^ n = max (a ^ n) (b ^ n) := by
  wlog h : a ≤ b generalizing a b
  · simp at h; rw [max_comm, max_comm (a ^ n)]
    exact this (le_of_lt h)
  rw [max_eq_right h, max_eq_right (pow_le_pow_of_le_left h n)]

lemma Nat.le_sq {a : ℕ} : a ≤ a ^ 2 := by
  by_cases a = 0; rw [h]; simp
  push_neg at h
  rw [← Nat.pos_iff_ne_zero] at h
  calc a
    _ = a * 1 := (mul_one a).symm
    _ ≤ a * a := Nat.mul_le_mul_left a h
    _ = a ^ 2 := (Nat.pow_two a).symm

lemma Nat.le_pow {a n : ℕ} (hn : 0 < n) : a ≤ a ^ n := by
  by_cases a = 0; rw [h]; simp
  push_neg at h
  rw [← Nat.pos_iff_ne_zero] at h
  induction' n with k hk
  absurd hn; simp
  by_cases H : k = 0
  rw [H]; simp
  calc a
    _ = a * 1 := (mul_one a).symm
    _ ≤ a * a := Nat.mul_le_mul_left a h
    _ ≤ a * a ^ k := Nat.mul_le_mul_left a <| hk (Nat.pos_of_ne_zero H)
    _ = a ^ (k + 1) := Nat.pow_succ'.symm

lemma Nat.le_of_sq_le {a b : ℕ} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra h'
  simp at h'
  have : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_of_lt_left h' (by norm_num)
  linarith

lemma Nat.add_le_self {a b : ℕ} (h : a + b ≤ a) : b = 0 :=
  le_zero.1 <| (Nat.add_le_add_iff_left a b 0).1 h

lemma Nat.max_div {a b c : ℕ} : max (a / c) (b / c) = max a b / c := by
  wlog h : a ≤ b
  · simp at h; rw [max_comm, max_comm a b]
    exact this (le_of_lt h)
  rw [max_eq_right h, max_eq_right (Nat.div_le_div_right h)]
