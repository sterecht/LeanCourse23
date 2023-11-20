import LeanCourse.Common
import Mathlib.AlgebraicGeometry.EllipticCurve.Point


open WeierstrassCurve Nat Int
/-
  We assume elliptic curves are in the form Y^2 = X^3 + a₄X + a₆
  This is always possible via a simple variable transformation
  unless the characteristic of the base field is 2 or 3
-/
variable {W : WeierstrassCurve ℚ} (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)

example : Point W := 0

def H : (Point W) → ℕ
  | 0 => 1
  | @Point.some _ _ _ x _ _ => max (natAbs x.num) x.den

def H_coord : ℤ → ℕ → ℕ :=
  fun p q ↦ if q = 0 then 0 else max (natAbs p) q / Nat.gcd (natAbs p) q

lemma H_pos (p : Point W) : H p > 0 := by
  rcases p with h | h
  · rw [H]; simp
  rw [H]; simp; right; apply Rat.pos

lemma H_symm (p : Point W) : H (-p) = H p := by
  rcases p with h | h
  · abel
  simp; rw [H, H]

lemma H_eq_coord (p : ℤ) (q : ℕ) (hq : q ≠ 0) (y : ℚ) (h : W.nonsingular (Rat.normalize p q hq) y) :
    H (Point.some h) = H_coord p q := by
  rw [H, H_coord]; simp; rw [if_neg hq, Rat.normalize_eq]; simp
  rw [natAbs_ediv]
  have : natAbs ↑(Nat.gcd (natAbs p) q) = Nat.gcd (natAbs p) q := rfl
  rw [this]
  by_cases hl : natAbs p ≤ q
  · have : natAbs p / Nat.gcd (natAbs p) q ≤ q / Nat.gcd (natAbs p) q :=
      Nat.div_le_div_right hl
    rw [Nat.max_eq_right hl, Nat.max_eq_right this]
  · simp at hl
    have : q / Nat.gcd (natAbs p) q ≤ natAbs p /Nat.gcd (natAbs p) q :=
      Nat.div_le_div_right (le_of_lt hl)
    rw [Nat.max_eq_left this, Nat.max_eq_left (le_of_lt hl)]
  apply @Int.dvd_trans (↑(Nat.gcd (natAbs p) q)) ↑(natAbs p) p
  exact ofNat_dvd.2 (Nat.gcd_dvd_left (natAbs p) q)
  by_cases 0 ≤ p <;> simp

lemma H_coord_le (p : ℤ) (q : ℕ) (hq : q ≠ 0) : H_coord p q ≤ max (natAbs p) q := by
  rw [H_coord, if_neg hq]
  exact Nat.div_le_self (max (natAbs p) q) (Nat.gcd (natAbs p) q)

lemma H_le_coord (p : ℤ) (q : ℕ) (hq : q ≠ 0) (y : ℚ) (h : W.nonsingular (Rat.normalize p q hq) y) :
    H (Point.some h) ≤ max (natAbs p) q := by
  rw [H_eq_coord]
  exact H_coord_le p q hq
