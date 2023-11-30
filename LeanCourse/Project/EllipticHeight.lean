import Mathlib.AlgebraicGeometry.EllipticCurve.Point
import LeanCourse.Project.WeierstrassHeight

open MvPolynomial Int

variable {E : EllipticCurve ℚ} (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
        (ha₄ : Rat.isInt E.a₄) (ha₆ : Rat.isInt E.a₆)

noncomputable section
namespace EllipticHeight

def D : ℤ := 4 * E.a₄.num ^ 3 + 27 * E.a₆.num ^ 2
def F : MvPolynomial (Fin 2) ℤ := (X 0) ^ 4 - C 2 * C E.a₄.num * (X 0) ^ 2 * (X 1) ^ 2 -
    C 8 * C E.a₆.num * X 0 * (X 1) ^ 3 + C E.a₄.num ^ 2 * (X 1) ^ 4
def G : MvPolynomial (Fin 2) ℤ := C 4 * (X 0) ^ 3 * X 1 + C 4 * C E.a₄.num * X 0 * (X 1) ^ 3 +
    C 4 * C E.a₆.num * (X 1) ^ 4
def f₁ : MvPolynomial (Fin 2) ℤ := C 12 * (X 0) ^ 2 * X 1 + C 16 * C E.a₄.num * (X 1) ^ 3
def g₁ : MvPolynomial (Fin 2) ℤ := C 3 * (X 0) ^ 3 - C 5 * C E.a₄.num * (X 0) * (X 1) ^ 2 -
    C 27 * C E.a₆.num * (X 1) ^ 3
def f₂ : MvPolynomial (Fin 2) ℤ := C (16 * E.a₄.num ^ 3 + 108 * E.a₆.num ^ 2) * (X 0) ^ 3 -
    C (4 * E.a₄.num ^ 2 * E.a₆.num) * (X 0) ^ 2 * X 1 +
    C (12 * E.a₄.num ^ 4 + 88 * E.a₄.num * E.a₆.num ^ 2) * (X 0) * (X 1) ^ 2 +
    C (12 * E.a₄.num ^ 3 * E.a₆.num + 96 * E.a₆.num ^ 3) * (X 1) ^ 3
def g₂ : MvPolynomial (Fin 2) ℤ := - C (E.a₄.num ^ 2 * E.a₆.num) * (X 0) ^ 3 -
    C (5 * E.a₄.num ^ 4 + 32 * E.a₄.num * E.a₆.num ^ 2) * (X 0) ^ 2 * X 1 -
    C (26 * E.a₄.num ^ 3 * E.a₆.num + 192 * E.a₆.num ^ 3) * X 0 * (X 1) ^ 2 +
    C (3 * E.a₄.num ^ 5 + 24 * E.a₄.num ^ 2 * E.a₆.num ^ 2) * (X 1) ^ 3

lemma D_disc : ((-16 * @D E) : ℚ) = E.Δ := by
  unfold D; unfold WeierstrassCurve.Δ
  unfold WeierstrassCurve.b₂; unfold WeierstrassCurve.b₄
  unfold WeierstrassCurve.b₆; unfold WeierstrassCurve.b₈
  push_cast; rw [← Rat.eq_num_of_isInt ha₄, ← Rat.eq_num_of_isInt ha₆]
  rw [ha₁, ha₂, ha₃]; ring

lemma D_ne : @D E ≠ 0 := by
  have : E.Δ ≠ 0 := by
    intro h
    have : E.Δ = (E.Δ' : ℚ) := E.coe_Δ'.symm
    rw [h] at this
    exact Units.ne_zero E.Δ' this.symm
  rw [← D_disc ha₁ ha₂ ha₃ ha₄ ha₆] at this
  simp at this; exact this

lemma pol_rel_1 (a b : ℤ) : eval ![a, b] (@f₁ E * @F E - @g₁ E * @G E) =
    eval ![a, b] (C (4 * @D E) * (X 1) ^ 7) := by
  unfold f₁; unfold F; unfold g₁; unfold G; unfold D; simp; ring

lemma pol_rel_2 (a b : ℤ) : eval ![a, b] (@f₂ E * @F E - @g₂ E * @G E) =
    MvPolynomial.eval ![a, b] (C (4 * @D E) * (X 0) ^ 7) := by
  unfold f₂; unfold F; unfold g₂; unfold G; unfold D; simp; ring

lemma pol_bound_1 (a b : ℤ) : natAbs (4 * @D E * b ^ 7) ≤ 2 *
    max (natAbs <| eval ![a, b] (@f₁ E)) (natAbs <| eval ![a, b] (@g₁ E)) *
    max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) := by
  have : MvPolynomial.eval ![a, b] (@f₁ E * @F E - @g₁ E * @G E) =
    MvPolynomial.eval ![a, b] (C (4 * @D E) * (X 1) ^ 7) := pol_rel_1 a b
  simp at this; rw [← this]
  apply le_trans (natAbs_sub_le _ _)
  rw [natAbs_mul, natAbs_mul]
  apply le_trans (add_le_add_right (Nat.mul_le_mul_right _ <| Nat.le_max_left (natAbs <| eval ![a, b] (@f₁ E)) (natAbs <| eval ![a, b] (@g₁ E))) _)
  apply le_trans (add_le_add_right (Nat.mul_le_mul_left _ <| Nat.le_max_left (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E))) _)
  rw [mul_assoc 2, two_mul]; apply add_le_add_left
  apply le_trans (Nat.mul_le_mul_right _ <|Nat.le_max_right (natAbs <| eval ![a, b] (@f₁ E)) (natAbs <| eval ![a, b] (@g₁ E)))
  apply Nat.mul_le_mul_left
  exact Nat.le_max_right (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E))

lemma pol_bound_2 (a b : ℤ) : natAbs (4 * @D E * a ^ 7) ≤ 2 *
    max (natAbs <| eval ![a, b] (@f₂ E)) (natAbs <| eval ![a, b] (@g₂ E)) *
    max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) := by
  have : eval ![a, b] (@f₂ E * @F E - @g₂ E * @G E) =
    MvPolynomial.eval ![a, b] (C (4 * @D E) * (X 0) ^ 7) := pol_rel_2 a b
  simp at this; rw [← this]
  apply le_trans (natAbs_sub_le _ _)
  rw [natAbs_mul, natAbs_mul]
  apply le_trans (add_le_add_right (Nat.mul_le_mul_right _ <| Nat.le_max_left (natAbs <| eval ![a, b] (@f₂ E)) (natAbs <| eval ![a, b] (@g₂ E))) _)
  apply le_trans (add_le_add_right (Nat.mul_le_mul_left _ <| Nat.le_max_left (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E))) _)
  rw [mul_assoc 2, two_mul]; apply add_le_add_left
  apply le_trans (Nat.mul_le_mul_right _ <|Nat.le_max_right (natAbs <| eval ![a, b] (@f₂ E)) (natAbs <| eval ![a, b] (@g₂ E)))
  apply Nat.mul_le_mul_left
  exact Nat.le_max_right (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E))

def Cf_1 : ℕ := 12 + 16 * natAbs E.a₄.num
def Cg_1 : ℕ := 3 + 5 * natAbs E.a₄.num + 27 * natAbs E.a₆.num
def Cf_2 : ℕ := (16 * natAbs E.a₄.num ^ 3 + 108 * natAbs E.a₆.num ^ 2) +
                4 * natAbs E.a₄.num ^ 2 * natAbs E.a₆.num +
                (12 * natAbs E.a₄.num ^ 4 + 88 * natAbs E.a₄.num * natAbs E.a₆.num ^ 2) +
                (12 * natAbs E.a₄.num ^ 3 * natAbs E.a₆.num + 96 * natAbs E.a₆.num ^ 3)
def Cg_2 : ℕ := natAbs E.a₄.num ^ 2 * natAbs E.a₆.num +
                (5 * natAbs E.a₄.num ^ 4 + 32 * natAbs E.a₄.num * natAbs E.a₆.num ^ 2) +
                (26 * natAbs E.a₄.num ^ 3 * natAbs E.a₆.num + 192 * natAbs E.a₆.num ^ 3) +
                (3 * natAbs E.a₄.num ^ 5 + 24 * natAbs E.a₄.num ^ 2 * natAbs E.a₆.num ^ 2)
def C_ineq_2 : ℕ := max (max (@Cf_1 E) (@Cg_1 E)) (max (@Cf_2 E) (@Cg_2 E))

lemma f_1_bound (a b : ℤ) : natAbs (eval ![a, b] (@f₁ E)) ≤
    (@Cf_1 E) * max (natAbs a ^ 3) (natAbs b ^ 3) := by
  unfold f₁; unfold Cf_1; simp
  apply le_trans (natAbs_add_le _ _)
  rw [add_mul]; gcongr
  · rw [natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow, mul_assoc]
    apply Nat.mul_le_mul_left
    apply le_trans (Nat.mul_le_mul_left _ <| Nat.le_max_right (natAbs a) (natAbs b))
    rw [pow_succ' _ 2]
    apply Nat.mul_le_mul_right
    rw [sq, sq]; apply Nat.mul_le_mul <;>
    exact Nat.le_max_left (natAbs a) (natAbs b)
  · rw [natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_of_le_left
    exact Nat.le_max_right (natAbs a) (natAbs b)

lemma g_1_bound (a b : ℤ) : natAbs (eval ![a, b] (@g₁ E)) ≤
    (@Cg_1 E) * max (natAbs a ^ 3) (natAbs b ^ 3) := by
  unfold g₁; unfold Cg_1; simp
  apply le_trans (natAbs_sub_le _ _)
  apply le_trans (add_le_add_right (natAbs_sub_le _ _) _)
  rw [add_mul, add_mul]; gcongr
  · rw [natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_of_le_left (Nat.le_max_left (natAbs a) (natAbs b)) 3
  · rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow, mul_assoc]
    apply Nat.mul_le_mul_left
    apply le_trans (Nat.mul_le_mul_right _ (Nat.le_max_left (natAbs a) (natAbs b)))
    rw [pow_succ _ 2]
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 2
  · rw [natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 3

lemma f_2_bound (a b : ℤ) : natAbs (eval ![a, b] (@f₂ E)) ≤
    (@Cf_2 E) * max (natAbs a ^ 3) (natAbs b ^ 3) := by
  unfold f₂; unfold Cf_2; simp
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  · rw [natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_of_le_left (Nat.le_max_left (natAbs a) (natAbs b)) 3))
    apply Nat.mul_le_mul_right
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow]
    rfl
  · rw [natAbs_neg, natAbs_mul, natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, mul_assoc]
    apply Nat.mul_le_mul_left
    rw [ ← Nat.max_pow, pow_succ' _ 2, natAbs_pow]
    apply le_trans (Nat.mul_le_mul_left _ <| Nat.le_max_right (natAbs a) (natAbs b))
    apply Nat.mul_le_mul_right
    exact Nat.pow_le_pow_of_le_left (Nat.le_max_left (natAbs a) (natAbs b)) 2
  · rw [natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow, pow_succ _ 2, ← mul_assoc]
    apply Nat.mul_le_mul _ <| Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 2
    apply Nat.mul_le_mul _ <| Nat.le_max_left (natAbs a) (natAbs b)
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow]
    rfl
  · rw [natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul _ <| Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 3
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow]
    rfl

lemma g_2_bound (a b : ℤ) : natAbs (eval ![a, b] (@g₂ E)) ≤
    (@Cg_2 E) * max (natAbs a ^ 3) (natAbs b ^ 3) := by
  unfold g₂; unfold Cg_2; simp
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  rw [add_mul _ _ (max _ _)]; apply le_trans (natAbs_add_le _ _); gcongr
  · rw [natAbs_neg, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_of_le_left (Nat.le_max_left (natAbs a) (natAbs b)) 3
  · rw [natAbs_neg, natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow, pow_succ' _ 2, ← mul_assoc]
    apply Nat.mul_le_mul _ <| Nat.le_max_right (natAbs a) (natAbs b)
    apply Nat.mul_le_mul _ <| Nat.pow_le_pow_of_le_left (Nat.le_max_left (natAbs a) (natAbs b)) 2
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow]
    rfl
  · rw [natAbs_neg, natAbs_mul, natAbs_mul, natAbs_pow, ← Nat.max_pow, pow_succ (max _ _) 2, ← mul_assoc]
    apply Nat.mul_le_mul _ <| Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 2
    apply Nat.mul_le_mul _ <| Nat.le_max_left (natAbs a) (natAbs b)
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow]
    rfl
  · rw [natAbs_mul, natAbs_pow, ← Nat.max_pow]
    apply Nat.mul_le_mul _ <| Nat.pow_le_pow_of_le_left (Nat.le_max_right (natAbs a) (natAbs b)) 3
    apply le_trans (natAbs_add_le _ _)
    apply le_of_eq
    rw [natAbs_mul, natAbs_mul, natAbs_mul, natAbs_pow, natAbs_pow, natAbs_pow]
    rfl

lemma F_G_bound (a b : ℤ) : natAbs (4 * @D E) * max (natAbs a ^ 4) (natAbs b ^ 4) ≤
    2 * @C_ineq_2 E * max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) := by
  by_cases h : natAbs a ≤ natAbs b
  · rw [← Nat.max_pow, max_eq_right h]
    by_cases hb : natAbs b = 0
    · rw [hb]; simp
    apply le_of_nsmul_le_nsmul <| pow_ne_zero 3 hb
    rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc, ← Nat.pow_add, ← natAbs_pow, ← natAbs_mul]
    apply le_trans (pol_bound_1 a b)
    rw [← mul_assoc]
    apply Nat.mul_le_mul_right
    rw [← mul_assoc, mul_comm _ 2, mul_assoc]
    apply Nat.mul_le_mul_left
    rw [mul_comm, ← max_eq_right h, Nat.max_pow]
    unfold C_ineq_2
    apply le_trans _ <| Nat.mul_le_mul_right _ <| Nat.le_max_left (max Cf_1 Cg_1) (max Cf_2 Cg_2)
    apply max_le
    · exact le_trans (f_1_bound a b) <| Nat.mul_le_mul_right _ <| Nat.le_max_left Cf_1 Cg_1
    · exact le_trans (g_1_bound a b) <| Nat.mul_le_mul_right _ <| Nat.le_max_right Cf_1 Cg_1
  · have h : natAbs b ≤ natAbs a := Nat.le_of_not_le h
    rw [← Nat.max_pow, max_eq_left h]
    by_cases ha : natAbs a = 0
    · rw [ha]; simp
    apply le_of_nsmul_le_nsmul <| pow_ne_zero 3 ha
    rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc, ← Nat.pow_add, ← natAbs_pow, ← natAbs_mul]
    apply le_trans (pol_bound_2 a b)
    rw [← mul_assoc]
    apply Nat.mul_le_mul_right
    rw [← mul_assoc, mul_comm _ 2, mul_assoc]
    apply Nat.mul_le_mul_left
    rw [mul_comm, ← max_eq_left h, Nat.max_pow]
    unfold C_ineq_2
    apply le_trans _ <| Nat.mul_le_mul_right _ <| Nat.le_max_right (max Cf_1 Cg_1) (max Cf_2 Cg_2)
    apply max_le
    · exact le_trans (f_2_bound a b) <| Nat.mul_le_mul_right _ <| Nat.le_max_left Cf_2 Cg_2
    · exact le_trans (g_2_bound a b) <| Nat.mul_le_mul_right _ <| Nat.le_max_right Cf_2 Cg_2


lemma gcd_le_4D {a b : ℤ} (h : Int.gcd a b = 1) :
    Int.gcd (eval ![a, b] (@F E)) (eval ![a, b] (@G E)) ≤ natAbs (4 * @D E) := by
  apply Nat.le_of_dvd
  · apply natAbs_pos.2; simp; exact D_ne ha₁ ha₂ ha₃ ha₄ ha₆
  have : Int.gcd (eval ![a, b] (@F E)) (eval ![a, b] (@G E)) ∣
      Nat.gcd (natAbs (4 * @D E * a ^ 7)) (natAbs (4 * @D E * b ^ 7)) := by
    apply Nat.dvd_gcd
    · have : eval ![a, b] (@f₂ E * @F E - @g₂ E * @G E) =
          MvPolynomial.eval ![a, b] (C (4 * @D E) * (X 0) ^ 7) := pol_rel_2 a b
      simp at this
      rw [← this, ← ofNat_dvd_left]
      apply Int.dvd_sub
      exact dvd_trans (Int.gcd_dvd_left _ _) (Int.dvd_mul_left _ _)
      exact dvd_trans (Int.gcd_dvd_right _ _) (Int.dvd_mul_left _ _)
    · have : eval ![a, b] (@f₁ E * @F E - @g₁ E * @G E) =
          MvPolynomial.eval ![a, b] (C (4 * @D E) * (X 1) ^ 7) := pol_rel_1 a b
      simp at this
      rw [← this, ← ofNat_dvd_left]
      apply Int.dvd_sub
      exact dvd_trans (Int.gcd_dvd_left _ _) (Int.dvd_mul_left _ _)
      exact dvd_trans (Int.gcd_dvd_right _ _) (Int.dvd_mul_left _ _)
  rw [natAbs_mul, natAbs_mul _ (b ^ 7), Nat.gcd_mul_left, natAbs_pow, natAbs_pow] at this
  have hg : Nat.gcd (natAbs a ^ 7) (natAbs b ^ 7) = 1 := by
    have : Int.gcd (a ^ 7) b = 1 := gcd_pow_left 7 h
    have : Int.gcd (a ^ 7) (b ^ 7) = 1 := gcd_pow_right 7 this
    unfold Int.gcd at this; rw [← natAbs_pow,←  natAbs_pow]; exact this
  rw [hg, mul_one] at this
  exact this

lemma H_F_div_G_bound {a b : ℤ} (h : Int.gcd a b = 1) (hG : eval ![a, b] (@G E) ≠ 0) :
    max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) ≤
    natAbs (4 * @D E) * (H_q <| ((eval ![a, b] (@F E)) : ℚ) / ((eval ![a, b] (@G E)) : ℚ)) := by
  have : Int.gcd (eval ![a, b] (@F E)) (eval ![a, b] (@G E)) ∣
      max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) := by
    by_cases hf : natAbs (eval ![a, b] (@F E)) ≤ natAbs (eval ![a, b] (@G E))
    · rw [max_eq_right hf]; unfold Int.gcd; exact Nat.gcd_dvd_right _ _
    · simp at hf; rw [max_eq_left <| le_of_lt hf]; unfold Int.gcd; exact Nat.gcd_dvd_left _ _
  rw [← Nat.mul_div_cancel' this]
  rw [Hq_eq_coord hG]
  have : 0 < max (natAbs <| eval ![a, b] (@F E)) (natAbs <| eval ![a, b] (@G E)) /
      Int.gcd (eval ![a, b] (@F E)) (eval ![a, b] (@G E)) := by
    by_contra hf
    simp at hf
    rw [Nat.div_eq_zero_iff] at hf
    · absurd hf; apply not_lt_of_le; unfold Int.gcd
      exact le_trans (Nat.gcd_le_right _ (natAbs_pos.2 hG)) (le_max_right _ _)
    · exact gcd_pos_of_ne_zero_right _ hG
  exact (mul_le_mul_right this).2 (gcd_le_4D ha₁ ha₂ ha₃ ha₄ ha₆ h)

open WeierstrassCurve Polynomial

lemma two_tor_eq_y0 {x y : ℚ} (h : E.equation x y) : 2 • (Point.some (E.nonsingular h)) = 0 ↔ y = 0 := by
  have r : 2 • (Point.some (E.nonsingular h)) = Point.some (E.nonsingular h) + Point.some (E.nonsingular h) := rfl
  constructor <;> intro hp
  · by_cases hy : y = E.negY x y
    · unfold negY at hy; simp[ha₁, ha₃] at hy; exact hy
    · rw [r, Point.some_add_some_of_Y_ne' rfl hy] at hp; simp at hp
  · have : y = E.negY x y := by unfold negY; simp[ha₁, ha₃]; exact hp
    rw [r, Point.some_add_self_of_Y_eq this]

private def f : E.Point → ℚ
  | 0 => 0
  | @Point.some _ _ _ x _ _ => x

private lemma f_inj : Set.InjOn f {p : E.Point | p ≠ 0 ∧ 2 • p = 0} := by
  intro p hp q hq hpq
  simp at hp; simp at hq; unfold f at hpq
  rcases p with h | @⟨x₁,y₁,hx₁⟩
  · absurd hp.1; rfl
  rcases q with h | @⟨x₂,y₂,hx₂⟩
  · absurd hq.1; rfl
  simp at hpq
  have hy₁ : y₁ = 0 := (two_tor_eq_y0 ha₁ ha₃ hx₁.1).1 hp.2
  have hy₂ : y₂ = 0 := (two_tor_eq_y0 ha₁ ha₃ hx₂.1).1 hq.2
  have hy : y₁ = y₂ := by rw [← hy₂] at hy₁; exact hy₁
  simp; exact ⟨hpq, hy⟩

private lemma f_range : f '' {p : E.Point | p ≠ 0 ∧ 2 • p = 0} = {x : ℚ | 0 = x ^ 3 + E.a₄ * x + E.a₆} := by
  ext x; constructor <;> intro h
  · simp; obtain ⟨p, hp, hpx⟩ := h; simp at hp
    rcases p with h | @⟨x',y,h⟩
    · absurd hp.1; rfl
    unfold f at hpx; simp at hpx
    have eq : E.equation x y := by rw [← hpx]; exact h.1
    unfold WeierstrassCurve.equation at eq; unfold WeierstrassCurve.polynomial at eq
    simp[ha₁, ha₂, ha₃] at eq
    rw [(two_tor_eq_y0 ha₁ ha₃ h.1).1 hp.2] at eq
    simp at eq; rw [← neg_eq_zero] at eq; simp at eq
    exact eq.symm
  · simp at h
    have : E.equation x 0 := by
      unfold WeierstrassCurve.equation; unfold WeierstrassCurve.polynomial
      simp; rw [← neg_eq_zero]; simp[ha₂]; exact h.symm
    use EllipticCurve.Point.mk E this
    simp; constructor; constructor
    · unfold EllipticCurve.Point.mk; simp
    · exact (two_tor_eq_y0 ha₁ ha₃ this).2 rfl
    · unfold f; unfold EllipticCurve.Point.mk; simp

lemma two_tor_fin : Set.Finite {p : E.Point | 2 • p = 0} := by
  have : {p : E.Point | 2 • p = 0} = Set.insert 0 {p : E.Point | p ≠ 0 ∧ 2 • p = 0} := by
    ext p; constructor <;> simp <;> intro h
    · by_cases hp : p = 0
      left; exact hp
      right; simp; exact ⟨hp, h⟩
    · rcases h with h | h
      rw [h]; rfl
      simp at h; exact h.2
  rw [this]
  apply Set.Finite.insert
  apply Set.Finite.of_finite_image _ <| f_inj ha₁ ha₃
  rw [f_range ha₁ ha₂ ha₃]
  let P : ℚ[X] := Polynomial.X ^ 3 + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆
  have : {x | 0 = x ^ 3 + E.a₄ * x + E.a₆} = {x | Polynomial.IsRoot P x} := by
    ext x; simp; exact eq_comm
  rw [this]
  have : P ≠ 0 := by
    intro h
    rw [Polynomial.ext_iff] at h
    specialize h 3; simp at h
  exact Polynomial.finite_setOf_isRoot this

def C_tor : ℕ := (Finset.max' (Finset.image (@H E.toWeierstrassCurve) <| Set.Finite.toFinset (two_tor_fin ha₁ ha₂ ha₃))
    (by use 1; simp; use 0; simp; rfl)) ^ 4

lemma H_two_tor_le (p : E.Point) (h : 2 • p = 0) : H p ≤ C_tor ha₁ ha₂ ha₃ := by
  unfold C_tor
  apply le_trans (Nat.le_pow (by norm_num : 0 < 4))
  apply Nat.pow_le_pow_of_le_left _ 4
  apply Finset.le_max'
  rw [Finset.mem_image]
  use p; simp; exact h

theorem height_ineq2 : ∃ C > 0, ∀ p : E.Point, C * H (2 • p) ≥ (H p) ^ 4 := by
  use max (C_tor ha₁ ha₂ ha₃) (2 * @C_ineq_2 E) ; constructor
  · exact lt_of_lt_of_le (lt_of_lt_of_le (H_pos 0) (H_two_tor_le ha₁ ha₂ ha₃ 0 rfl)) (le_max_left _ _)
  intro p
  by_cases h : 2 • p = 0
  · rw [h]; simp; left
    unfold C_tor
    apply Nat.pow_le_pow_of_le_left _ 4
    apply Finset.le_max'
    rw [Finset.mem_image]
    use p; simp; exact h
  rcases p with h0 | @⟨x,y,hp⟩
  · absurd h; rw [Point.zero_def]; rfl
  have hy : y ≠ 0 := fun hy ↦ h <| (two_tor_eq_y0 ha₁ ha₃ hp.1).2 hy
  have hy' : y ≠ negY E.toWeierstrassCurve x y := by
    unfold negY; rw [ha₁, ha₃]; simp; exact hy
  have : 2 • (Point.some hp) = (Point.some hp) + (Point.some hp) := rfl
  rw [this, Point.some_add_some_of_Y_ne' rfl hy', Hxy_eq_Hx, H_symm, Hxy_eq_Hx]
  simp; unfold slope; rw [if_pos rfl, if_neg hy', ha₁, ha₂]; simp
  rw [ha₁, ha₃]; simp
  have eq : WeierstrassCurve.equation E.toWeierstrassCurve x y := hp.1
  have eq : y ^ 2 = x ^ 3 + E.a₄ * x + E.a₆ := by
    unfold WeierstrassCurve.equation at eq; unfold WeierstrassCurve.polynomial at eq
    simp[ha₁,ha₂,ha₃] at eq; rw [sub_eq_zero] at eq; exact eq
  have : (y + y) ^ 2 = 4 * x ^ 3 + 4 * E.a₄ * x + 4 * E.a₆ := by
    ring; rw [eq]; ring
  have den1 : 4 * x ^ 3 + 4 * E.a₄ * x + 4 * E.a₆ ≠ 0 := by
    rw [← this]; simp; exact hy
  have : (3 * x ^ 2 + E.a₄) ^ 2 / (y + y) ^ 2 - x - x =
      (x ^ 4 - 2 * E.a₄ * x ^ 2 - 8 * E.a₆ * x + E.a₄ ^ 2) / (4 * x ^ 3 + 4 * E.a₄ * x + 4 * E.a₆) := by
    rw [this]; field_simp; ring
  apply le_trans _ <| Nat.mul_le_mul_right _ (le_max_right (C_tor ha₁ ha₂ ha₃) _)
  rw [this]
  let a := x.num
  let b := (x.den : ℤ)
  have ha : a = x.num := rfl
  have hb : b = (x.den : ℤ) := rfl
  have hab : Int.gcd a b = 1 := by unfold Int.gcd; simp; exact x.reduced
  have hG : eval ![a, b] (@G E) ≠ 0 := by
    unfold G; simp; intro h
    have h : ((((4 : ℤ) * x.num ^ 3 * (x.den : ℤ) + (4 : ℤ) * E.a₄.num * x.num * (x.den : ℤ) ^ 3 +
        (4 : ℤ) * E.a₆.num * (x.den : ℤ) ^ 4) : ℤ) : ℚ) / ((((x.den : ℤ) ^ 4) : ℤ) : ℚ) = 0 := by
      rw [h]; simp
    push_cast at h; rw [add_div, add_div, mul_div_cancel _ (by simp; exact x.den_nz)] at h
    rw [mul_div_assoc, mul_div_assoc, pow_succ _ 3, div_mul_eq_div_div, div_self (by simp; exact x.den_nz)] at h
    rw [← mul_div_assoc, mul_one, ← pow_succ, pow_succ' _ 3, div_mul_eq_div_div, div_self (by simp; exact x.den_nz)] at h
    rw [← mul_div_assoc, mul_one, mul_div_assoc, ← div_pow, mul_div_assoc, Rat.num_div_den] at h
    rw [← Rat.eq_num_of_isInt ha₄, ← Rat.eq_num_of_isInt ha₆] at h; exact den1 h
  have : ((eval ![a, b] (@G E)) : ℚ) ≠ 0 := by norm_num; exact hG
  have hden2 : 4 * (x.num : ℚ) ^ 3 * (x.den : ℚ) + 4 * (E.a₄.num : ℚ) * (x.num : ℚ) * (x.den : ℚ) ^ 3 +
        4 * (E.a₆.num : ℚ) * (x.den : ℚ) ^ 4 ≠ 0 := by
    unfold G at hG; simp at hG
    have : (((4 * x.num ^ 3 * (x.den : ℤ) + 4 * E.a₄.num * x.num * (x.den : ℤ) ^ 3 + 4 * E.a₆.num * (x.den : ℤ) ^ 4) : ℤ) : ℚ) =
        4 * (x.num : ℚ) ^ 3 * (x.den : ℚ) + 4 * (E.a₄.num : ℚ) * (x.num : ℚ) * (x.den : ℚ) ^ 3 + 4 * (E.a₆.num : ℚ) * (x.den : ℚ) ^ 4 :=
      by norm_cast
    rw [← this]; norm_cast
  have : (x ^ 4 - 2 * E.a₄ * x ^ 2 - 8 * E.a₆ * x + E.a₄ ^ 2) / (4 * x ^ 3 + 4 * E.a₄ * x + 4 * E.a₆) =
      ((eval ![a, b] (@F E)) : ℚ) / ((eval ![a, b] (@G E)) : ℚ) := by
    unfold F; unfold G; field_simp; rw [← Rat.eq_num_of_isInt ha₄, ← Rat.eq_num_of_isInt ha₆]
    have : (x.den : ℚ) = ((x.den : ℤ) : ℚ) := rfl
    rw [← ha, this, ← hb, ← Rat.num_div_den x]
    have : (x.den : ℚ) ≠ 0 := by simp; exact x.den_nz
    have : (x.den : ℚ) ^ 2 ≠ 0 := by simp; exact x.den_nz
    have : (x.den : ℚ) ^ 3 ≠ 0 := by simp; exact x.den_nz
    have : (x.den : ℚ) ^ 4 ≠ 0 := by simp; exact x.den_nz
    field_simp; ring
  rw [this]
  have : natAbs (4 * (@D E)) ≠ 0 :=
    natAbs_ne_zero.2 <| Int.mul_ne_zero (by norm_num) <| D_ne ha₁ ha₂ ha₃ ha₄ ha₆
  apply le_of_nsmul_le_nsmul this
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm _ (2 * C_ineq_2), mul_assoc]
  apply le_trans _ <| Nat.mul_le_mul_left _ <| H_F_div_G_bound ha₁ ha₂ ha₃ ha₄ ha₆ hab hG
  apply le_trans _ <| F_G_bound a b
  apply Nat.mul_le_mul_left
  apply le_of_eq
  rw [← Nat.max_pow]
  apply congrFun (congrArg HPow.hPow _) 4
  unfold H_q; unfold H_coord; rw [if_neg x.den_nz, x.reduced, Nat.div_one]
  simp




end EllipticHeight
