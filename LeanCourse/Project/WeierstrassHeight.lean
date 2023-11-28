import LeanCourse.Common
import Mathlib.AlgebraicGeometry.EllipticCurve.Point

set_option maxHeartbeats 500000
/-
  This file introduces the height of a rational number and the height of a point
  on a Weierstrass curve. We prove two of the three required inequalities of the
  descent theorem for Mordell-Weil. (These don't require the curve to be non-singular).
  Reference: J Silverman, The Arithmetic of Elliptic Curves, VIII.4
-/

open WeierstrassCurve Nat Int BigOperators

/-
  We assume elliptic curves are in short Weierstraß form
  Y^2 = X^3 + a₄X + a₆ with a₄, a₆ ∈ ℤ.
  This is always possible via a simple variable transformation
  unless the characteristic of the base field is 2 or 3
  TODO : show this
-/
variable {W : WeierstrassCurve ℚ} (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
        (ha₄ : Rat.isInt W.a₄) (ha₆ : Rat.isInt W.a₆)

example : Point W := 0

/-
  The (absolute, multiplicative) height of a rational p/q is
  max |p| |q| if gcd p q = 1, or max |p| |q| / gcd p q in general.
  The height of a point on an elliptic curve is the height of its x-coordinate.
-/
def H : (Point W) → ℕ
  | 0 => 1
  | @Point.some _ _ _ x _ _ => max (natAbs x.num) x.den

def H_coord : ℤ → ℕ → ℕ :=
  fun p q ↦ if q = 0 then 0 else max (natAbs p) q / Nat.gcd (natAbs p) q

def H_q : ℚ → ℕ := fun r ↦ H_coord r.num r.den

@[simp]
lemma H_zero : @H W 0 = 1 := rfl
lemma H_some {x y : ℚ} {h : W.nonsingular x y} : @H W (@Point.some _ _ _ x y h) = max (natAbs x.num) x.den := rfl
lemma Hxy_eq_Hx {x y : ℚ} (h : W.nonsingular x y) : @H W (@Point.some _ _ _ x y h) = H_q x := by
  rw [H_some, H_q, H_coord, if_neg x.den_nz, x.reduced]; simp

lemma H_pos (p : Point W) : H p > 0 := by
  rcases p with h | h
  · rw [H]; simp
  rw [H]; simp; right; apply Rat.pos

lemma H_symm (p : Point W) : H (-p) = H p := by
  rcases p with h | h
  · abel
  simp; rw [H, H]

/-
  Lots of helper lemmas
  TODO: sort, namespaces, maybe separate files
-/
lemma H_q_symm (r : ℚ) : H_q (-r) = H_q r := by
  unfold H_q
  unfold H_coord
  rw [if_neg r.den_nz, if_neg (-r).den_nz]
  simp

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

lemma H_eq_coord_q (r : ℚ) (y : ℚ) (h : W.nonsingular r y) : H (Point.some h) = H_q r := by
  rw [H_q]
  let h' := h
  rw [← Rat.normalize_self r] at h'
  have : H (Point.some h') = H_coord r.num r.den := H_eq_coord r.num r.den r.den_nz y h'
  rw [← this]
  apply congrArg H
  simp
  exact (Rat.normalize_self r).symm

lemma H_coord_le (p : ℤ) (q : ℕ) (hq : q ≠ 0) : H_coord p q ≤ max (natAbs p) q := by
  rw [H_coord, if_neg hq]
  exact Nat.div_le_self (max (natAbs p) q) (Nat.gcd (natAbs p) q)

lemma H_le_coord (p : ℤ) (q : ℕ) (hq : q ≠ 0) (y : ℚ) (h : W.nonsingular (Rat.normalize p q hq) y) :
    H (Point.some h) ≤ max (natAbs p) q := by
  rw [H_eq_coord]
  exact H_coord_le p q hq

lemma Hq_le_frac {a b : ℤ} (hb : b ≠ 0) : H_q ((a : ℚ) / (b : ℚ)) ≤ max (natAbs a) (natAbs b) := by
  wlog h : 0 ≤ b generalizing a b
  · simp at h
    rw [← natAbs_neg b, ← H_q_symm, ← div_neg]
    exact this (by linarith : -b ≠ 0) (by linarith : 0 ≤ -b)
  have : ∃ b' : ℕ, (b' : ℤ) = b := CanLift.prf b h
  obtain ⟨b', h⟩ := this
  subst h
  have : (a : ℚ) / (b' : ℚ) = mkRat a b' := Rat.mkRat_eq_div.symm
  have ht : ((b' : ℤ) : ℚ) = (b' : ℚ) := rfl
  rw [ht, this]
  unfold H_q
  unfold H_coord
  rw [if_neg (mkRat a b').den_nz, (mkRat a b').reduced, Nat.div_one]
  unfold mkRat
  norm_num at hb
  rw [dif_neg hb]
  unfold Rat.normalize
  simp only [Rat.maybeNormalize_eq]
  by_cases natAbs (div a ↑(Nat.gcd (natAbs a) b')) ≤ b' / Nat.gcd (natAbs a) b'
  rw [max_eq_right h]; apply le_trans <| Nat.div_le_self _ _
  simp
  rw [not_le] at h; rw [max_eq_left (le_of_lt h)]
  simp; left; exact Nat.div_le_self (natAbs a) (Nat.gcd (natAbs a) b')

lemma eq_abs_of_lin_dep {a b c d : ℤ} (h : a * b + c * d = 0) (hac : Int.gcd c a = 1) (hbd : Int.gcd b d = 1) : natAbs b = natAbs c := by
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

lemma gcd_pow_left {a b : ℤ} (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd ((a : ℤ) ^ n) b = 1 := by
  unfold Int.gcd at *
  have : Coprime (natAbs a ^ n) (natAbs b ^ 1) := Nat.Coprime.pow n 1 h
  rw [natAbs_pow a n]
  simp at *
  exact this

lemma gcd_pow_right {a b : ℤ} (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd a (b ^ n) = 1 := by
  rw [Int.gcd_comm] at *
  exact gcd_pow_left n h

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
  have hh : n • b.factorization = m • c.factorization := by rw [← Nat.factorization_pow, ← Nat.factorization_pow, this]
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

lemma Nat.le_of_sq_le {a b : ℕ} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra h'
  simp at h'
  have : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_of_lt_left h' (by norm_num)
  linarith

lemma Nat.add_le_self {a b : ℕ} (h : a + b ≤ a) : b = 0 := by
  have : a + b ≤ a + 0 := by rw [add_zero]; exact h
  have : b ≤ 0 := (Nat.add_le_add_iff_left a b 0).1 h
  exact le_zero.1 this

lemma point_den_sq_cb {x y : ℚ} (h : W.equation x y) : ∃ d : ℕ, d ^ 2 = x.den ∧ d ^ 3 = y.den := by
  unfold WeierstrassCurve.equation at h
  unfold WeierstrassCurve.polynomial at h
  simp[ha₁, ha₂, ha₃] at h
  have : y.num ^ 2 * (x.den : ℤ) ^ 3 + (y.den : ℤ) ^ 2 * -(x.num ^ 3 + W.a₄.num * x.num * (x.den : ℤ) ^ 2 + W.a₆.num * (x.den : ℤ) ^ 3) = 0 := by
    apply (Rat.coe_int_inj _ _).1
    push_cast
    have hy2 : (y.den : ℚ) ^ 2 ≠ 0 := by norm_cast; exact pow_ne_zero 2 y.den_nz
    apply (div_left_inj' hy2).1
    rw [zero_div, _root_.add_div, mul_div_right_comm, mul_div_right_comm, div_self hy2, one_mul, ← div_pow, Rat.num_div_den]
    have hx2 : (x.den : ℚ) ^ 2 ≠ 0 := by norm_cast; exact pow_ne_zero 2 x.den_nz
    have hx3 : (x.den : ℚ) ^ 3 ≠ 0 := by norm_cast; exact pow_ne_zero 3 x.den_nz
    apply (div_left_inj' hx3).1
    rw [zero_div, _root_.add_div, mul_div_assoc, div_self hx3, mul_one, neg_div, _root_.add_div, _root_.add_div]
    rw [← div_pow, Rat.num_div_den, mul_div_assoc, mul_div_assoc, div_self hx3, mul_one, ← Rat.eq_num_of_isInt ha₄, ← Rat.eq_num_of_isInt ha₆]
    rw [_root_.pow_succ' (x.den : ℚ) 2, div_mul_eq_div_div, div_self hx2, ← mul_div_assoc, mul_one, mul_div_assoc, Rat.num_div_den]
    rw [← h]; ring
  have hg : Int.gcd (x.den : ℤ) (-(x.num ^ 3 + W.a₄.num * x.num * (x.den : ℤ) ^ 2 + W.a₆.num * (x.den : ℤ) ^ 3)) = 1 := by
    have : -(x.num ^ 3 + W.a₄.num * x.num * (x.den : ℤ) ^ 2 + W.a₆.num * (x.den : ℤ) ^ 3) =
        -x.num ^ 3 + -(W.a₄.num * x.num * (x.den : ℤ) + W.a₆.num * (x.den : ℤ) ^ 2) * (x.den : ℤ) := by ring
    rw [this, Int.gcd_add_mul_self, gcd_neg_right, Int.gcd_comm]
    exact gcd_pow_left 3 x.reduced
  exact root_of_copr_exp x.den_nz y.den_nz this (gcd_pow_right 2 y.reduced') hg (by norm_num) (by linarith) (by linarith)

lemma point_coord_eq_x {x₁ y₁ x₂ y₂ : ℚ} (h₁ : W.equation x₁ y₁) (h₂ : W.equation x₂ y₂) (hx : x₁ = x₂) :
    y₁ = y₂ ∨ y₁ = - y₂ := by
  unfold WeierstrassCurve.equation at *
  unfold WeierstrassCurve.polynomial at *
  simp[ha₁,ha₂,ha₃] at h₁
  simp[ha₁,ha₂,ha₃] at h₂
  have : y₁ ^ 2 = y₂ ^ 2 := by calc y₁ ^ 2
    _ = y₁ ^ 2 - (x₁ ^ 3 + W.a₄ * x₁ + W.a₆) + (x₁ ^ 3 + W.a₄ * x₁ + W.a₆) := by ring
    _ = 0 + (x₂ ^ 3 + W.a₄ * x₂ + W.a₆) := by rw[h₁, hx]
    _ = y₂ ^ 2 - (x₂ ^ 3 + W.a₄ * x₂ + W.a₆) + (x₂ ^ 3 + W.a₄ * x₂ + W.a₆) := by rw[h₂]
    _ = y₂ ^ 2 := by ring
  exact eq_or_eq_neg_of_sq_eq_sq y₁ y₂ this

lemma point_of_eq_x {x₁ y₁ x₂ y₂} (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂) (hx : x₁ = x₂) :
    Point.some h₁ = Point.some h₂ ∨ Point.some h₁ = -Point.some h₂ := by
  rcases point_coord_eq_x ha₁ ha₂ ha₃ h₁.1 h₂.1 hx with h | h
  · left; subst h; subst hx; rfl
  · right; subst h; subst hx; rw [Point.neg_some]; simp
    rw [ha₁, ha₃]; simp

lemma WeierstrassCurve.int_equation {x y} (h : W.equation x y) :
    y.num ^ 2 = x.num ^ 3 + W.a₄.num * x.num * (x.den : ℤ) ^ 2 + W.a₆.num * (y.den : ℤ) ^ 2 := by
  obtain ⟨d, hx, hy⟩ := point_den_sq_cb ha₁ ha₂ ha₃ ha₄ ha₆ h
  unfold WeierstrassCurve.equation at h
  unfold WeierstrassCurve.polynomial at h
  simp[ha₁, ha₂, ha₃] at h
  rw [sub_eq_zero] at h
  rw [← Rat.num_div_den y, ← Rat.num_div_den x, Rat.eq_num_of_isInt ha₄, Rat.eq_num_of_isInt ha₆] at h
  have h1 : (y.den : ℚ) ^ 2 ≠ 0 := by norm_num; exact y.den_nz
  have h2 : (x.den : ℚ) ≠ 0 := by norm_num; exact x.den_nz
  have h3 : (x.den : ℚ) ^ 3 ≠ 0 := by norm_num; exact x.den_nz
  have h4 : (d : ℤ) ^ 8 ≠ 0 := by
    norm_num
    have : d ^ 2 ≠ 0 := by rw [hx]; exact x.den_nz
    exact right_ne_zero_of_mul this
  field_simp at h; norm_cast at h; rw [← hx, ← hy]; rw [← hx, ← hy] at h
  push_cast at h; ring at h
  rw [mul_comm ((d : ℤ) ^ 8), mul_comm ((d : ℤ) ^ 12), mul_comm ((d : ℤ) ^ 14)] at h
  have : (d : ℤ) ^ 12 = (d : ℤ) ^ 4 * (d : ℤ) ^ 8 := by ring
  rw [mul_assoc, mul_comm ((d : ℤ) ^ 12), ← mul_assoc, this, ← mul_assoc, ← add_mul] at h
  have : (d : ℤ) ^ 14 = (d : ℤ) ^ 6 * (d : ℤ) ^ 8 := by ring
  rw [this, ← mul_assoc, ← add_mul, Int.mul_eq_mul_right_iff h4] at h
  push_cast; rw [h]; ring

/-
  The first inequality : ∀ p ∃ C₁ ∀ q : H (p + q) ≤ 2 * H q + C₁
-/
def C_ineq1_num (x y : ℚ) : ℕ := x.den * natAbs x.num + x.den * natAbs x.num * natAbs W.a₄.num + natAbs (x.num ^ 2) +
                                natAbs W.a₄.num * x.den ^ 2 + 2 * x.den * natAbs y.num * (1 + natAbs W.a₄.num + natAbs W.a₆.num) + 2 * natAbs W.a₆.num * x.den ^ 2
def C_ineq1_den (x : ℚ) : ℕ := (natAbs (x.num ^ 2) + x.den ^ 2 + 2 * x.den * natAbs (x.num))
def C_ineq1 (x y : ℚ) : ℕ := @C_ineq1_num W x y + C_ineq1_den x

-- assuming 0 is not involved. Lots of calculating, don't look
lemma Hsum1_xy {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂) :
    H_q (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) ≤ @C_ineq1 W x₁ y₁ * (H_q x₂) ^ 2 := by
  obtain ⟨d₁, hd₁x, hd₁y⟩ := point_den_sq_cb ha₁ ha₂ ha₃ ha₄ ha₆ h₁.1
  obtain ⟨d₂, hd₂x, hd₂y⟩ := point_den_sq_cb ha₁ ha₂ ha₃ ha₄ ha₆ h₂.1
  simp[ha₁, ha₂]
  unfold slope
  rw [if_neg hx, ← Rat.num_div_den x₁, ← Rat.num_div_den x₂, ← Rat.num_div_den y₁, ← Rat.num_div_den y₂]
  rw [← hd₁x, ← hd₁y, ← hd₂x, ← hd₂y]
  -- proofs that the denominators that occur in the calculations are not zero
  -- need to be in context explicitly for simp etc. to work properly
  have hden1 : (x₁.num * (d₂ : ℤ) ^ 2 - x₂.num * (d₁ : ℤ) ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    intro h
    rw [sub_eq_zero, ← Nat.cast_pow, ← Nat.cast_pow, hd₁x, hd₂x] at h
    exact hx <| Rat.eq_iff_mul_eq_mul.2 h
  have hden1₂ : ((x₁.num : ℚ) * (d₂ : ℚ) ^ 2 - (x₂.num : ℚ) * (d₁ : ℚ) ^ 2) ^ 2 ≠ 0 := by
    norm_num; intro h
    have : (x₁.num : ℚ) * (d₂ : ℚ) ^ 2 - (x₂.num : ℚ) * (d₁ : ℚ) ^ 2 =
        (((x₁.num * (d₂ : ℤ) ^ 2 : ℤ) - (x₂.num * (d₁ : ℤ) ^ 2) : ℤ) : ℚ) := by push_cast; rfl
    have silly : ((0 : ℤ) : ℚ) = (0 : ℚ) := rfl
    rw [this, ← silly, Rat.coe_int_inj] at h; rw [h] at hden1; simp at hden1
  have hden2 : (d₁ : ℚ) ^ 2 ≠ 0 := by norm_cast; rw [hd₁x]; exact x₁.den_nz
  have hden3 : (d₁ : ℚ) ^ 3 ≠ 0 := by norm_cast; rw [hd₁y]; exact y₁.den_nz
  have hden4 : (d₂ : ℚ) ^ 2 ≠ 0 := by norm_cast; rw [hd₂x]; exact x₂.den_nz
  have hden5 : (d₂ : ℚ) ^ 3 ≠ 0 := by norm_cast; rw [hd₂y]; exact y₂.den_nz
  have : ((x₁.num : ℚ) / (d₁ : ℚ) ^ 2 - (x₂.num : ℚ) / (d₂ : ℚ) ^ 2) ^ 2 ≠ 0 := by
    field_simp; intro h; rw [mul_comm _ ((x₂.num) : ℚ)] at h; rw [h] at hden1₂; simp at hden1₂
  have hden7 : ((d₁ : ℚ) ^ 3 * (d₂ : ℚ) ^ 3) ^ 2 * ((x₁.num : ℚ) * (d₂ : ℚ) ^ 2 - (d₁ : ℚ) ^ 2 * (x₂.num : ℚ)) ^ 2 ≠ 0 := by
    rw [mul_comm ((d₁ : ℚ) ^ 2) (x₂.num : ℚ)]
    exact mul_ne_zero (pow_ne_zero 2 <| mul_ne_zero hden3 hden5) hden1₂
  have hy₁ : y₁.num ^ 2 = x₁.num ^ 3 + x₁.num * W.a₄.num * (d₁ : ℤ) ^ 4 + W.a₆.num * (d₁ : ℤ) ^ 6 := by
    rw [WeierstrassCurve.int_equation ha₁ ha₂ ha₃ ha₄ ha₆ h₁.1]
    rw [← hd₁x, ← hd₁y]; push_cast; ring
  have hy₂ : y₂.num ^ 2 = x₂.num ^ 3 + x₂.num * W.a₄.num * (d₂ : ℤ) ^ 4 + W.a₆.num * (d₂ : ℤ) ^ 6 := by
    rw [WeierstrassCurve.int_equation ha₁ ha₂ ha₃ ha₄ ha₆ h₂.1]
    rw [← hd₂x, ← hd₂y]; push_cast; ring
  have : (((y₁.num : ℚ) / ((d₁ ^ 3 : ℕ) : ℚ) - (y₂.num : ℚ) / ((d₂ ^ 3 : ℕ) : ℚ)) / ((x₁.num : ℚ) / ((d₁ ^ 2 : ℕ) : ℚ) - (x₂.num : ℚ) / ((d₂ ^ 2 : ℕ) : ℚ))) ^ 2 - (x₁.num : ℚ) / ((d₁ ^ 2 : ℕ) : ℚ) - (x₂.num : ℚ) / ((d₂ ^ 2 : ℕ) : ℚ) =
      ((((x₁.num * x₂.num + W.a₄.num * (d₁ : ℤ) ^ 2 * (d₂ : ℤ) ^ 2) * (x₁.num * (d₂ : ℤ) ^ 2 + x₂.num * (d₁ : ℤ) ^ 2) + (2 : ℤ) * W.a₆.num * (d₁ : ℤ) ^ 4 * (d₂ : ℤ) ^ 4 - (2 : ℤ) * y₁.num * y₂.num * (d₁ : ℤ) * (d₂ : ℤ)) : ℤ) : ℚ) / (((x₁.num * (d₂ : ℤ) ^ 2 - x₂.num * (d₁ : ℤ) ^ 2) ^ 2 : ℤ) : ℚ) := by
    norm_num; field_simp; norm_cast; push_cast; ring; rw [hy₁, hy₂]; ring
  rw [this]
  apply le_trans (Hq_le_frac hden1)
  rw [hd₁x, hd₂x, hd₁y, Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
  unfold H_q; unfold H_coord
  rw [if_neg x₂.den_nz, x₂.reduced, Nat.div_one, ← hd₂x, Nat.max_sq]
  ring
  have : d₁ ^ 4 = (d₁ ^ 2) ^ 2 := by rw [← Nat.pow_mul]
  have hd₂ : d₂ ^ 4 = (d₂ ^ 2) ^ 2 := by rw [← Nat.pow_mul]
  apply max_le
  · trans natAbs (x₁.num * x₂.num ^ 2 * (d₁ : ℤ) ^ 2) + natAbs (x₁.num * W.a₄.num * (d₁ : ℤ) ^ 2 * (d₂ : ℤ) ^ 4) +
      natAbs (x₁.num ^ 2 * x₂.num * (d₂ : ℤ) ^ 2) + natAbs (x₂.num * W.a₄.num * (d₁ : ℤ) ^ 4 * (d₂ : ℤ) ^  2) +
      natAbs ((d₁ : ℤ) * (d₂ : ℤ) * y₁.num * y₂.num * 2) + natAbs ((d₁ : ℤ) ^ 4 * (d₂ : ℤ) ^ 4 * W.a₆.num * 2)
    apply le_trans (natAbs_add_le _ _); apply add_le_add_right
    rw [← add_sub_assoc]
    apply le_trans (natAbs_sub_le _ _); apply add_le_add_right
    apply le_trans (natAbs_add_le _ _); apply add_le_add_right
    apply le_trans (natAbs_add_le _ _); apply add_le_add_right
    apply le_trans (natAbs_add_le _ _); apply add_le_add_right
    exact le_of_eq rfl
    repeat rw [natAbs_mul]; norm_cast;
    rw [this, hd₁x]
    have hn : natAbs y₂.num * d₂ ≤ (1 + natAbs W.a₄.num + natAbs W.a₆.num) * (max (natAbs x₂.num) (d₂ ^ 2)) ^ 2 := by
      apply Nat.le_of_sq_le; rw [Nat.mul_pow, Nat.mul_pow]; trans (1 + natAbs W.a₄.num + natAbs W.a₆.num) * (max (natAbs x₂.num) (d₂ ^ 2)) ^ 4
      swap; rw [← Nat.pow_mul]; norm_num; apply Nat.mul_le_mul_right; exact @Nat.le_sq (1 + natAbs W.a₄.num + natAbs W.a₆.num)
      have : y₂ ^ 2 = x₂ ^ 3 + W.a₄ * x₂ + W.a₆ := by
        have : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ = x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆ := (equation_iff W x₂ y₂).1 h₂.1
        rw [ha₁, ha₂, ha₃] at this; ring at this; ring; exact this
      have : y₂.num ^ 2 = x₂.num ^ 3 + W.a₄.num * x₂.num * (d₂ : ℤ) ^ 4 + W.a₆.num * (d₂ : ℤ) ^ 6 := by
        apply (Rat.coe_int_inj _ _).1
        push_cast
        have hd : (d₂ : ℚ) ^ 6 ≠ 0 := by
          intro h; norm_cast at h
          rw [pow_eq_zero h] at hd₂x; simp at hd₂x
          exact x₂.den_nz hd₂x.symm
        apply (div_left_inj' hd).1
        have temp : 6 = 3 * 2 := by norm_num
        rw [temp, pow_mul, ← div_pow, ← pow_mul, ← temp, _root_.add_div, _root_.add_div, mul_div_assoc (W.a₆.num : ℚ)]
        rw [div_self hd, mul_one, ← Nat.cast_pow d₂ 3, hd₂y, Rat.num_div_den, ← Rat.eq_num_of_isInt ha₄, ← Rat.eq_num_of_isInt ha₆]
        have temp : 6 = 2 * 3 := by norm_num
        rw [temp, pow_mul, ← div_pow, ← pow_mul, ← temp, ← Nat.cast_pow d₂ 2, hd₂x, Rat.num_div_den, this]
        simp; rw [mul_assoc, mul_div_assoc]; apply congrArg (HMul.hMul W.a₄)
        set t := x₂.num with temp
        rw [← Rat.num_div_den x₂, temp, ← hd₂x]; field_simp
        ring
      have : natAbs y₂.num ^ 2 ≤ (1 + natAbs W.a₄.num + natAbs W.a₆.num) * max (natAbs x₂.num) (d₂ ^ 2) ^ 3 := by
        rw [← natAbs_pow, this]; apply le_trans (natAbs_add_le _ _)
        apply le_trans (Nat.add_le_add_right (natAbs_add_le _ _) _)
        repeat rw [natAbs_mul]
        ring; rw [add_comm _ (max (natAbs x₂.num) (d₂ ^ 2) ^ 3), ← add_assoc]
        apply Nat.add_le_add; apply Nat.add_le_add
        · rw [max_pow, natAbs_pow x₂.num 3]; exact Nat.le_max_left (natAbs x₂.num ^ 3) ((d₂ ^ 2) ^ 3)
        · rw [mul_assoc]; apply Nat.mul_le_mul_left
          have : 3 = Nat.succ 2 := rfl
          rw [this, Nat.pow_succ _ 2, mul_comm _ (max (natAbs x₂.num) (d₂ ^ 2))]
          apply Nat.mul_le_mul (le_max_left (natAbs x₂.num) (d₂ ^ 2))
          rw [max_sq, ← hd₂, natAbs_pow (d₂ : ℤ) 4]; simp
        · apply Nat.mul_le_mul_left
          rw [natAbs_pow _ 6]; simp
          rw [max_pow, ← Nat.pow_mul]; simp; right; norm_num
      apply le_trans <| mul_le_mul_right (d₂ ^ 2) this
      rw [Nat.pow_succ (max (natAbs x₂.num) (d₂ ^ 2)) 3, ← mul_assoc]
      apply Nat.mul_le_mul_left; exact le_max_right (natAbs x₂.num) (d₂ ^ 2)
    have hi1 : natAbs x₁.num * natAbs (x₂.num ^ 2) * x₁.den ≤ x₁.den * natAbs x₁.num * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      rw [mul_comm _ x₁.den, ← mul_assoc, natAbs_pow x₂.num 2]
      exact Nat.mul_le_mul_left (x₁.den * natAbs x₁.num) <| le_max_left (natAbs x₂.num ^ 2) (d₂ ^ 4)
    have hi2 : natAbs x₁.num * natAbs W.a₄.num * x₁.den * d₂ ^ 4 ≤ x₁.den * natAbs x₁.num * natAbs W.a₄.num * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      rw [mul_comm _ x₁.den, ← mul_assoc]; apply Nat.mul_le_mul_left; exact le_max_right (natAbs x₂.num ^ 2) (d₂ ^ 4)
    have hi3 : natAbs (x₁.num ^ 2) * natAbs x₂.num * d₂ ^ 2 ≤ natAbs (x₁.num ^ 2) * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      rw [mul_assoc]; apply Nat.mul_le_mul_left; rw [hd₂, ← max_sq, Nat.pow_two (max (natAbs x₂.num) (d₂ ^ 2))]
      apply Nat.mul_le_mul; exact le_max_left (natAbs x₂.num) (d₂ ^ 2); exact le_max_right (natAbs x₂.num) (d₂ ^ 2)
    have hi4 : natAbs x₂.num * natAbs W.a₄.num * x₁.den ^ 2 * d₂ ^ 2 ≤ natAbs W.a₄.num * x₁.den ^ 2 * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      rw [mul_assoc (natAbs x₂.num), mul_assoc, mul_comm, mul_assoc]; apply Nat.mul_le_mul_left
      rw [hd₂, ← max_sq, Nat.pow_two (max (natAbs x₂.num) (d₂ ^ 2))]; apply Nat.mul_le_mul
      exact le_max_right (natAbs x₂.num) (d₂ ^ 2); exact le_max_left (natAbs x₂.num) (d₂ ^ 2)
    have hi5 : d₁ * d₂ * natAbs y₁.num * natAbs y₂.num * 2 ≤ 2 * x₁.den * natAbs y₁.num * (1 + natAbs W.a₄.num + natAbs W.a₆.num) * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      rw [mul_comm _ 2, mul_assoc 2, mul_assoc 2, mul_assoc 2]; apply Nat.mul_le_mul_left
      rw [mul_comm _ (natAbs y₁.num), mul_assoc, mul_comm _ (natAbs y₁.num), mul_assoc (natAbs y₁.num), mul_assoc (natAbs y₁.num)]
      apply Nat.mul_le_mul_left; rw [mul_assoc, mul_assoc]; apply Nat.mul_le_mul
      · rw [← hd₁x]; exact @Nat.le_sq d₁
      · rw [mul_comm]; apply le_trans hn; apply Nat.mul_le_mul_left; apply le_of_eq
        rw [max_sq, ← hd₂]
    have hi6 : x₁.den ^ 2 * d₂ ^ 4 * natAbs W.a₆.num * 2 ≤ 2 * natAbs W.a₆.num * x₁.den ^ 2 * max (natAbs x₂.num ^ 2) (d₂ ^ 4) := by
      ring; apply Nat.mul_le_mul_right; rw [mul_assoc, mul_assoc]; apply Nat.mul_le_mul_left
      rw [mul_comm]; apply Nat.mul_le_mul_left; exact le_max_right (natAbs x₂.num ^ 2) (d₂ ^ 4)
    trans @C_ineq1_num W x₁ y₁ * max (natAbs x₂.num ^ 2) (d₂ ^ 4)
    · unfold C_ineq1_num; rw [add_mul]; apply Nat.add_le_add _ hi6
      rw [add_mul]; apply Nat.add_le_add _ hi5
      rw [add_mul]; apply Nat.add_le_add _ hi4
      rw [add_mul]; apply Nat.add_le_add _ hi3
      rw [add_mul]; apply Nat.add_le_add _ hi2; exact hi1
    · apply Nat.mul_le_mul_right; unfold C_ineq1; exact Nat.le_add_right (C_ineq1_num x₁ y₁) (C_ineq1_den x₁)
  · apply le_trans (natAbs_add_le _ _); apply le_trans (add_le_add_right (natAbs_add_le _ _) _)
    rw [natAbs_neg]; repeat rw [natAbs_mul]; norm_cast;
    rw [this, hd₁x]
    calc natAbs x₁.num * natAbs x₂.num * x₁.den * d₂ ^ 2 * 2 + natAbs (x₁.num ^ 2) * d₂ ^ 4 + natAbs (x₂.num ^ 2) * x₁.den ^ 2
      _ = natAbs (x₁.num ^ 2) * d₂ ^ 4 + x₁.den ^ 2 * natAbs (x₂.num ^ 2) + 2 * x₁.den * natAbs x₁.num * natAbs x₂.num * d₂ ^ 2 := by ring
      _ ≤ natAbs (x₁.num ^ 2) * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) + x₁.den ^ 2 * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) + 2 * x₁.den * natAbs x₁.num * (max (natAbs x₂.num) (d₂ ^ 2)) * (max (natAbs x₂.num) (d₂ ^ 2)) := ?_
      _ = natAbs (x₁.num ^ 2) * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) + x₁.den ^ 2 * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) + 2 * x₁.den * natAbs x₁.num * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) :=
        by rw [mul_assoc _ (max (natAbs x₂.num) (d₂ ^ 2)) (max (natAbs x₂.num) (d₂ ^ 2)), ← Nat.pow_two (max (natAbs x₂.num) (d₂ ^ 2)), Nat.max_sq, ← Nat.pow_mul]
      _ = (natAbs (x₁.num ^ 2) + x₁.den ^ 2 + 2 * x₁.den * natAbs x₁.num) * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) := by ring
      _ ≤ (@C_ineq1_num W x₁ y₁ + (natAbs (x₁.num ^ 2) + x₁.den ^ 2 + 2 * x₁.den * natAbs x₁.num)) * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) := by
        apply Nat.mul_le_mul_right (max (natAbs x₂.num ^ 2) (d₂ ^ 4)); exact Nat.le_add_left (natAbs (x₁.num ^ 2) + x₁.den ^ 2 + 2 * x₁.den * natAbs x₁.num) (@C_ineq1_num W x₁ y₁)
      _ = @C_ineq1 W x₁ y₁ * (max (natAbs x₂.num ^ 2) (d₂ ^ 4)) := by unfold C_ineq1; unfold C_ineq1_den; rfl
    apply Nat.add_le_add; apply Nat.add_le_add;
    exact Nat.mul_le_mul_left (natAbs (x₁.num ^ 2)) (le_max_right (natAbs x₂.num ^ 2) (d₂ ^ 4))
    apply Nat.mul_le_mul_left (x₁.den ^ 2); simp; left; exact le_of_eq (natAbs_pow x₂.num 2)
    rw [mul_assoc, mul_assoc (2 * x₁.den * natAbs x₁.num)]
    apply Nat.mul_le_mul_left (2 * x₁.den * natAbs x₁.num)
    exact Nat.mul_le_mul (le_max_left (natAbs x₂.num) (d₂ ^ 2)) (le_max_right (natAbs x₂.num) (d₂ ^ 2))

theorem height_ineq1 (p : Point W) : ∃ C > 0, ∀ q : Point W, H (p + q) ≤ C * (H q) ^ 2 := by
  rcases p with h | @⟨x,y,h⟩
  · use 1
    constructor; norm_num
    intro q; rw [one_mul, Point.zero_def, zero_add]
    calc H q
      _ = H q * 1 := (mul_one (H q)).symm
      _ ≤ H q * H q := Nat.mul_le_mul_left (H q) (H_pos q)
      _ = H q ^ 2 := (Nat.pow_two (H q)).symm
  · use max (@C_ineq1 W x y) <| max (H (Point.some h)) (H (2 • (Point.some h)))
    constructor
    · apply lt_of_lt_of_le (H_pos (Point.some h))
      exact le_trans (le_max_left (H (Point.some h)) (H (2 • (Point.some h)))) <| le_max_right (@C_ineq1 W x y) <|
          max (H (Point.some h)) (H (2 • (Point.some h)))
    intro q
    rcases q with hq | @⟨x₁,y₁,h'⟩
    · rw [Point.zero_def]; simp
    by_cases hx : x = x₁
    · rcases point_of_eq_x ha₁ ha₂ ha₃ h h' hx with heq | hne
      · rw [← heq]; trans max (@C_ineq1 W x y) (max (H (Point.some h)) (H (2 • (Point.some h))))
        simp; right; right; rfl
        calc max (@C_ineq1 W x y) (max (H (Point.some h)) (H (2 • (Point.some h))))
          _ = max (@C_ineq1 W x y) (max (H (Point.some h)) (H (2 • (Point.some h)))) * 1 := by rw [mul_one]
          _ ≤ max (@C_ineq1 W x y) (max (H (Point.some h)) (H (2 • (Point.some h)))) * H (Point.some h) ^ 2 :=
            Nat.mul_le_mul_left (max (@C_ineq1 W x y) (max (H (Point.some h)) (H (2 • (Point.some h))))) <|
                one_le_pow 2 (H (Point.some h)) <| H_pos (Point.some h)
      · rw [hne, add_left_neg, H_zero]
        calc 1
          _ ≤ 1 * H (Point.some h') := by rw [one_mul]; exact H_pos (Point.some h')
          _ ≤ H (Point.some h') * H (Point.some h') := Nat.mul_le_mul_right (H (Point.some h')) <| H_pos (Point.some h')
          _ = 1 * H (Point.some h') ^ 2 := by ring
          _ ≤ max (@C_ineq1 W x y) (max (H (-Point.some h')) (H (2 • (-Point.some h')))) * H (Point.some h') ^ 2 :=
            Nat.mul_le_mul_right (H (Point.some h') ^ 2) <| ?_
        apply le_max_of_le_right; apply le_max_of_le_left
        exact H_pos (-Point.some h')
    · rw [Point.some_add_some_of_X_ne hx, Hxy_eq_Hx]
      apply le_trans (Hsum1_xy ha₁ ha₂ ha₃ ha₄ ha₆ hx h h')
      rw [Hxy_eq_Hx h']
      apply Nat.mul_le_mul_right (H_q x₁ ^ 2)
      apply le_max_of_le_left
      rfl


/-
  The third inequality, ∀ c : |{p | H p < c}| < ∞
  We reduce the finiteness via the maps
    f : p ↦ x,y
    g : x,y ↦ x
    h : p/q ↦ p,q
  loosing at most a finite summand or a finite factor at each step
-/
def f (W : WeierstrassCurve ℚ) : W.Point → (ℚ × ℚ) × Fin 2
  | 0 => ((0,0),0)
  | @Point.some _ _ _ x y _ => ((x,y),1)

lemma f_inj : Function.Injective (f W) := by
  intro a b h
  rcases a with ha | @⟨x,y,ha⟩ <;> rcases b with hb | @⟨z,w,hb⟩
  · rfl
  · simp; unfold f at h; simp at h
  · simp; unfold f at h; simp at h
  · simp; unfold f at h; simp at h; exact h

lemma f_range : Set.range (f W) = insert ((0,0),0) {z | z.2 = 1 ∧ W.nonsingular z.1.1 z.1.2} := by
  ext z; constructor
  · intro h
    obtain ⟨p, hp⟩ := h
    rcases p with h | @⟨x,y,h⟩
    left; unfold f at hp; simp at hp; exact hp.symm
    right; unfold f at hp; simp at hp; simp; constructor
    exact (congrArg Prod.snd hp).symm
    rw [← congrArg Prod.fst (congrArg Prod.fst hp), ← congrArg Prod.snd (congrArg Prod.fst hp)]
    exact h
  · intro h; simp at h
    rcases h with h | h
    use 0; unfold f; simp; rw [h]
    use Point.some h.2; unfold f; simp
    exact Prod.ext rfl h.1.symm

lemma height_f {p : W.Point} (hp : p ≠ 0) : H p = H_q ((f W) p).1.1 := by
  rcases p with h | @⟨x,y,h⟩
  by_contra; exact hp rfl
  unfold f; simp; exact Hxy_eq_Hx h

lemma f_range_bound {c : ℕ} (hc : 0 < c) : (f W) '' {p : Point W | H p ≤ c} = insert ((0,0),0) {z | z.2 = 1 ∧ W.nonsingular z.1.1 z.1.2 ∧ H_q z.1.1 ≤ c} := by
  ext z; constructor
  · intro h
    obtain ⟨p, h⟩ := h; simp; rcases p with hp | @⟨x,y,hp⟩
    · left; unfold f at h; simp at h; exact h.2.symm
    right; constructor; unfold f at h; simp at h; exact (congrArg Prod.snd h.2).symm
    constructor; unfold f at h; simp at h
    rw [← congrArg Prod.fst (congrArg Prod.fst h.2), ← congrArg Prod.snd (congrArg Prod.fst h.2)]
    exact hp
    simp at h; rw [← h.2, ← height_f (by simp)]
    exact h.1
  · intro h; simp at h
    rcases h with h | h
    · use 0; unfold f; simp; rw [h]; exact ⟨hc, rfl⟩
    use Point.some h.2.1
    have hp : f W (Point.some h.2.1) = z := by
      unfold f; simp; exact Prod.ext rfl h.1.symm
    constructor; simp; rw [height_f (by simp), hp]; exact h.2.2
    exact hp

def g : (ℚ × ℚ) × Fin 2 → ℚ × Fin 2 := fun ((x,y),_) ↦ if 0 ≤ y then (x,1) else (x,0)

lemma g_inj (c : ℕ) : Set.InjOn g {z | z.2 = 1 ∧ W.nonsingular z.1.1 z.1.2 ∧ H_q z.1.1 ≤ c} := by
  intro x hx y hy h; simp at *
  apply Prod.ext
  · unfold g at h;
    by_cases hx2 : 0 ≤ x.1.2 <;> by_cases hy2 : 0 ≤ y.1.2
    · simp at h; rw [if_pos hx2, if_pos hy2] at h
      have : x.1.1 = y.1.1 := by
        have : (x.1.1, 1).1 = (y.1.1, 1).1 := congrArg Prod.fst h
        simp at this; exact this
      apply Prod.ext; exact this
      rcases point_of_eq_x ha₁ ha₂ ha₃ hx.2.1 hy.2.1 this with h | h
      simp at h; exact h.2
      simp[ha₁, ha₃] at h; rw [h.2] at hx2; simp at hx2
      have : y.1.2 = 0 := le_antisymm hx2 hy2
      rw [this]; rw [this] at h; simp at h; rw [h.2]
    · simp at h; rw [if_pos hx2, if_neg hy2] at h; simp at h
    · simp at h; rw [if_neg hx2, if_pos hy2] at h; simp at h
    · simp at h; rw [if_neg hx2, if_neg hy2] at h
      have : x.1.1 = y.1.1 := by
        have : (x.1.1, 0).1 = (y.1.1, 0).1 := congrArg Prod.fst h
        simp at this; exact this
      apply Prod.ext; exact this
      rcases point_of_eq_x ha₁ ha₂ ha₃ hx.2.1 hy.2.1 this with h | h
      simp at h; exact h.2
      simp [ha₁, ha₃] at h; rw [h.2] at hx2; simp at hx2; simp at hy2
      linarith
  · rw [hx.1, hy.1]

lemma g_range_bound (c : ℕ) :  g '' {z | z.2 = 1 ∧ W.nonsingular z.1.1 z.1.2 ∧ H_q z.1.1 ≤ c} ⊆ {r : ℚ | H_q r ≤ c} ×ˢ {0,1} := by
  rintro ⟨r, t⟩ ⟨z, hz⟩
  simp at *; constructor
  · unfold g at hz
    by_cases hy : 0 ≤ z.1.2
    simp at hz; rw [if_pos hy] at hz
    have : (z.1.1, 1).1 = (r, t).1 := congrArg Prod.fst hz.2
    simp at this; rw [this] at hz; exact hz.1.2.2
    simp at hz; rw [if_neg hy] at hz
    have : (z.1.1, 0).1 = (r, t).1 := congrArg Prod.fst hz.2
    simp at this; rw [this] at hz; exact hz.1.2.2
  · by_cases t = 0
    left; exact h
    right; apply Fin.eq_of_val_eq
    have : (t : ℕ) < 2 := t.2
    have ht0 : (t : ℕ) ≠ 0 := fun ht ↦ h (Fin.eq_of_val_eq ht)
    interval_cases (t : ℕ)
    simp at ht0; simp

def h : ℚ → ℤ × ℕ := fun r ↦ (r.num, r.den)

lemma h_inj : Function.Injective h := by
  intro x y hxy
  unfold h at hxy
  ext
  have : (x.num, x.den).1 = (y.num, y.den).1 := congrArg Prod.fst hxy
  simp at this; exact this
  have : (x.num, x.den).2 = (y.num, y.den).2 := congrArg Prod.snd hxy
  simp at this; exact this

lemma h_range_bound (c : ℕ) : h '' {r : ℚ | H_q r ≤ c} ⊆ {p : ℤ | natAbs p ≤ c} ×ˢ {q : ℕ | q ≤ c} := by
  rintro ⟨x,y⟩ ⟨r, hr⟩
  simp
  unfold h at hr; simp at hr
  rw [← hr.2.1, ← hr.2.2]
  unfold H_q at hr; unfold H_coord at hr; rw [if_neg r.den_nz, r.reduced, Nat.div_one] at hr
  exact ⟨le_trans (le_max_left (natAbs r.num) r.den) hr.1, le_trans (le_max_right (natAbs r.num) r.den) hr.1⟩

def i (c : ℕ) : ℤ → ℕ := fun n ↦ if 0 ≤ n then natAbs n else c + natAbs n

lemma i_inj (c : ℕ) : Set.InjOn (i c) {p | natAbs p ≤ c} := by
  intro x hx y hy hxy
  unfold i at hxy; simp at hx; simp at hy
  by_cases hx0 : 0 ≤ x <;> by_cases hy0 : 0 ≤ y
  · rw [if_pos hx0, if_pos hy0] at hxy
    rw [eq_natAbs_of_zero_le hx0, eq_natAbs_of_zero_le hy0, hxy]
  · rw [if_pos hx0, if_neg hy0] at hxy
    rw [hxy] at hx; simp at hy0
    linarith [natAbs_eq_zero.1 (Nat.add_le_self hx)]
  · rw [if_neg hx0, if_pos hy0] at hxy
    rw [← hxy] at hy; simp at hx0
    linarith [natAbs_eq_zero.1 (Nat.add_le_self hy)]
  · rw [if_neg hx0, if_neg hy0] at hxy
    simp at hxy; simp at hx0; simp at hy0
    rcases Int.natAbs_eq_natAbs_iff.1 hxy with he | hn
    exact he; linarith

lemma i_range (c : ℕ) : i c '' {p | natAbs p ≤ c} = {n : ℕ | n ≤ 2 * c} := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, hy, hx⟩ := hx
    simp; simp at hy; unfold i at hx
    by_cases h0 : 0 ≤ y
    rw [if_pos h0] at hx; rw [hx] at hy
    exact Nat.le_trans hy (by linarith)
    rw [if_neg h0] at hx; rw [← hx]; simp[two_mul]; exact hy
  · simp; simp at hx
    by_cases hc : x ≤ c
    use (x : ℤ); constructor
    simp; exact hc; unfold i; rw [if_pos (ofNat_nonneg x)]; simp
    use (c : ℤ) - (x : ℤ); simp at hc; constructor
    rcases Int.natAbs_eq ((c : ℤ) - (x : ℤ)) with hp | hn
    exfalso
    have hi1 : (c : ℤ) - (x : ℤ) < 0 := by linarith
    have hi2 : 0 ≤ (natAbs ((c : ℤ) - (x : ℤ)) : ℤ) := ofNat_nonneg (natAbs ((c : ℤ) - (x : ℤ)))
    linarith
    have : -((c : ℤ) - (x : ℤ)) = (natAbs ((c : ℤ) - (x : ℤ)) : ℤ) := Int.neg_eq_comm.mp (id hn.symm)
    apply ofNat_le.1; rw [← this]; linarith
    unfold i; rw [if_neg (by linarith)]
    rcases Int.natAbs_eq ((c : ℤ) - (x : ℤ)) with hp | hn
    exfalso
    have hi1 : (c : ℤ) - (x : ℤ) < 0 := by linarith
    have hi2 : 0 ≤ (natAbs ((c : ℤ) - (x : ℤ)) : ℤ) := ofNat_nonneg (natAbs ((c : ℤ) - (x : ℤ)))
    linarith
    have : -((c : ℤ) - (x : ℤ)) = (natAbs ((c : ℤ) - (x : ℤ)) : ℤ) := Int.neg_eq_comm.mp (id hn.symm)
    apply ofNat_inj.1
    have s : ↑(c + natAbs ((c : ℤ) - (x : ℤ))) = (c : ℤ) + (natAbs ((c : ℤ) - (x : ℤ)) : ℤ) := rfl
    rw [s, ← this]; simp

lemma g_range_fin (c : ℕ) : Set.Finite {r : ℚ | H_q r ≤ c} := by
  apply Set.Finite.of_finite_image _ <| Function.Injective.injOn h_inj {r : ℚ | H_q r ≤ c}
  apply Set.Finite.subset _ (h_range_bound c)
  apply Set.Finite.prod _ (Set.finite_le_nat c)
  apply Set.Finite.of_finite_image _ (i_inj c)
  rw [i_range]
  exact Set.finite_le_nat (2 * c)

lemma f_range_fin (c : ℕ) : Set.Finite ({z | z.2 = 1 ∧ W.nonsingular z.1.1 z.1.2 ∧ H_q z.1.1 ≤ c} : Set ((ℚ × ℚ) × Fin 2)) := by
  apply Set.Finite.of_finite_image _ (g_inj ha₁ ha₂ ha₃ c)
  apply Set.Finite.subset _ (g_range_bound c)
  apply Set.Finite.prod (g_range_fin c)
  simp

theorem height_finite : ∀ c : ℝ, Set.Finite {p : W.Point | H p ≤ c} := by
  have : ∀ c : ℕ, Set.Finite {p : W.Point | H p ≤ c} := by
    intro c
    by_cases h0 : 0 < c
    · apply Set.Finite.of_finite_image _ <| Function.Injective.injOn f_inj {p : W.Point | H p ≤ c}
      rw [f_range_bound h0]; apply Set.Finite.insert
      exact f_range_fin ha₁ ha₂ ha₃ c
    · simp at h0
      have : {p : W.Point | H p ≤ c} = ∅ := by
        ext p; constructor <;> simp; intro h'; rw [h0] at h'
        exact not_le_of_gt (H_pos p) h'
      rw [this]; exact Set.finite_empty
  intro c
  apply Set.Finite.subset (this (ceil c))
  intro p hp; simp at *
  rw [Nat.eq_add_of_sub_eq (H_pos p) rfl]
  apply Nat.add_one_le_ceil_iff.2; apply lt_of_lt_of_le _ hp
  exact Nat.cast_lt.mpr <| Nat.sub_lt (H_pos p) (by linarith)
