import LeanCourse.Common
/-
  This file contains the descent argument to finish the proof of the
  Mordell-Weil theorem from the weak version and the theory of heights.
  Reference: J. Silverman, Arithmetic of Elliptic Curves, VIII.3
-/

/-
  Subgroups and quotients of the form mA, m ∈ ℕ
-/
section NMulSubgroups
open AddCommGroup
variable {A : Type*} [AddCommGroup A]

def mul_m (m : ℕ) : A →+ A where
  toFun := fun a ↦ m • a
  map_zero' := by simp
  map_add' := by simp

def m_multiples (m : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A where
  carrier := Set.range (mul_m m)
  add_mem' := by
    rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  zero_mem' := ⟨0, by exact AddMonoidHom.map_zero (mul_m m)⟩
  neg_mem' := by
    rintro _ ⟨a, ha⟩
    use -a
    simp
    exact ha

infixl:70 " ⬝ " => m_multiples
example : AddSubgroup A := 3 ⬝ A

lemma temp (a b : A) (m : ℕ) (h : QuotientAddGroup.mk' (m ⬝ A) a = QuotientAddGroup.mk' (m ⬝ A) b) :
    ∃ c : A, a = b + m • c := by
  rw [QuotientAddGroup.mk'_eq_mk'] at h
  obtain ⟨z, ⟨c, hc⟩, hz⟩ := h
  use -c
  rw [← hz, ← hc, smul_neg]
  have : a + m • c = a + (mul_m m).toFun c := rfl
  exact eq_add_neg_of_add_eq this

end NMulSubgroups

noncomputable section HeightFunctions
open Real Classical Function BigOperators
variable {A : Type*} [AddCommGroup A]

/-
  Some inequalities of real numbers for the proof
  These should be in mathlib, but I couldn't find them
-/
lemma geo_series (r : ℝ) (n : ℕ) (h : r ≠ 1) :
    ∑ i in Finset.range n, r ^ i = (1 - r ^ n) / (1 - r) := by
  induction' n with n hn
  · simp
  rw [Finset.sum_range_succ, hn]
  apply (mul_right_inj' (sub_ne_zero.2 h.symm)).1
  rw [mul_div_cancel' _ (sub_ne_zero.2 h.symm), mul_add, mul_div_cancel' _ (sub_ne_zero.2 h.symm)]
  ring

lemma geo_series_le_lim (r : ℝ) (n : ℕ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑ i in Finset.range n, r ^ i ≤ 1 / (1 - r) := by
  rw [geo_series r n (ne_of_lt h1)]
  have : 1 - r > 0 := by linarith
  apply (div_le_div_right this).2
  simp
  exact pow_nonneg h0 n

/-
  right inverse of a surjective functions
-/
def right_inv_of_surj {α β : Type*} {f : α → β} (h : Surjective f) : β → α :=
  fun y : β ↦ Classical.choose (h y)

lemma right_inv_spec {α β : Type*} {f : α → β} (h : Surjective f) :
    RightInverse (right_inv_of_surj h) f :=
  fun y ↦ Classical.choose_spec (h y)

/-
  A recursively defined sequence of points that is needed for the next theorem:
  Let Q be a chosen class of representatives of A / m ⬝ A
  p (n - 1) = m • p n + q, q ∈ Q
-/
namespace Descent
def r (m : ℕ) : A → A ⧸ m ⬝ A := QuotientAddGroup.mk' (m ⬝ A)
def s (m : ℕ) : A ⧸ m ⬝ A → A := right_inv_of_surj <| QuotientAddGroup.mk'_surjective (m ⬝ A)

lemma sr_inv (m : ℕ) : (r m) ∘ (s m : A ⧸ m ⬝ A → A) = id := by
  apply Function.RightInverse.id
  exact right_inv_spec <| QuotientAddGroup.mk'_surjective (m ⬝ A)

lemma class_eq_class_rep (m : ℕ) (a : A) : r m a = r m (s m (r m a)) := by
  calc r m a
    _ = (id ∘ r m) a := rfl
    _ = ((r m ∘ s m) ∘ r m) a := by rw [sr_inv m]
    _ = r m (s m (r m a)) := by simp only [comp_apply]

def p (x₀ : A) (m : ℕ) : ℕ → A
  | 0 => x₀
  | n + 1 =>  Classical.choose <| temp (p x₀ m n) (s m (r m (p x₀ m n))) m <| class_eq_class_rep m (p x₀ m n)

lemma p_rec_eq (x₀ : A) (m : ℕ) (n : ℕ) : p x₀ m n = s m (r m (p x₀ m n)) + m • (p x₀ m (n + 1)) := by
  exact Classical.choose_spec <| temp (p x₀ m n) (s m (r m (p x₀ m n))) m <| class_eq_class_rep m (p x₀ m n)

/-
  The main theorem we use to conclude the Mordell-Weil theorem:
  If there is a height function with nice enough properties on a group
  and some quotient is finite, then the group is finitely generated.
-/
theorem fg_of_height_function (H : A → ℝ)
    (h1 : ∀ a, ∃ c₁ > 0, ∀ b, H (a + b) ≤ 2 * H b + c₁)
    (m : ℕ) (hm : m ≥ 2)
    (h2 : ∃ c₂ > 0, ∀ a : A, H (m • a) ≥ (m : ℝ) ^ 2 * H a - c₂)
    (h3 : ∀ c : ℝ, Set.Finite {a : A | H a ≤ c})
    (h4 : Finite (A ⧸ m ⬝ A)) : AddGroup.FG A := by
  haveI := Fintype.ofFinite (A ⧸ m ⬝ A)
  let s : A ⧸ m ⬝ A → A := s m
  let Q : Finset A := Set.Finite.toFinset <| Set.finite_range s
  let map_c₁ : A → ℝ := fun a ↦ Classical.choose (h1 a)
  let c₁Q : Finset ℝ := Finset.image (map_c₁ ∘ (fun a ↦ -a)) Q
  let c₁ : ℝ := Finset.max' c₁Q <| Finset.Nonempty.image ⟨s 0, by simp⟩ (map_c₁ ∘ (fun a ↦ -a))
  have h1₀ : c₁ > 0 := by
    let q : Q := ⟨s 0, by simp⟩
    have i1 : 0 < map_c₁ (-q) := (Classical.choose_spec (h1 (-q))).1
    have i2 : map_c₁ (-q) ≤ c₁ := Finset.le_max' c₁Q (map_c₁ (-q)) <| Finset.mem_image.2 ⟨q, ⟨by simp, rfl⟩⟩
    exact lt_of_lt_of_le i1 i2
  have hc₁ : ∀ q ∈ Q, ∀ a : A, H (a - q) ≤ 2 * H a + c₁ := by
    intro q hq a
    rw [← neg_add_eq_sub]
    trans 2 * H a + map_c₁ (-q)
    · simp
      exact (Classical.choose_spec (h1 (-q))).2 a
    · exact add_le_add_left (Finset.le_max' c₁Q (map_c₁ (-q)) <| Finset.mem_image.2 ⟨q, ⟨hq, rfl⟩⟩) (2 * H a)
  obtain ⟨c₂, h2₀, h2⟩ := h2
  have hm2 : 2 ^ 2 ≤ (m : ℝ) ^ 2 := sq_le_sq.2 (by rw [abs_eq_self.2 (by norm_num), abs_eq_self.2 (by linarith)]; norm_cast)
  have hm2 : 4 ≤ (m : ℝ) ^ 2 := by norm_num at hm2; exact hm2
  let L : ℝ := 1 + (c₁ + c₂) / 2
  use Q ∪ Set.Finite.toFinset (h3 L)
  ext x; constructor; simp
  intro _
  let P : ℕ → A := p x m
  have : 0 < (m : ℝ) ^ 2 := by norm_cast; apply sq_pos_of_pos; linarith
  have hHP : ∀ n : ℕ, H (P (n + 1)) ≤ (2 * H (P n) + c₁ + c₂) / (m : ℝ) ^ 2 := by
    intro n
    calc H (P (n + 1))
      _ ≤ (H (m • P (n + 1)) + c₂) / (m : ℝ) ^ 2 := by
          rw [le_div_iff this, mul_comm, ← tsub_le_iff_right];
          exact h2 (P (n + 1))
      _ = (H (s (r m (P n)) + m • P (n + 1) - s (r m (P n))) + c₂) / (m : ℝ) ^ 2 := by rw [add_sub_cancel']
      _ = (H (P n - s (r m (P n))) + c₂) / (m : ℝ) ^ 2 := by rw [← p_rec_eq]
      _ ≤ (2 * H (P n) + c₁ + c₂) / (m : ℝ) ^ 2 :=
          (div_le_div_right this).2 <| add_le_add_right (hc₁ (s (r m (P n))) (by simp) (P n)) c₂
  have hHP1 : ∀ n : ℕ, H (P n) ≤ (2 / (m : ℝ) ^ 2) ^ n * H x + (c₁ + c₂) * ∑ i in Finset.range n, (2 : ℝ) ^ i / (m : ℝ) ^ (2 * (i + 1)) := by
    intro n
    induction' n with n h
    · simp; rfl
    calc H (P (n + 1))
      _ ≤ (2 * H (P n) + c₁ + c₂) / (m : ℝ) ^ 2 := hHP n
      _ ≤ (2 * ((2 / (m : ℝ) ^ 2) ^ n * H x + (c₁ + c₂) * ∑ i in Finset.range n, 2 ^ i / (m : ℝ) ^ (2 * (i + 1))) + c₁ + c₂) / (m : ℝ) ^ 2 := by
          apply (div_le_div_right this).2
          apply add_le_add_right
          apply add_le_add_right
          exact (mul_le_mul_left (by norm_num)).2 h
      _ = (2 / (m : ℝ) ^ 2) ^ (n + 1) * H x + (c₁ + c₂) * 2 / (m : ℝ) ^ 2 * (∑ i in Finset.range n, 2 ^ i / (m : ℝ) ^ (2 * (i + 1))) + (c₁ + c₂) / (m : ℝ) ^ 2 := by ring
      _ = (2 / (m : ℝ) ^ 2) ^ (n + 1) * H x + (c₁ + c₂) * (∑ i in Finset.range (n + 1), (2 : ℝ) ^ i / (m : ℝ) ^ (2 * (i + 1))) := by
          have h' : 2 / (m : ℝ) ^ 2 * (∑ i in Finset.range n, 2 ^ i / (m : ℝ) ^ (2 * (i + 1))) + 1 / (m : ℝ) ^ 2
              = ∑ i in Finset.range (n + 1), (2 : ℝ) ^ i / (m : ℝ) ^ (2 * (i + 1)) := by
            rw [Finset.sum_range_succ', Finset.mul_sum]
            field_simp
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [← h']
          ring
  have hHP2 : ∀ n : ℕ, H (P n) ≤ (2 / (m : ℝ) ^ 2) ^ n * (H x) + (c₁ + c₂) / 2 := by
    intro n
    trans (2 / (m : ℝ) ^ 2) ^ n * H x + (c₁ + c₂) * ∑ i in Finset.range n, (2 : ℝ) ^ i / (m : ℝ) ^ (2 * (i + 1))
    · exact hHP1 n
    apply add_le_add_left
    apply (mul_le_mul_left (by linarith : 0 < c₁ + c₂)).2
    have h : ∀ i : ℕ, 2 ^ i / (m : ℝ) ^ (2 * (i + 1)) = 1 / (m : ℝ) ^ 2 * (2 / (m : ℝ) ^ 2) ^ i :=
      fun i ↦ by field_simp; ring
    have h : ∀ i ∈ Finset.range n, 2 ^ i / (m : ℝ) ^ (2 * (i + 1)) = 1 / (m : ℝ) ^ 2 * (2 / (m : ℝ) ^ 2) ^ i :=
      fun i _ ↦ h i
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
    apply (mul_le_mul_left this).1
    rw [← mul_assoc, mul_one_div_cancel (ne_of_lt this).symm, one_mul]
    have h : 2 / (m : ℝ) ^ 2 < 1 := by
      apply (div_lt_iff' this).2
      linarith
    trans 1 / (1 - 2 / (m : ℝ) ^ 2)
    · exact geo_series_le_lim (2 / (m : ℝ) ^ 2) n (le_of_lt (div_pos (by norm_num) this)) h
    field_simp
    apply (mul_le_mul_left this).2
    apply (inv_le_inv (by linarith) (by linarith)).2
    linarith
  have hHlim : ∃ n : ℕ, H (P n) < L := by
    by_cases h0 : H x ≤ 0
    · use 0
      have : H (P 0) = H x := by simp; rfl
      rw [this]
      apply lt_of_le_of_lt h0
      have : 0 < 1 + (c₁ + c₂) / 2 := by linarith
      exact this
    simp at h0
    have h : ∃ n : ℕ, (2 / (m : ℝ) ^ 2) ^ n < 1 / H x := by
      apply exists_pow_lt_of_lt_one (one_div_pos.2 h0)
      apply (div_lt_iff' this).2
      linarith
    obtain ⟨n, hn⟩ := h
    use n
    apply lt_of_le_of_lt (hHP2 n)
    calc (2 / (m : ℝ) ^ 2) ^ n * H x + (c₁ + c₂) / 2
      _ < 1 / H x * H x + (c₁ + c₂) / 2 := add_lt_add_right ((mul_lt_mul_right h0).2 hn) ((c₁ + c₂) / 2)
      _ = 1 + (c₁ + c₂) / 2 := by rw [one_div_mul_cancel (ne_of_lt h0).symm]
      _ = L := rfl
  have hxgen : ∀ n : ℕ, x ∈ AddSubgroup.closure (Q ∪ {P n}) := by
    intro n
    induction' n with n hn
    · apply AddSubgroup.subset_closure
      right; simp; rfl
    have : AddSubgroup.closure (↑Q ∪ {P n}) ≤ AddSubgroup.closure (↑Q ∪ {P (n + 1)}) := by
      apply (AddSubgroup.closure_le (AddSubgroup.closure (↑Q ∪ {P (n + 1)}))).2
      apply Set.union_subset_iff.2; constructor
      · trans ↑Q ∪ {P (n + 1)}; exact Set.subset_union_left ↑Q {P (n + 1)}
        exact AddSubgroup.subset_closure
      · rw [Set.singleton_subset_iff]
        have : P n = s (r m (P n)) + m • P (n + 1) := p_rec_eq x m n
        rw [this]
        apply AddSubgroup.add_mem (AddSubgroup.closure (↑Q ∪ {P (n + 1)}))
        · apply AddSubgroup.subset_closure; left; simp
        · apply AddSubgroup.nsmul_mem (AddSubgroup.closure (↑Q ∪ {P (n + 1)})) _ m
          apply AddSubgroup.subset_closure; right; simp
    exact this hn
  obtain ⟨n, hnL⟩ := hHlim
  specialize hxgen n
  have hc : AddSubgroup.closure (Q ∪ {P n}) ≤ AddSubgroup.closure (Q ∪ Set.Finite.toFinset (h3 L)) := by
    apply AddSubgroup.closure_mono
    gcongr
    simp
    simp at hnL
    exact le_of_lt hnL
  norm_cast at hc
  exact hc hxgen

end Descent
end HeightFunctions
