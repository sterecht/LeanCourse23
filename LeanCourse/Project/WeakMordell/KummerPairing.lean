import LeanCourse.Project.Descent
import LeanCourse.Project.WeakMordell.GaloisReduction
import Mathlib.FieldTheory.Adjoin

set_option maxHeartbeats 500000

open WeierstrassCurve EllipticCurve Descent GalReduction

variable (k : Type*) [Field k] [NumberField k]
         (K : Type*) [Field K] [Algebra k K] [IsAlgClosure k K]
         (E : EllipticCurve k) (m : ℕ) (hm : 2 ≤ m)
         (htor : m_tor (E⟮K⟯) m ≤ (Point.ofBaseChange E.toWeierstrassCurve k K).range)

noncomputable section
theorem Point.div_of_algClosed (p : E⟮k⟯) : ∃ q : E⟮K⟯, m • q = Point.ofBaseChange E.toWeierstrassCurve k K p := by
  sorry

namespace Kummer

def Q : E⟮k⟯ → E⟮K⟯ := fun p ↦ Exists.choose <| Point.div_of_algClosed k K E m p

lemma action_tor {p : E⟮k⟯} (σ : (K ≃ₐ[k] K)) {q : E⟮K⟯} (h : m • q = Point.ofBaseChange E.toWeierstrassCurve k K p) :
    m • (σ • q - q) = 0 := by simp; rw [GalReduction.nsmul_hom_action, h, GalReduction.gal_action_base]; simp

def kummer_fun : E⟮k⟯ × (K ≃ₐ[k] K) → E⟮K⟯ := fun x ↦ x.2 • (Q k K E m x.1) - Q k K E m x.1

lemma kummer_tor (x : E⟮k⟯ × (K ≃ₐ[k] K)) : kummer_fun k K E m x ∈ m_tor (E⟮K⟯) m := by
  unfold m_tor
  simp only [baseChange_toWeierstrassCurve, Nat.isUnit_iff, AddSubgroup.mem_mk, Set.mem_setOf_eq]
  exact action_tor k K E m x.2 <| Exists.choose_spec <| Point.div_of_algClosed k K E m x.1

def kummer₁ : E⟮k⟯ → (K ≃ₐ[k] K) → E⟮K⟯ := fun p σ ↦ kummer_fun k K E m ⟨p, σ⟩

def kummer₂ : (K ≃ₐ[k] K) → E⟮k⟯ → E⟮K⟯ := fun σ p ↦ kummer_fun k K E m ⟨p, σ⟩

lemma kummer₁₂ (p : E⟮k⟯) (σ : (K ≃ₐ[k] K)) : kummer₁ k K E m p σ = kummer₂ k K E m σ p := rfl

lemma kummer₁_tor (p : E⟮k⟯) (σ : (K ≃ₐ[k] K)) : kummer₁ k K E m p σ ∈ m_tor (E⟮K⟯) m :=
  kummer_tor k K E m ⟨p, σ⟩

lemma kummer₂_tor (p : E⟮k⟯) (σ : (K ≃ₐ[k] K)) : kummer₂ k K E m σ p ∈ m_tor (E⟮K⟯) m :=
  kummer_tor k K E m ⟨p, σ⟩

lemma choice_indep {p : E⟮k⟯} {q : E⟮K⟯} (hq : m • q = Point.ofBaseChange E.toWeierstrassCurve k K p) :
    kummer₁ k K E m p = fun σ ↦ σ • q - q := by
  have : Q k K E m p - q ∈ m_tor (E⟮K⟯) m := by
    unfold m_tor; simp; unfold Q
    rw [hq, Exists.choose_spec <| Point.div_of_algClosed k K E m p]; simp
  obtain ⟨t, ht⟩ := htor this
  ext σ; unfold kummer₁; unfold kummer_fun; simp
  have : σ • (Q k K E m p - q) = Q k K E m p - q := by
    rw [← ht, GalReduction.gal_action_base]
  rw [sub_eq_add_neg, GalReduction.action_hom, ← sub_eq_add_neg,
      GalReduction.action_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add] at this
  rw [this]; abel_nf; simp; rw [add_comm, ← sub_eq_add_neg]

lemma add_left (p₁ p₂ : E⟮k⟯) (σ : (K ≃ₐ[k] K)) : kummer_fun k K E m ⟨p₁ + p₂, σ⟩ =
    kummer_fun k K E m ⟨p₁, σ⟩ + kummer_fun k K E m ⟨p₂, σ⟩ := by
  have : kummer_fun k K E m ⟨p₁ + p₂, σ⟩ = σ • (Q k K E m p₁ + Q k K E m p₂) - (Q k K E m p₁ + Q k K E m p₂) := by
    apply congrFun (choice_indep k K E m htor _) σ
    simp; unfold Q
    rw [Exists.choose_spec (Point.div_of_algClosed k K E m p₁), Exists.choose_spec (Point.div_of_algClosed k K E m p₂)]
    rfl
  rw [this]; unfold kummer_fun; simp
  rw [GalReduction.action_hom, add_sub_assoc, sub_add, sub_eq_add_neg, sub_eq_add_neg]
  apply congrArg (HAdd.hAdd _) _
  simp; rw [sub_sub, sub_eq_add_neg]
  apply congrArg (HAdd.hAdd _) _
  simp; rw [add_comm]

lemma mul_right (p : E⟮k⟯) (σ₁ σ₂ : (K ≃ₐ[k] K)) : kummer_fun k K E m ⟨p, σ₁ * σ₂⟩ =
    kummer_fun k K E m ⟨p, σ₁⟩ + kummer_fun k K E m ⟨p, σ₂⟩ := by
  unfold kummer_fun; simp
  have : (σ₁ * σ₂) • Q k K E m p - Q k K E m p = σ₁ • (σ₂ • Q k K E m p - Q k K E m p) + σ₁ • Q k K E m p - Q k K E m p := by
    simp
    rw [sub_eq_add_neg, GalReduction.action_hom, GalReduction.action_neg]
    simp
    exact GalReduction.gal_action_assoc k K E σ₁ σ₂ (Q k K E m p)
  rw [this, add_sub_assoc, add_comm]
  simp
  obtain ⟨q, hq⟩ := htor <| kummer_tor k K E m ⟨p, σ₂⟩
  unfold kummer_fun at hq
  rw [← hq]
  apply GalReduction.gal_action_base

lemma mul_base_change (n : ℕ) (p : E⟮k⟯) : Point.ofBaseChange E.toWeierstrassCurve k K (n • p) = n • (Point.ofBaseChange E.toWeierstrassCurve k K p) := by
  exact AddMonoidHom.map_nsmul (Point.ofBaseChange E.toWeierstrassCurve k K) p n

lemma ker_left (p : E⟮k⟯) : (∀ σ : (K ≃ₐ[k] K), kummer_fun k K E m ⟨p, σ⟩ = 0) ↔ p ∈ m ⬝ E⟮k⟯ := by
  constructor
  · intro h
    have : ∀ σ : (K ≃ₐ[k] K), σ • Q k K E m p = Q k K E m p := by
      intro σ
      specialize h σ
      unfold kummer_fun at h
      simp at h
      rw [sub_eq_zero] at h
      exact h
    obtain ⟨q, hq⟩ := gal_action_fixed_inf k K E (Q k K E m p) this
    unfold Q at hq
    use q
    have : m • Point.ofBaseChange E.toWeierstrassCurve k K q = Point.ofBaseChange E.toWeierstrassCurve k K p := by
      rw [← Exists.choose_spec <| Point.div_of_algClosed k K E m p, hq]
    rw [← AddMonoidHom.map_nsmul (Point.ofBaseChange E.toWeierstrassCurve k K) q m] at this
    exact Point.ofBaseChange_injective E.toWeierstrassCurve k K this
  · rintro ⟨q, hq⟩ σ
    have : kummer₁ k K E m p σ = kummer_fun k K E m ⟨p, σ⟩ := rfl
    have hq' : m • Point.ofBaseChange E.toWeierstrassCurve k K q = Point.ofBaseChange E.toWeierstrassCurve k K p := by
      have : m • q = p := hq
      rw [← AddMonoidHom.map_nsmul (Point.ofBaseChange E.toWeierstrassCurve k K) q m, this]
    rw [← this, choice_indep k K E m htor hq']
    simp
    rw [sub_eq_zero]
    apply GalReduction.gal_action_base

def kummer_1 : E⟮k⟯ →+ Additive (K ≃ₐ[k] K) →+ E⟮K⟯ :=
  AddMonoidHom.mk' (fun p ↦ (AddMonoidHom.mk' (fun σ ↦ kummer_fun k K E m ⟨p, σ⟩) (by
    intro σ₁ σ₂
    simp
    exact mul_right k K E m htor p σ₁ σ₂
  ))) <| by
    intro p q
    simp
    ext σ
    simp
    exact add_left k K E m htor p q σ

def div_points := {p : E⟮K⟯ | m • p ∈ (Point.ofBaseChange E.toWeierstrassCurve k K).range}

def field_of_def : E⟮K⟯ → IntermediateField k K
  | 0 => ⊥
  | @Point.some _ _ _ x y _ => IntermediateField.adjoin k {x, y}


open IntermediateField
lemma field_of_def_spec (p : E⟮K⟯) : p ∈ (Point.ofBaseChange E.toWeierstrassCurve (field_of_def k K E p) K).range := by
  rcases p with h | @⟨x,y,h⟩
  · use 0; simp [Point.zero_def]
  have hx : x ∈ (Subfield.subtype (field_of_def k K E (Point.some h)).toSubfield).range := by
    simp
    unfold field_of_def
    simp
    sorry
  obtain ⟨x', hx⟩ := hx
  have hy : y ∈ (Subfield.subtype (field_of_def k K E (Point.some h)).toSubfield).range := by
    sorry
  obtain ⟨y', hy⟩ := hy
  have h' : (E.baseChange (field_of_def k K E (Point.some h))).toWeierstrassCurve.equation x' y' := by
    unfold WeierstrassCurve.equation
    simp
    unfold WeierstrassCurve.polynomial
    simp
    --apply (@algebraMap.coe_inj _ _ (field_of_def k K E (Point.some h)).toSubfield K _ _).1
    sorry
  use Point.some <| nonsingular (EllipticCurve.baseChange E (↥field_of_def k K E (Point.some h))) h'
  simp
  unfold Point.ofBaseChangeFun
  simp
  constructor
  exact hx
  exact hy

def div_field : IntermediateField k K := sorry

lemma ker_right (σ : (K ≃ₐ[k] K)) : (∀ p : E⟮k⟯, kummer_fun k K E m ⟨p, σ⟩ = 0) ↔ (∀ x : div_field k K, σ x = x) := by
  sorry

def kummer : E⟮k⟯ ⧸ m ⬝ E⟮k⟯ →+ Additive (K ≃ₐ[div_field k K] K) →+ E⟮K⟯ := sorry

theorem weak_mord_iff_div_field_fin : Finite (E⟮k⟯ ⧸ m ⬝ E⟮k⟯) ↔ FiniteDimensional k (div_field k K) := by
  sorry

/-
  I won't be able to prove this. The proof requires Kummer theory and Dirichlet's S-unit-theorem,
  both of which are difficult theorems which are not formalized yet. Just stating the latter
  would require heaps of formalization work on valuations and completions.
-/
theorem div_field_fin : FiniteDimensional k (div_field k K) := by
  sorry

end Kummer
