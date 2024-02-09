import LeanCourse.Project.Descent
import LeanCourse.Project.WeakMordell.GaloisReduction
import Mathlib.FieldTheory.Adjoin

set_option maxHeartbeats 500000

open WeierstrassCurve EllipticCurve Descent GalReduction

universe u
variable (k : Type u) [Field k] [NumberField k]
         (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
         (E : EllipticCurve k) (m : ℕ) (hm : 2 ≤ m)
         (htor : m_tor (E⟮K⟯) m ≤ (Point.ofBaseChange E.toWeierstrassCurve k K).range)

noncomputable section
-- this is a very lengthy calculation that I unfortunately couldn't finish in time
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
    simp; unfold field_of_def; simp; unfold adjoin; simp
    exact Subfield.subset_closure <| Set.mem_insert x _
  obtain ⟨x', hx⟩ := hx
  have hy : y ∈ (Subfield.subtype (field_of_def k K E (Point.some h)).toSubfield).range := by
    simp; unfold field_of_def; simp; unfold adjoin; simp
    exact Subfield.subset_closure <| Set.mem_insert_of_mem x <| Set.mem_insert y _
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

def div_field : IntermediateField k K := Subfield.toIntermediateField (Subfield.closure <| ⋃₀ {field_of_def k K E p | p ∈ div_points k K E m}) <| fun x ↦ by
  apply Subfield.subset_closure
  have : 0 ∈ div_points k K E m := by
    unfold div_points; simp
    use 0; unfold Point.ofBaseChangeFun; simp
  have h : (field_of_def k K E 0).carrier ⊆ ⋃₀ {field_of_def k K E p | p ∈ div_points k K E m} := by
    intro x hx
    apply Set.mem_sUnion.2
    simp
    exact ⟨0, this, hx⟩
  have : algebraMap k K x ∈ field_of_def k K E 0 := by
    unfold field_of_def; simp
    exact IntermediateField.algebraMap_mem ⊥ x
  exact h this

-- More facts from Galois theory. These are not too hard to prove,
-- but the problem is that we don't know yet that the field extension is finite, so we can't use any
-- theorems from mathlib.
def gal_sub : Subgroup (K ≃ₐ[k] K) where
  carrier := {σ : (K ≃ₐ[k] K) | ∀ x ∈ div_field k K E m, σ x = x}
  mul_mem' := by
    intro σ τ hσ hτ
    simp at *
    intro x hx
    rw [hτ x hx, hσ x hx]
  one_mem' := by simp
  inv_mem' := by
    intro σ hσ
    simp at *
    intro x hx
    specialize hσ x hx
    have h : σ⁻¹ (σ x) = σ⁻¹ x := congrArg (↑σ⁻¹) hσ
    have : σ⁻¹ (σ x) = x := by calc
      σ⁻¹ (σ x) = (σ⁻¹ * σ) x := by rfl
      _         = x := by simp
    rw [this] at h
    exact h.symm


instance : Subgroup.Normal (gal_sub k K E m) where
  conj_mem := sorry
lemma gal_quotient : (div_field k K E m ≃ₐ[k] div_field k K E m) ≃* (K ≃ₐ[k] K) ⧸ (gal_sub k K E m) := by sorry
def gal_quotient_map : (div_field k K E m ≃ₐ[k] div_field k K E m) →* (K ≃ₐ[k] K) ⧸ (gal_sub k K E m) := gal_quotient k K E m
instance : IsGalois k (div_field k K E m) := sorry

lemma ker_right (σ : (K ≃ₐ[k] K)) : (∀ p : E⟮k⟯, kummer_fun k K E m ⟨p, σ⟩ = 0) ↔ (σ ∈ gal_sub k K E m) := by
  constructor
  · sorry
  · intro H p
    simp at H
    unfold kummer_fun
    simp
    have : Q k K E m p ∈ div_points k K E m := by
      unfold div_points
      simp
      use p
      exact (Exists.choose_spec <| Point.div_of_algClosed k K E m p).symm
    rcases Q k K E m p with h|@⟨x,y,h⟩
    · simp [Point.zero_def]
      exact action_zero k K E σ
    have hx : x ∈ div_field k K E m := by
      unfold div_field
      apply Subfield.subset_closure
      apply Set.mem_sUnion.2
      use field_of_def k K E (Q k K E m p)
      constructor; simp; use Q k K E m p
      sorry
    have hy : y ∈ div_field k K E m := by sorry
    have hx : σ x = x := H x hx
    have hy : σ y = y := H y hy
    rw [gal_action_some]
    simp
    sorry



def kummer_help (p : E⟮k⟯) : (K ≃ₐ[k] K) ⧸ (gal_sub k K E m) →* Multiplicative (E⟮K⟯) :=
  QuotientGroup.lift (gal_sub k K E m) (AddMonoidHom.toMultiplicative <| kummer_1 k K E m htor p) <| by
    intro σ h
    rw [MonoidHom.mem_ker]
    exact (ker_right k K E m σ).2 h p

def kummer_help₂ (p : E⟮k⟯) : Additive ((K ≃ₐ[k] K) ⧸ (gal_sub k K E m)) →+ (E⟮K⟯) :=
    MonoidHom.toAdditive <| kummer_help k K E m htor p

def kummer : E⟮k⟯ ⧸ m ⬝ E⟮k⟯ →+ Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ E⟮K⟯ :=
  QuotientAddGroup.lift (m ⬝ E⟮k⟯) ({
    toFun := fun p ↦ (kummer_help₂ k K E m htor p).comp (MonoidHom.toAdditive <| (gal_quotient_map k K E m))
    map_zero' := by
      ext σ
      simp
      unfold kummer_help₂
      unfold kummer_help
      simp
      -- there are a lot of casts going on here, with Additive/Multiplicative, and with the subfields.
      -- I can't figure out how to simplify the expression.
      sorry
    map_add' := sorry
  }) <| by
  intro q h
  rw [AddMonoidHom.mem_ker]
  simp
  ext σ
  simp
  sorry

lemma kummer_inj : Function.Injective (kummer k K E m htor) := sorry
lemma kummer_torsion (p : E⟮k⟯ ⧸ m ⬝ E⟮k⟯) (σ : (div_field k K E m ≃ₐ[k] div_field k K E m)) : kummer k K E m htor p σ ∈ m_tor (E⟮K⟯) m := sorry
lemma kummer_range : (kummer k K E m htor).range ≤ {f : (Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ E⟮K⟯) | f.range ≤ (m_tor (E⟮K⟯) m)} := by
  rintro f ⟨p, hp⟩
  simp
  rintro q ⟨σ, hσ⟩
  rw [← hp] at hσ
  rw [← hσ]
  exact kummer_torsion k K E m htor p σ
lemma range₂ : {f : Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ E⟮K⟯ | f.range ≤ (m_tor (E⟮K⟯) m)} ≃ (Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ m_tor (E⟮K⟯) m) := sorry

private def fun_incl : (Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ m_tor (E⟮K⟯) m) → ((div_field k K E m ≃ₐ[k] div_field k K E m) → m_tor (E⟮K⟯) m) :=
    fun f ↦ f
lemma fun_incl_inj : Function.Injective (fun_incl k K E m) := by
  intro f g hfg
  unfold Kummer.fun_incl at hfg
  exact AddMonoidHom.ext (congrFun hfg)


theorem weak_mord_of_div_field_fin : FiniteDimensional k (div_field k K E m) → Finite (E⟮k⟯ ⧸ m ⬝ E⟮k⟯) := by
  intro h
  -- (a priori) infinite Galois theory again
  have : Finite (div_field k K E m ≃ₐ[k] div_field k K E m) := sorry
  have : Finite {p : E⟮K⟯ | m • p = 0} := tor_finite (E.baseChange K) m
  have : Finite (m_tor (E⟮K⟯) m) := this
  have : Finite ((div_field k K E m ≃ₐ[k] div_field k K E m) → m_tor (E⟮K⟯) m) := Pi.finite
  have : Finite (Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ m_tor (E⟮K⟯) m) :=
    @Finite.of_injective_finite_range _ _ _ (fun_incl_inj k K E m) (Subtype.finite)
  have : Finite {f : Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ E⟮K⟯ | f.range ≤ (m_tor (E⟮K⟯) m)} :=
    Finite.of_equiv (Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ m_tor (E⟮K⟯) m) (range₂ k K E m).symm
  have : Finite (kummer k K E m htor).range := Finite.Set.subset {f : Additive (div_field k K E m ≃ₐ[k] div_field k K E m) →+ E⟮K⟯ | f.range ≤ (m_tor (E⟮K⟯) m)} (kummer_range k K E m htor)
  have : Finite (Set.range (kummer k K E m htor)) := this
  exact Finite.of_injective_finite_range (kummer_inj k K E m htor)

/-
  I won't be able to prove this. The proof requires Kummer theory and Dirichlet's S-unit-theorem,
  both of which are difficult theorems which are not formalized yet. Just stating the latter
  would require heaps of formalization work on valuations and completions.
-/
theorem div_field_fin : FiniteDimensional k (div_field k K E m) := by
  sorry

end Kummer
