import Mathlib.AlgebraicGeometry.EllipticCurve.Point
import LeanCourse.Project.Descent
import LeanCourse.Project.WeakMordell.Local

set_option maxHeartbeats 500000

/-
  Proof that E(K)/mE(K) being finite is preserved under finite Galois field extensions.
  This allows us to later assume wlog that E[m] ⊆ E(K).
  Also introduces the Galois action on E(K) with basic properties.
  Reference: J. Silverman, Arithmetic of Elliptic Curves
  This is exactly VIII, Lemma 1.1, following both the proof and notation.
-/

universe u
variable (K : Type u) [Field K] [NumberField K]
         (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [NumberField L]
         (E : EllipticCurve K) (m : ℕ) (hm : 2 ≤ m)

noncomputable section
open EllipticCurve Descent WeierstrassCurve Classical

-- the map from the group under consideration in the larger group. We show finiteness
-- by finiteness of kernel and codomain, the latter of which is an assumption.
def iota_mod : E⟮K⟯ ⧸ m ⬝ E⟮K⟯ →+ E⟮L⟯ ⧸ m ⬝ E⟮L⟯ :=
    QuotientAddGroup.map (m ⬝ E⟮K⟯) (m ⬝ E⟮L⟯) (Point.ofBaseChange E.toWeierstrassCurve K L) <| by
  rintro p ⟨q, hq⟩
  simp only [baseChange_toWeierstrassCurve, AddSubgroup.mem_comap]
  use (Point.ofBaseChange E.toWeierstrassCurve K L) q
  have hq : m • q = p := hq
  rw [← hq]
  unfold mul_m; simp

-- so the main work is showing that Φ := ker is finite.
def Phi := AddMonoidHom.ker (iota_mod K L E m)

lemma Phi_eq : Phi K L E m = AddSubgroup.map (QuotientAddGroup.mk' (m ⬝ E⟮K⟯))
    (AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯)) := by
  ext p; constructor
  · simp
    intro h
    unfold Phi at h
    rw [AddMonoidHom.mem_ker] at h
    let x := Exists.choose (QuotientAddGroup.mk'_surjective (m ⬝ E⟮K⟯) p)
    have hx : QuotientAddGroup.mk' (m ⬝ E⟮K⟯) x = p :=
      Exists.choose_spec (QuotientAddGroup.mk'_surjective (m ⬝ E⟮K⟯) p)
    use x; constructor; swap; exact hx
    rw [← hx] at h
    have : iota_mod K L E m (QuotientAddGroup.mk' (m ⬝ E⟮K⟯) x) =
        QuotientAddGroup.mk' (m ⬝ E⟮L⟯) (Point.ofBaseChange E.toWeierstrassCurve K L x) := rfl
    have : QuotientAddGroup.mk' (m ⬝ E⟮L⟯) (Point.ofBaseChange E.toWeierstrassCurve K L x) = 0 := by
      trans iota_mod K L E m (QuotientAddGroup.mk' (m ⬝ E⟮K⟯) x)
      exact this.symm; exact h
    exact (QuotientAddGroup.eq_zero_iff (Point.ofBaseChange E.toWeierstrassCurve K L x)).1 this
  · simp
    intro x h hp
    unfold Phi
    rw [AddMonoidHom.mem_ker, ← hp]
    have : iota_mod K L E m (QuotientAddGroup.mk' (m ⬝ E⟮K⟯) x) =
        QuotientAddGroup.mk' (m ⬝ E⟮L⟯) (Point.ofBaseChange E.toWeierstrassCurve K L x) := rfl
    trans QuotientAddGroup.mk' (m ⬝ E⟮L⟯) (Point.ofBaseChange E.toWeierstrassCurve K L x)
    exact this
    exact (QuotientAddGroup.eq_zero_iff (Point.ofBaseChange E.toWeierstrassCurve K L x)).2 h

-- for P ∈ Φ, choose Q ∈ E(L) s.t. mQ = P
def Q : AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯) → E⟮L⟯ :=
  fun p ↦ Exists.choose (AddSubgroup.mem_comap.1 <| SetLike.coe_mem p)

lemma Q_spec (p : AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯)) :
    m • (Q K L E m p) = Point.ofBaseChange E.toWeierstrassCurve K L p := by
  exact Exists.choose_spec (AddSubgroup.mem_comap.1 <| SetLike.coe_mem p)

-- Gal(L/K) acts on E(L) by acting on coordinates.
-- We show that this is well-defined, defines an action, and commutes with the group law on E(L)
lemma action_on_curve (σ : L ≃ₐ[K] L) {x y : L} (h : (E.baseChange L).equation x y) :
    (E.baseChange L).equation (σ x) (σ y) := by
  unfold WeierstrassCurve.equation; unfold WeierstrassCurve.polynomial; simp
  unfold WeierstrassCurve.equation at h;
  unfold WeierstrassCurve.polynomial at h; simp at h
  rw [← AlgEquiv.commutes σ E.a₁, ← AlgEquiv.commutes σ E.a₂, ← AlgEquiv.commutes σ E.a₃]
  rw [← AlgEquiv.commutes σ E.a₄, ← AlgEquiv.commutes σ E.a₆]
  rw [← AlgEquiv.map_mul, ← AlgEquiv.map_mul, ← AlgEquiv.map_pow, ← AlgEquiv.map_pow, ← AlgEquiv.map_pow]
  rw [← AlgEquiv.map_mul, ← AlgEquiv.map_add, ← AlgEquiv.map_add, ← AlgEquiv.map_add, ← AlgEquiv.map_add]
  rw [← AlgEquiv.map_mul, ← AlgEquiv.map_add, ← AlgEquiv.map_sub]
  rw [congrArg σ h]; exact AlgEquiv.map_zero σ

def gal_action (σ : L ≃ₐ[K] L) : E⟮L⟯ → E⟮L⟯
  | 0 => 0
  | Point.some h => Point.some (nonsingular (E.baseChange L) (action_on_curve K L E σ h.1))

lemma gal_action_one (p : E⟮L⟯) : gal_action K L E 1 p = p := by
  rcases p with h | h <;>
  unfold gal_action <;> simp[Point.zero_def]

lemma gal_action_assoc (σ τ : L ≃ₐ[K] L) (p : E⟮L⟯) :
    gal_action K L E (σ * τ) p = gal_action K L E σ (gal_action K L E τ p) := by
  rcases p with h | @⟨x,y,h⟩ <;>
  unfold gal_action <;> simp[Point.zero_def]

instance : MulAction (L ≃ₐ[K] L) (E⟮L⟯) where
  smul := gal_action K L E
  one_smul := gal_action_one K L E
  mul_smul := gal_action_assoc K L E

lemma smul_def (σ : L ≃ₐ[K] L) (p : E⟮L⟯) : σ • p = gal_action K L E σ p := rfl

lemma action_zero (σ : L ≃ₐ[K] L) : σ • (0 : E⟮L⟯) = 0 := rfl

lemma gal_action_some (σ : L ≃ₐ[K] L) {x y : L} (h : (E.baseChange L).toWeierstrassCurve.nonsingular x y) :
    σ • Point.some h = Point.some (nonsingular (E.baseChange L) (action_on_curve K L E σ h.1)) := rfl

lemma action_neg (σ : L ≃ₐ[K] L) (p : E⟮L⟯) : σ • (-p) = - (σ • p) := by
  rcases p with h | @⟨x,y,h⟩
  · simp[Point.zero_def]
    rw [action_zero]
    simp
  · simp
    rw [gal_action_some, gal_action_some]
    simp

-- this isn't hard, but lengthy and annoying because of lots of case distinctions and unfolds/calculations
lemma action_hom (σ : L ≃ₐ[K] L) (p q : E⟮L⟯) : σ • (p + q) = σ • p + σ • q := by
  rcases p with h | @⟨x,y,h⟩
  · rw [Point.zero_def, action_zero]; simp
  rcases q with h' | @⟨x',y',h'⟩
  · rw [Point.zero_def, action_zero]; simp
  by_cases hn : Point.some h = - Point.some h'
  · rw [hn, action_neg]; simp; exact action_zero K L E σ
  by_cases hx : x = x'
  · rw [Point.some_add_some_of_Y_ne hx]; swap
    · by_contra H
      have : Point.some h = - Point.some h' := by
        rw[Point.neg_some]; simp; exact ⟨hx, H⟩
      exact hn this
    simp; rw [gal_action_some, gal_action_some, gal_action_some]
    rw [Point.some_add_some_of_Y_ne (congrArg σ hx)]; swap
    · by_contra H
      have : σ • Point.some h = σ • (-Point.some h') := by
        rw [Point.neg_some, gal_action_some, gal_action_some]
        simp; constructor; exact hx; exact H
      have : σ⁻¹ • σ • Point.some h = σ⁻¹ • σ • -Point.some h' :=
        congrArg (HSMul.hSMul σ⁻¹) this
      rw [← mul_smul, ← mul_smul, mul_left_inv, one_smul, one_smul] at this
      exact hn this
    simp
    have : σ (slope (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x x' y y') =
        slope (WeierstrassCurve.baseChange E.toWeierstrassCurve L) (σ x) (σ x') (σ y) (σ y') := by
      unfold slope; rw [if_pos hx, if_pos (congrArg σ hx)]
      have hy : y ≠ negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x' y' := by
        by_contra H
        have : Point.some h = -Point.some h' := by rw [Point.neg_some]; simp; exact ⟨hx, H⟩
        exact hn this
      rw [if_neg hy]
      have hneg : σ (negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x' y') =
          negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) (σ x') (σ y') := by simp
      have hy : σ y ≠ negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) (σ x') (σ y') := by
        rw [← hneg]; by_contra H
        have : σ.symm (σ y) = σ.symm (σ (negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x' y')) :=
          congrArg σ.symm H
        simp at this; exact hy this
      have hneg2 : σ (negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x y) =
          negY (WeierstrassCurve.baseChange E.toWeierstrassCurve L) (σ x) (σ y) := by simp
      rw [if_neg hy, map_div₀ σ, AlgEquiv.map_sub, AlgEquiv.map_add, AlgEquiv.map_sub]
      rw [hneg2, AlgEquiv.map_add, AlgEquiv.map_mul, AlgEquiv.map_mul, AlgEquiv.map_mul]
      simp
    constructor; rw [this]; rw [this]
  · rw [Point.some_add_some_of_X_ne hx, gal_action_some, gal_action_some, gal_action_some]
    rw [Point.some_add_some_of_X_ne]; swap
    · by_contra H
      have : σ.symm (σ x) = σ.symm (σ x') := congrArg σ.symm H
      simp at this; exact hx this
    simp
    have : σ (slope (WeierstrassCurve.baseChange E.toWeierstrassCurve L) x x' y y') =
        slope (WeierstrassCurve.baseChange E.toWeierstrassCurve L) (σ x) (σ x') (σ y) (σ y') := by
      unfold slope
      rw [if_neg hx, if_neg]
      simp
      by_contra H
      have : σ.symm (σ x) = σ.symm (σ x') := congrArg σ.symm H
      simp at this; exact hx this
    constructor; rw [this]; rw [this]

lemma nsmul_hom_action (σ : L ≃ₐ[K] L) (p : E⟮L⟯) (n : ℕ) : n • σ • p = σ • n • p := by
  induction' n with n hn
  · simp; exact (action_zero K L E σ).symm
  rw [succ_nsmul, succ_nsmul, action_hom, hn]

-- the galois action fixes E(K), and if L/K is Galois, these are the only fixed points
lemma gal_action_base (σ : L ≃ₐ[K] L) (p : E⟮K⟯) :
    σ • (show E⟮L⟯ from (Point.ofBaseChange E.toWeierstrassCurve K L p)) = (Point.ofBaseChange E.toWeierstrassCurve K L p : E⟮L⟯) := by
  rcases p with h | @⟨x,y,h⟩
  · simp; unfold Point.ofBaseChangeFun; simp; exact action_zero K L E σ
  simp; unfold Point.ofBaseChangeFun; simp
  rw [gal_action_some]; simp

lemma gal_fixed_field [IsGalois K L] (x : L) (h : ∀ σ : L ≃ₐ[K] L, σ x = x) : x ∈ (algebraMap K L).range := by
  have hgal : IntermediateField.fixedField ⊤ = ⊥ := (List.TFAE.out (@IsGalois.tfae K _ L _ _ _) 0 1).1 (by infer_instance)
  have : (algebraMap K L).range = (⊥ : IntermediateField K L).toSubring := rfl
  rw [this, ← hgal]; simp
  unfold IntermediateField.fixedField; unfold FixedPoints.intermediateField; simp
  apply Subsemiring.mem_carrier.1; simp
  exact fun σ _ ↦ h σ

lemma gal_action_fixed [IsGalois K L] (p : E⟮L⟯) (h : ∀ σ : L ≃ₐ[K] L, σ • p = p) :
    p ∈ (Point.ofBaseChange E.toWeierstrassCurve K L).range := by
  rcases p with h | @⟨x,y,hp⟩
  · simp; use 0; simp[Point.zero_def]; rfl
  have hxy : ∀ σ : (L ≃ₐ[K] L), σ x = x ∧ σ y = y := fun σ ↦ by
    specialize h σ
    rw [gal_action_some] at h
    simp at h; exact h
  obtain ⟨x', hx⟩ := gal_fixed_field K L x <| fun σ ↦ (hxy σ).1
  obtain ⟨y', hy⟩ := gal_fixed_field K L y <| fun σ ↦ (hxy σ).2
  have he : E.equation x' y' := by
    apply (equation_iff_baseChange E.toWeierstrassCurve L x' y').2
    rw [hx, hy]; exact hp.1
  use Point.some <| nonsingular E he; simp
  unfold Point.ofBaseChangeFun; simp
  exact ⟨hx, hy⟩

-- to show that Φ is finite, we prove that
-- λ : Φ → (Gal(L/K) → E(L)[m]) , [p] ↦ σ ↦ σ • (Q p) - (Q p)
-- is injective, and the codomain is clearly finite.
-- note that this depends on the choice of representative for [p] and the choice of Q p
-- Also, λ [p] is only a function of sets, not a group morphism
def lambda : AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯) → (L ≃ₐ[K] L) → E⟮L⟯ :=
  fun p σ ↦ σ • (Q K L E m p) - (Q K L E m p)

lemma lambda_tor {p : AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯)}
    {σ : (L ≃ₐ[K] L)} : m • lambda K L E m p σ = 0 := by
  unfold lambda
  rw [nsmul_sub, nsmul_hom_action, Q_spec, gal_action_base]
  simp

lemma lambda_inj [IsGalois K L] {p₁ p₂ : AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯)}
    (h : lambda K L E m p₁ = lambda K L E m p₂) : Subtype.val p₁ - Subtype.val p₂ ∈ m ⬝ E⟮K⟯ := by
  have hσ : ∀ σ : L ≃ₐ[K] L, σ • (Q K L E m p₁ - Q K L E m p₂) = Q K L E m p₁ - Q K L E m p₂ := by
    intro σ
    rw [sub_eq_add_neg, action_hom, action_neg, ← sub_eq_add_neg]
    apply sub_eq_of_eq_add
    rw [add_assoc, add_comm]
    apply eq_add_of_sub_eq
    rw [add_comm, ← sub_eq_add_neg]
    exact congrFun h σ
  have hQ : Q K L E m p₁ - Q K L E m p₂ ∈ (Point.ofBaseChange E.toWeierstrassCurve K L).range :=
    gal_action_fixed K L E (Q K L E m p₁ - Q K L E m p₂) hσ
  have : Function.Injective (Point.ofBaseChange E.toWeierstrassCurve K L) :=
    Point.ofBaseChange_injective E.toWeierstrassCurve K L
  apply (AddSubgroup.mem_map_iff_mem this).1
  rw [map_sub, ← Q_spec, ← Q_spec, ← smul_sub]
  obtain ⟨q, hq⟩ := hQ
  use m • q; constructor
  · use q; rfl
  simp; simp at hq; rw [hq]; exact nsmul_sub (Q K L E m p₁) (Q K L E m p₂) m

lemma quot_lift (p : E⟮K⟯ ⧸ (m ⬝ E⟮K⟯)) (h : p ∈ Phi K L E m) :
    ∃ q : (AddSubgroup.comap (Point.ofBaseChange E.toWeierstrassCurve K L) (m ⬝ E⟮L⟯)),
    QuotientAddGroup.mk' (m ⬝ E⟮K⟯) (Subtype.val q) = p := by
  rw [Phi_eq] at h
  obtain ⟨q, hq⟩ := h
  use {val := q, property := hq.1}
  exact hq.2

def lambda' : E⟮K⟯ ⧸ (m ⬝ E⟮K⟯) → (L ≃ₐ[K] L) → E⟮L⟯ := fun p ↦
  if h : p ∈ SetLike.coe (Phi K L E m) then (lambda K L E m) (Exists.choose <| quot_lift K L E m p h) else 0

lemma lambda'_injOn [IsGalois K L] : Set.InjOn (lambda' K L E m) (Phi K L E m) := by
  intro p hp q hq hpq
  unfold lambda' at hpq
  rw [dif_pos hp, dif_pos hq] at hpq
  set P := Exists.choose <| quot_lift K L E m p hp with hP
  set Q := Exists.choose <| quot_lift K L E m q hq with hQ
  rw [← Exists.choose_spec (quot_lift K L E m p hp), ← Exists.choose_spec (quot_lift K L E m q hq), ← hP, ← hQ]
  obtain ⟨R, hR⟩ := lambda_inj K L E m hpq
  rw [QuotientAddGroup.mk'_eq_mk']
  use -(m • R); constructor; use -R; simp; rfl
  have : (mul_m m) R = m • R := rfl
  rw [this] at hR; rw [hR]; simp

lemma Phi_finite [IsGalois K L] : Finite (Phi K L E m) := by
  apply Set.finite_coe_iff.2
  apply Set.Finite.of_finite_image _ (lambda'_injOn K L E m)
  have : lambda' K L E m '' (SetLike.coe <| Phi K L E m) ⊆ {f : (L ≃ₐ[K] L) → E⟮L⟯ | ∀ σ : (L ≃ₐ[K] L), m • (f σ) = 0} := by
    rintro p ⟨q, h, rfl⟩
    simp; intro σ; unfold lambda'
    rw [dif_pos h, lambda_tor]
  apply Set.Finite.subset _ this
  set F : ((L ≃ₐ[K] L) → E⟮L⟯) → (L ≃ₐ[K] L) → {p : E⟮L⟯ | m • p = 0} := fun f ↦
    if h : ∀ σ : (L ≃ₐ[K] L), m • (f σ) = 0 then fun σ ↦ ⟨f σ, h σ⟩ else fun _ ↦ ⟨0, by simp⟩ with hF
  have : Set.InjOn F {f | ∀ σ, m • (f σ) = 0} := by
    intro f hf g hg h; ext σ
    simp at hf; simp at hg
    rw [hF] at h; simp at h
    rw [dif_pos hf, dif_pos hg] at h
    have : _ := congrFun h σ
    simp at this; exact this
  apply Set.Finite.of_finite_image _ this
  apply Set.Finite.subset _ (Set.subset_univ _)
  have hf1 : Finite (L ≃ₐ[K] L) := Finite.of_fintype (L ≃ₐ[K] L)
  have hf2 : Finite {p : E⟮L⟯ | m • p = 0} := tor_finite (E.baseChange L) m
  have : Finite ((L ≃ₐ[K] L) → {p : E⟮L⟯ | m • p = 0}) := Pi.finite
  exact Set.finite_univ

-- main theorem
theorem WeakMordell.galois_reduction [IsGalois K L] (_ : Finite (E⟮L⟯ ⧸ m ⬝ E⟮L⟯)) : Finite (E⟮K⟯ ⧸ m ⬝ E⟮K⟯) :=
  have : Finite ((iota_mod K L E m).ker) := Phi_finite K L E m
  Fintype.finite <| @AddGroup.fintypeOfKerOfCodom (E⟮K⟯ ⧸ m ⬝ E⟮K⟯) (E⟮L⟯ ⧸ m ⬝ E⟮L⟯) _ _
      (Fintype.ofFinite (E⟮L⟯ ⧸ m ⬝ E⟮L⟯)) (iota_mod K L E m) (Fintype.ofFinite (↥AddMonoidHom.ker (iota_mod K L E m)))
