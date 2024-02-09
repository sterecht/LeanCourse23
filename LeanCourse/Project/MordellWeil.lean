import Mathlib.AlgebraicGeometry.EllipticCurve.Point
import Mathlib.GroupTheory.Finiteness
import LeanCourse.Project.Descent
import LeanCourse.Project.HeightFunctions.EllipticHeight
import LeanCourse.Project.WeakMordell.KummerPairing
import LeanCourse.Project.WeakMordell.GaloisReduction

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 200000

variable (E : EllipticCurve ℚ)

theorem mw_of_weak (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (ha₄ : Rat.isInt E.a₄) (ha₆ : Rat.isInt E.a₆) (h : Finite (E.Point ⧸ m_multiples 2 E.Point)) :
    AddGroup.FG (E.Point) :=
  have : ∃ C > 0, ∀ p : E.Point, EllipticHeight.h (2 • p) ≥ (2 ^ 2) * (EllipticHeight.h p) - C := by
    have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this]; exact EllipticHeight.height_le_double ha₁ ha₂ ha₃ ha₄ ha₆
  Descent.fg_of_height_function EllipticHeight.h
      (EllipticHeight.height_sum_le ha₁ ha₂ ha₃ ha₄ ha₆)
      2 (by norm_num) this
      (EllipticHeight.fin_of_fin_height ha₁ ha₂ ha₃) h

open GalReduction Kummer EllipticCurve
noncomputable section

def tor_field : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    Subfield.toIntermediateField (Subfield.closure <| ⋃₀ {field_of_def ℚ (AlgebraicClosure ℚ) E p | p ∈ m_tor (E⟮AlgebraicClosure ℚ⟯) 2}) <| by
  intro x
  apply Subfield.subset_closure
  have : 0 ∈ m_tor (E⟮AlgebraicClosure ℚ⟯) 2 := by
    unfold m_tor; simp; rfl
  have h : (field_of_def ℚ (AlgebraicClosure ℚ) E 0).carrier ⊆ ⋃₀ {field_of_def ℚ (AlgebraicClosure ℚ) E p | p ∈ m_tor (E⟮AlgebraicClosure ℚ⟯) 2} := by
    intro x hx
    apply Set.mem_sUnion.2
    simp
    use 0
    constructor; exact this
    exact hx
  have : algebraMap ℚ (AlgebraicClosure ℚ) x ∈ field_of_def ℚ (AlgebraicClosure ℚ) E 0 := by
    unfold field_of_def; simp
    exact IntermediateField.algebraMap_mem ⊥ x
  exact h this

def tor_field_normal : IntermediateField ℚ (AlgebraicClosure ℚ) := normalClosure ℚ (tor_field E) (AlgebraicClosure ℚ)

-- this should be easy: the two-torsion is finite, and each field_of_def is clearly finite.
-- I have proofs of both facts, but no matter how I try to piece them together, I get an error
-- (motive is not type correct)
instance : FiniteDimensional ℚ (tor_field E) := by
  unfold tor_field
  --rw [Subfield.closure_sUnion]
  sorry

instance : FiniteDimensional ℚ (tor_field_normal E) := normalClosure.is_finiteDimensional ℚ (tor_field E) (AlgebraicClosure ℚ)

instance : IsGalois ℚ (tor_field_normal E) := IsGalois.normalClosure ℚ (tor_field E) (AlgebraicClosure ℚ)

theorem mordell_weil (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (ha₄ : Rat.isInt E.a₄) (ha₆ : Rat.isInt E.a₆) : AddGroup.FG (E.Point) := by
  apply mw_of_weak E ha₁ ha₂ ha₃ ha₄ ha₆
  apply WeakMordell.galois_reduction ℚ (tor_field_normal E) E 2
  apply weak_mord_of_div_field_fin (tor_field_normal E) (AlgebraicClosure ℚ) (E.baseChange (tor_field_normal E)) 2
  · intro p hp
    obtain ⟨q, hq⟩ := field_of_def_spec ℚ (AlgebraicClosure ℚ) E p
    have : (field_of_def ℚ (AlgebraicClosure ℚ) E p) ≤ (tor_field_normal E) := by
      unfold tor_field_normal
      trans (tor_field E)
      · intro x hx
        unfold tor_field
        have : x ∈ Subfield.closure (⋃₀ {(field_of_def ℚ (AlgebraicClosure ℚ) E p).carrier | p ∈ m_tor (E⟮AlgebraicClosure ℚ⟯) 2}) := by
          apply Subfield.subset_closure
          apply Set.mem_sUnion.2
          use (field_of_def ℚ (AlgebraicClosure ℚ) E p)
          constructor
          use p
          constructor
          exact hp
          rfl
          exact hx
        exact this
      · exact IntermediateField.le_normalClosure (tor_field E)
    -- same problem as the sorry above
    sorry
  exact div_field_fin (tor_field_normal E) (AlgebraicClosure ℚ) (E.baseChange (tor_field_normal E)) 2
