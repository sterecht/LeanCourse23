import Mathlib.AlgebraicGeometry.EllipticCurve.Point
import LeanCourse.Project.Descent

open WeierstrassCurve EllipticCurve
notation E "⟮" S "⟯" => Point (toWeierstrassCurve (baseChange E S))

def m_tor {G : Type*} [AddCommGroup G] (m : ℕ) : AddSubgroup G where
  carrier := {g : G | m • g = 0}
  add_mem' := fun a b ↦ by simp at *; simp[a, b]
  zero_mem' := by simp
  neg_mem' := by simp









namespace EllipticCurve
theorem tor_finite {K : Type*} [Field K] [NumberField K] (E : EllipticCurve K) (m : ℕ) : Finite {p : E⟮K⟯ | m • p = 0} := by
  sorry
