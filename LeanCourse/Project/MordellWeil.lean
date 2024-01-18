import Mathlib.AlgebraicGeometry.EllipticCurve.Point
import Mathlib.GroupTheory.Finiteness
import LeanCourse.Project.Descent
import LeanCourse.Project.HeightFunctions.EllipticHeight
import LeanCourse.Project.WeakMordell.KummerPairing
import LeanCourse.Project.WeakMordell.GaloisReduction


variable (E : EllipticCurve ℚ)

theorem mw_of_weak_short (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (ha₄ : Rat.isInt E.a₄) (ha₆ : Rat.isInt E.a₆) (h : Finite (E.Point ⧸ m_multiples 2 E.Point)) :
    AddGroup.FG (E.Point) :=
  have : ∃ C > 0, ∀ p : E.Point, EllipticHeight.h (2 • p) ≥ (2 ^ 2) * (EllipticHeight.h p) - C := by
    have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this]; exact EllipticHeight.height_le_double ha₁ ha₂ ha₃ ha₄ ha₆
  Descent.fg_of_height_function EllipticHeight.h
      (EllipticHeight.height_sum_le ha₁ ha₂ ha₃ ha₄ ha₆)
      2 (by norm_num) this
      (EllipticHeight.fin_of_fin_height ha₁ ha₂ ha₃) h

theorem mw_short (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (ha₄ : Rat.isInt E.a₄) (ha₆ : Rat.isInt E.a₆) : AddGroup.FG (E.Point) :=
  sorry

theorem mordell_weil : AddGroup.FG E.Point := sorry
