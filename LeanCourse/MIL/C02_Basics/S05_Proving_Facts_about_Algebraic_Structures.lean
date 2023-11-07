import LeanCourse.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    exact inf_le_right
    exact inf_le_left



example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    --exact le_trans (inf_le_left (x ⊓ y) z) (inf_le_left x y)
    trans x ⊓ y
    apply inf_le_left
    apply inf_le_left
    apply le_inf
    trans x ⊓ y
    apply inf_le_left
    apply inf_le_right
    apply inf_le_right
  · apply le_inf
    apply le_inf
    exact inf_le_left
    trans y ⊓ z
    exact inf_le_right
    exact inf_le_left
    trans y ⊓ z
    exact inf_le_right
    exact inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  apply sup_le
  exact le_sup_right
  exact le_sup_left
  apply sup_le
  exact le_sup_right
  exact le_sup_left



example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by {
  apply le_antisymm
  apply sup_le
  apply sup_le
  exact le_sup_left
  trans y ⊔ z
  exact le_sup_left
  exact le_sup_right
  trans y ⊔ z
  exact le_sup_right
  exact le_sup_right
  apply sup_le
  trans x ⊔ y
  exact le_sup_left
  exact le_sup_left
  apply sup_le
  trans x ⊔ y
  exact le_sup_right
  exact le_sup_left
  exact le_sup_right
}


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  exact inf_le_left
  apply le_inf
  rfl
  exact le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  rfl
  exact inf_le_left
  exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  apply le_inf
  apply sup_le
  exact le_sup_left
  trans b
  exact inf_le_left
  exact le_sup_right
  apply sup_le
  exact le_sup_left
  trans c
  exact inf_le_right
  exact le_sup_right
  rw [h]
  apply sup_le
  rw [inf_comm]
  rw [h]
  apply sup_le
  rw [inf_idem]
  exact le_sup_left
  trans a
  exact inf_le_left
  exact le_sup_left
  rw [inf_comm]
  rw [h]
  apply sup_le
  trans a
  exact inf_le_right
  exact le_sup_left
  rw [inf_comm]
  exact le_sup_right




example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ _ a, absorb2, @sup_comm _ _ (a ⊓ b) c, h]
  rw [← inf_assoc, @sup_comm _ _ c, absorb1, @sup_comm _ _ c]


end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  simp
  assumption

example (h: 0 ≤ b - a) : a ≤ b := by
  simp at h
  assumption

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : 0 ≤ (b - a) := by
    simp
    assumption
  have : 0 ≤ (b - a) * c := mul_nonneg this h'
  have : 0 ≤ b * c - a * c := by
    calc 0
      _ ≤ (b - a) * c := this
      _ = b * c - a * c := by rw [sub_mul]
  simp at this
  assumption

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  calc (0 : ℝ)
    _ = (1/2) * 0 := by norm_num
    _ = (1/2) * dist x x := by rw [dist_self]
    _ ≤ (1/2) * (dist x y + dist y x) := ?_
    _ = (1/2) * (dist x y + dist x y) := by rw [dist_comm]
    _ = (1/2) * (2 * dist x y) := by rw [two_mul]
    _ = (1/2 * 2) * dist x y := by rw [mul_assoc]
    _ = 1 * dist x y := by norm_num
    _ = dist x y := by simp
  simp
  rw [← dist_self x]
  exact dist_triangle x y x
end
