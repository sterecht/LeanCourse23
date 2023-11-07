import LeanCourse.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h x hs
  simp
  apply h
  exact mem_image_of_mem f hs
  intro h y hs
  obtain ⟨x, hx, hxy⟩ := hs
  subst y
  exact h hx


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s :=
  fun _ ⟨_, hs, hy⟩ ↦ mem_of_eq_of_mem (h hy.symm) hs

example : f '' (f ⁻¹' u) ⊆ u :=
  fun _ ⟨_, hs, hx⟩ ↦ mem_of_eq_of_mem hx.symm hs

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  obtain ⟨x, hx⟩ := h y
  use x
  simp
  exact ⟨mem_of_eq_of_mem hx hy, hx⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
  fun _ ⟨x, hs, hx⟩ ↦ ⟨x, (h hs), hx⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
  fun _ hx ↦ h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  fun _ ⟨x, hst, hx⟩ ↦ ⟨⟨x, hst.1, hx⟩, ⟨x, hst.2, hx⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro _ ⟨⟨x, hs, hx⟩, ⟨z, ht, rfl⟩⟩
  have : x = z := h hx
  subst z
  use x, ⟨hs, ht⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro _ ⟨⟨x, hs, hx⟩, ht⟩
  use x
  simp
  exact ⟨⟨hs, fun h ↦ ht ⟨x, h, hx⟩⟩, hx⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro _ h
  simp; exact h

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  simp
  constructor
  rintro ⟨⟨x, hs, hy⟩, hx⟩
  use x, ⟨hs, mem_of_eq_of_mem hy hx⟩
  rintro ⟨x, ⟨⟨hs, hy⟩, hx⟩⟩
  exact ⟨⟨x, hs, hx⟩, mem_of_eq_of_mem hx.symm hy⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨hs, hu⟩, rfl⟩
  exact ⟨mem_image_of_mem f hs, hu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨hs, hu⟩
  simp
  constructor
  use x
  exact hu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x
  simp
  rintro (h | h)
  left; use x
  right; exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, _, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]


example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy hxy
  calc x
    _ = (sqrt x) ^ 2 := by rw [sq_sqrt hx]
    _ = (sqrt y) ^ 2 := by rw [hxy]
    _ = y := by rw [sq_sqrt hy]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy hxy
  simp at hxy
  calc x
    _ = sqrt (x ^ 2) := by rw [sqrt_sq hx]
    _ = sqrt (y ^ 2) := by rw [hxy]
    _ = y := by rw [sqrt_sq hy]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp
  constructor
  rintro ⟨x, _, rfl⟩
  exact sqrt_nonneg x
  exact fun h ↦ ⟨y ^ 2, sq_nonneg y, sqrt_sq h⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp
  constructor
  rintro ⟨x, rfl⟩
  exact sq_nonneg x
  exact fun h ↦ ⟨sqrt y, sq_sqrt h⟩

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h x ↦ h (inverse_spec (f x) ⟨x, by rfl⟩),
   fun h x y hxy ↦ by rw [← h x, ← h y, hxy]⟩

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h y ↦ inverse_spec y (h y), fun h y ↦ ⟨(inverse f) y, h y⟩⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [← h]
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
