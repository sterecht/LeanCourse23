import LeanCourse.Common
/-
  This file contains (difficult) theorems that are from fields not directly related to my project,
  but needed in proofs. I probably won't be able to prove these.
-/

section InfiniteGalois
variable (k : Type*) (K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-
  Infinite Galois theory is not formalized in Lean. If K/k is a (possibly infinite) field extension,
  there is an inclusion-reversing bijection between closed subgroups (w.r.t. the Krull topology) of Gal(K/k)
  and intermediate Galois fields, sending a subgroup to its fixed field and a field to its fixing subgroup.

  I only need the special case of the full group corresponding to the base field, i.e:
  x ∈ k iff it is fixed by all k-linear field automorphisms K → K.
  One direction is trivial and doesn't need Galois theory, the other direction is difficult,
  at least I don't see a quick way of proofing this without the full machinery of infinite Galois theory.
-/
theorem fixed_field_gal_inf (x : K) : x ∈ (algebraMap k K).range ↔ (∀ σ : (K ≃ₐ[k] K), σ x = x) :=
  sorry


end InfiniteGalois
