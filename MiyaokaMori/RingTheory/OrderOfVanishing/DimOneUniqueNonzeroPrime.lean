import MiyaokaMori.Prelude

/-! # The maximal ideal of a one-dimensional local domain is its unique nonzero prime

A Noetherian local domain of Krull dimension `≤ 1` which is not a field has the maximal ideal as its unique
nonzero prime ideal. (Used in the proof of Proposition 3.2 of the paper.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem bridge_unique_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] (h : Ring.KrullDimLE 1 R) (hnf : ¬ IsField R) :
    ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
  let _ : Ring.KrullDimLE 1 R := h
  refine ⟨IsLocalRing.maximalIdeal R, ?_, ?_⟩
  · constructor
    · intro hbot
      exact hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  · intro P hP
    exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

end
