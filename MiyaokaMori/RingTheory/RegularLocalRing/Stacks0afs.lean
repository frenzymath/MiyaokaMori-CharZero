import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o8
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00oc

/-! # Stacks 0AFS: localizations of a regular local ring are regular

Stacks 0AFS (Serre): the localization of a regular local ring at any prime is again a regular local ring, i.e.
a regular local ring is a regular ring.

Reference: Stacks 0AFS (in the proof of 0AG0: `R_q` regular).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IsRegularLocalRing.isRegularRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p hp
  obtain ⟨n, hn⟩ :=
    ((IsLocalRing.tfae_isRegularLocalRing_finite_globalDimension R).1.out 2 1).mp
      (inferInstance : IsRegularLocalRing R)
  have hloc : ∀ N : ModuleCat (Localization.AtPrime p),
      CategoryTheory.HasProjectiveDimensionLE N n :=
    Localization.forall_hasProjectiveDimensionLE_of_forall p.primeCompl n hn
  apply ((IsLocalRing.tfae_isRegularLocalRing_finite_globalDimension
    (Localization.AtPrime p)).1.out 1 2).mp
  exact ⟨n, hloc⟩

end
