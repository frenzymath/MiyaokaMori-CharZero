import MiyaokaMori.RingTheory.OrderOfVanishing.DimOneUniqueNonzeroPrime

/-! # A normal one-dimensional Noetherian local domain is a DVR

A one-dimensional Noetherian integrally closed local domain is a discrete valuation ring (after normalizing a
curve, every local ring is a DVR). (Used in the proof of Proposition 3.2 of the paper.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem isDiscreteValuationRing_of_isIntegrallyClosed_of_dim_one
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (h : Ring.KrullDimLE 1 R) (hnt : ¬ IsField R) :
    IsDiscreteValuationRing R := by
  apply ((IsDiscreteValuationRing.TFAE R hnt).out 3 0).mp
  exact ⟨inferInstance, bridge_unique_nonzero_prime R h hnt⟩

end
