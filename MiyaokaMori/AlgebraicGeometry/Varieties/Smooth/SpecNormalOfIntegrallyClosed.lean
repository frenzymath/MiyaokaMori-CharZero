import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme

/-! # The spectrum of an integrally closed domain is normal

`Spec` of an integrally closed domain is a normal scheme (the stalks are localizations, and a
localization of a normal domain is normal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Spec R` is normal for an integrally closed domain `R`. -/
theorem AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed (R : CommRingCat.{u}) [IsDomain R]
    [IsIntegrallyClosed R] : (AlgebraicGeometry.Spec R).IsNormal := by
  refine ⟨?_, ?_⟩
  · intro x
    letI : x.asIdeal.IsPrime := x.isPrime
    letI : IsDomain (Localization.AtPrime x.asIdeal) := by infer_instance
    letI : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) := by
      exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
        x.asIdeal.primeCompl_le_nonZeroDivisors
    exact (AlgebraicGeometry.Spec.stalkIso R x).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  · intro x
    letI : x.asIdeal.IsPrime := x.isPrime
    letI : IsDomain (Localization.AtPrime x.asIdeal) := by infer_instance
    letI : IsIntegrallyClosed (Localization.AtPrime x.asIdeal) := by
      exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
        x.asIdeal.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv
      (AlgebraicGeometry.Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm

end
