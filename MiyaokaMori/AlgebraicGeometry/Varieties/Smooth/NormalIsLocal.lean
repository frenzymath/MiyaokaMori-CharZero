import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme

/-! # Normality is local

Normality of a scheme can be checked on an open cover.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme covered by normal open subschemes is normal. -/
theorem isNormal_of_openCover {X : AlgebraicGeometry.Scheme.{u}} (𝒰 : X.OpenCover)
    (h : ∀ i, (𝒰.X i).IsNormal) : X.IsNormal := by
  constructor
  · intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    letI : (𝒰.X i).IsNormal := h i
    let e := (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv
    letI : IsDomain ((𝒰.X i).presheaf.stalk y) :=
      AlgebraicGeometry.Scheme.IsNormal.isDomain y
    exact e.toMulEquiv.isDomain _
  · intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    letI : (𝒰.X i).IsNormal := h i
    let e := (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv
    letI : IsIntegrallyClosed ((𝒰.X i).presheaf.stalk y) :=
      AlgebraicGeometry.Scheme.IsNormal.integrallyClosed y
    exact IsIntegrallyClosed.of_equiv e.symm

end
