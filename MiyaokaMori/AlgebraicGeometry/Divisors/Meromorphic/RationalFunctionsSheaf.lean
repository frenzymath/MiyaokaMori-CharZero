import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalSectionToFunctionField

/-! # The sheaf of rational functions on an integral scheme

The sheaf of rational functions `𝒦_X` is the sheafification of the presheaf of total quotient rings; on an
integral scheme it is the constant sheaf with value the function field `K(X)`. Local equations of Cartier
divisors are taken from its sheaf of units `𝒦_X^*`. The statement here follows from the bijective form of
Stacks 01X5, `rationalSectionToFunctionField_bijective`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- On an integral scheme, the sections of `𝒦_X` over a nonempty open are in bijection with the function
field `K(X)` (Stacks 01X5). -/
theorem AlgebraicGeometry.Scheme.rationalFunctionsSheaf_sections_of_isIntegral
    (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Nonempty ((X.rationalFunctionsSheaf.val.obj (Opposite.op U)) ≅ X.functionField) :=
  ⟨(RingEquiv.ofBijective (X.rationalSectionToFunctionField U).hom
    (X.rationalSectionToFunctionField_bijective U)).toCommRingCatIso⟩

end
