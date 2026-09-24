import MiyaokaMori.Prelude

/-! # The sheaf of rational functions as a sheafification

The sheaf of rational functions `𝒦_X` is defined as the sheafification of Mathlib's presheaf of total
quotient rings `totalQuotientPresheaf`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The sheaf of rational functions `𝒦_X`: the sheafification of the presheaf of total quotient rings. -/
noncomputable def AlgebraicGeometry.Scheme.rationalFunctionsSheaf
    (X : AlgebraicGeometry.Scheme.{u}) : TopCat.Sheaf CommRingCat.{u} X :=
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
      CommRingCat.{u}).obj X.presheaf.totalQuotientPresheaf

/-- `O_X → 𝒦_X`: the localization map to the presheaf of total quotient rings followed by the sheafification
unit. -/

noncomputable def AlgebraicGeometry.Scheme.toRationalFunctionsSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    X.sheaf ⟶ X.rationalFunctionsSheaf :=
  ⟨X.presheaf.toTotalQuotientPresheaf ≫
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) _⟩

end
