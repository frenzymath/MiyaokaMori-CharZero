import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnitsPostcompose

/-! # Sheaves of units on a scheme

The sheaf of units `F^*: U ↦ Γ(F, U)^×` of a sheaf of rings is a sheaf of commutative groups. For the
structure sheaf this gives `O_X^*`, for the sheaf of rational functions `𝒦_X^*`; both enter the
sheaf-theoretic descriptions of Cartier divisors and of the Picard group.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The sheaf of units `O_X^*` of the structure sheaf. -/
noncomputable def AlgebraicGeometry.Scheme.unitsSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    TopCat.Sheaf CommGrpCat.{u} X :=
  TopCat.Sheaf.units X.sheaf

/-- The sheaf of units `𝒦_X^*` of the sheaf of rational functions. -/
noncomputable def AlgebraicGeometry.Scheme.rationalFunctionsUnitsSheaf
    (X : AlgebraicGeometry.Scheme.{u}) : TopCat.Sheaf CommGrpCat.{u} X :=
  TopCat.Sheaf.units X.rationalFunctionsSheaf

end
