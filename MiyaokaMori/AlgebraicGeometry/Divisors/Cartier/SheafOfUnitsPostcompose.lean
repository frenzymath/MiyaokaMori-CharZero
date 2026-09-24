import MiyaokaMori.Prelude

/-! # The sheaf of units of a sheaf of commutative rings

Postcomposing a sheaf of commutative rings with the units functor gives a sheaf of commutative
groups: `CommMonCat.units` is a right adjoint, hence preserves limits, and the sheaf condition is
preserved under postcomposition with a limit-preserving functor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The sheaf of units `F^*` of a sheaf of commutative rings `F`. -/
noncomputable def TopCat.Sheaf.units {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X) :
    TopCat.Sheaf CommGrpCat.{u} X :=
  ⟨F.val ⋙ CategoryTheory.forget₂ CommRingCat.{u} CommMonCat.{u} ⋙ CommMonCat.units.{u},
    CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.cond⟩

/-- Functoriality: a morphism of sheaves of rings induces a morphism of sheaves of units. -/

noncomputable def TopCat.Sheaf.unitsMap {X : TopCat.{u}} {F G : TopCat.Sheaf CommRingCat.{u} X}
    (φ : F ⟶ G) : TopCat.Sheaf.units F ⟶ TopCat.Sheaf.units G :=
  ⟨CategoryTheory.Functor.whiskerRight φ.hom
    (CategoryTheory.forget₂ CommRingCat.{u} CommMonCat.{u} ⋙ CommMonCat.units.{u})⟩

end
