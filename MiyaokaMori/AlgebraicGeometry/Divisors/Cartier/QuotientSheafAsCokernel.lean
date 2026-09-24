import MiyaokaMori.Prelude

/-! # Quotient sheaves of sheaves of commutative groups as cokernels

The quotient sheaf `F/G` of a morphism `G ⟶ F` of sheaves of commutative groups is the cokernel in
the abelian category `Sheaf(X, AddCommGrpCat)`, transported back to multiplicative notation through
the equivalence `CommGrpCat ≌ AddCommGrpCat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The quotient sheaf `F/G` of `i : G ⟶ F`: the cokernel of `i` in sheaves of additive commutative
groups, written multiplicatively. -/
noncomputable def TopCat.Sheaf.quotient {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (i : G ⟶ F) : TopCat.Sheaf CommGrpCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X) commGroupAddCommGroupEquivalence.inverse).obj
    (CategoryTheory.Limits.cokernel
      ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        commGroupAddCommGroupEquivalence.functor).map i))

/-- The quotient map `F ⟶ F/G`. -/

noncomputable def TopCat.Sheaf.quotientπ {X : TopCat.{u}} {F G : TopCat.Sheaf CommGrpCat.{u} X}
    (i : G ⟶ F) : F ⟶ TopCat.Sheaf.quotient i :=
  CategoryTheory.ObjectProperty.homMk
      (Y := (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        commGroupAddCommGroupEquivalence.inverse).obj
        ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
          commGroupAddCommGroupEquivalence.functor).obj F))
      (CategoryTheory.Functor.whiskerLeft F.obj commGroupAddCommGroupEquivalence.unit) ≫
    (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      commGroupAddCommGroupEquivalence.inverse).map
      (CategoryTheory.Limits.cokernel.π
        ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
          commGroupAddCommGroupEquivalence.functor).map i))

end
