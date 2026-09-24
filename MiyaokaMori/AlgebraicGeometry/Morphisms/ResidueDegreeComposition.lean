import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Residue degree of a composite scheme morphism

The residue fields attached to two composable scheme morphisms form the actual scalar tower
induced by their residue-field maps.  The resulting `Module.finrank` tower identity gives
multiplicativity of Mathlib's existing `Scheme.Hom.residueDegree`.  This is a pointwise algebra
fact; no properness, finite-type, dominance, or finiteness hypothesis is needed.  In particular,
the theorem retains Mathlib's definition, which returns `0` when the relevant finrank is infinite.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- The actual residue maps of two composable morphisms form a scalar tower. -/
theorem residueFieldComp_isScalarTower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    letI : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
      (g.residueFieldMap (f x)).hom.toAlgebra
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
      ((f ≫ g).residueFieldMap x).hom.toAlgebra
    IsScalarTower (Z.residueField (g (f x)))
      (Y.residueField (f x)) (X.residueField x) := by
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change ((f ≫ g).residueFieldMap x).hom =
    (f.residueFieldMap x).hom.comp (g.residueFieldMap (f x)).hom
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)

/-- Residue degrees multiply along a composite of the actual scheme morphisms. -/
theorem residueDegree_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x =
      g.residueDegree (f x) * f.residueDegree x := by
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have hTower : IsScalarTower (Z.residueField (g (f x)))
      (Y.residueField (f x)) (X.residueField x) :=
    residueFieldComp_isScalarTower f g x
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank
    (Z.residueField (g (f x))) (Y.residueField (f x)) (X.residueField x)).symm

end AlgebraicGeometry.Intersection
