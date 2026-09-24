import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree
import Mathlib.Algebra.Algebra.Tower

/-!
# Compatibility of the actual residue fields over the base field

The residue-field map of a morphism over a field respects the two actual maps
from that field. This follows from the naturality of the maps from residue-field
spectra and the original commuting triangle. The three induced algebra
structures therefore form a scalar tower.

The base maps are the existing `pointBaseMap`; neither the fields nor their
structure maps are replaced. No finite-type, dimension, algebraicity, or
finiteness conclusion is assumed or proved in this file. These compatibility
proofs supply the same-field tower in MAIN C2's transcendence-degree argument.

Sources: Stacks Project, `varieties.tex`, Lemma `dimension-locally-algebraic`
(Tag 0A21), and `chow.tex`, Lemma `equal-dimension` (Tag 02R1); Mathlib's
residue-field spectrum naturality and `IsScalarTower.of_algebraMap_eq'`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- The actual residue-field map respects the two specified maps from the base field. -/
theorem pointBaseMap_residueFieldMap
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme) :
    pointBaseMap Y.toBase (f x) ≫ f.residueFieldMap x =
      pointBaseMap X.toBase x := by
  apply Spec.map_injective
  simp only [Spec.map_comp, pointBaseMap, Spec.map_preimage]
  rw [← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x,
    Category.assoc, hf]

/-- The three actual structure maps give the residue fields a compatible scalar tower. -/
theorem residueFieldBase_isScalarTower
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme) :
    letI : Algebra k (Y.scheme.residueField (f x)) :=
      (pointBaseMap Y.toBase (f x)).hom.toAlgebra
    letI : Algebra k (X.scheme.residueField x) :=
      (pointBaseMap X.toBase x).hom.toAlgebra
    letI : Algebra (Y.scheme.residueField (f x)) (X.scheme.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower k (Y.scheme.residueField (f x)) (X.scheme.residueField x) := by
  let : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  let : Algebra k (X.scheme.residueField x) :=
    (pointBaseMap X.toBase x).hom.toAlgebra
  let : Algebra (Y.scheme.residueField (f x)) (X.scheme.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change (pointBaseMap X.toBase x).hom =
    (f.residueFieldMap x).hom.comp (pointBaseMap Y.toBase (f x)).hom
  exact congrArg CommRingCat.Hom.hom (pointBaseMap_residueFieldMap f hf x).symm

end AlgebraicGeometry.Intersection
