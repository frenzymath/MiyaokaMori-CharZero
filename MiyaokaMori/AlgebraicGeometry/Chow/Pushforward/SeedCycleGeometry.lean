import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureDimensionTrdeg
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldFiniteOfTrdeg
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ProperPushforward

/-!
# Residue finiteness for morphisms of finite type over a field

A morphism over one field between schemes of finite type over that field
preserves residue finiteness: equality of point-closure dimensions forces the
residue extension to be finite. The proof uses the integral reduced closures of
the point and its image (`pointClosureDimension_eq_trdeg`).

Sources: Theorem 1.1 of the paper; Stacks Tags 01W6, 0A21, 02R1 and 02NX.
-/

set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Intersection

variable {k : Type u} [Field k]

/-- A dimension-preserving point has finite residue extension under a morphism
between finite-type schemes over the same field. Finite type is expressed using
locally finite type and quasi-compact structure morphisms. No global integrality,
dominance, or nonconstancy hypothesis is imposed. -/
theorem finiteDimensionPreservingResidues_of_finiteType_over_field
    {X Y : AlgebraicGeometry.Proj.SchemeOver k} (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase)
    [LocallyOfFiniteType X.toBase] [QuasiCompact X.toBase]
    [LocallyOfFiniteType Y.toBase] [QuasiCompact Y.toBase] :
    FiniteDimensionPreservingResidues f := by
  intro x hx
  refine residueFieldMap_finite_of_trdeg_toENat_eq f hf x ?_
  letI : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
  exact (MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg Y (f x)).symm.trans
    (hx.symm.trans (MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg X x))

end AlgebraicGeometry.Intersection
