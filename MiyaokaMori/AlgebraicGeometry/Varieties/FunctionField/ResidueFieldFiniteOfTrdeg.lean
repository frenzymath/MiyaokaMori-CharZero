import MiyaokaMori.RingTheory.Dimension.FiniteExtensionOfTrdeg
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseTower
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finiteness of the actual residue map from equal transcendence degrees

The two residue fields carry the algebra structures induced by the existing
base maps, and their relative algebra is induced by the actual residue map.
Naturality supplies the compatible scalar tower. Local finite type gives
essential finite type and finite transcendence degree, so equality after
`Cardinal.toENat` can be lifted back to equality of finite cardinals. The
field-extension theorem then proves finiteness of this same residue map.

This is the final algebra adapter for MAIN C2. Its explicit transcendence-degree
equality must still come from the geometric point-closure dimension argument;
it is not an additional hypothesis of the original milestone or of MAIN.
Sources: Stacks Project, Chow, equal-dimension (02R1), and Morphisms,
finite-degree (02NX).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- Equal residue transcendence degrees, measured in the geometric dimension codomain,
make the actual residue map finite for a morphism of locally finite type schemes over a field. -/
theorem residueFieldMap_finite_of_trdeg_toENat_eq
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k} (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.toBase = X.toBase)
    [LocallyOfFiniteType X.toBase] [LocallyOfFiniteType Y.toBase] (x : X.scheme)
    (h : letI : Algebra k (Y.scheme.residueField (f x)) :=
        (pointBaseMap Y.toBase (f x)).hom.toAlgebra
      letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg k (Y.scheme.residueField (f x))) : WithBot ℕ∞) =
        (Cardinal.toENat (Algebra.trdeg k (X.scheme.residueField x)) : WithBot ℕ∞)) :
    (f.residueFieldMap x).hom.Finite := by
  letI : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
  letI : Algebra (Y.scheme.residueField (f x)) (X.scheme.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower k (Y.scheme.residueField (f x)) (X.scheme.residueField x) :=
    residueFieldBase_isScalarTower f hf x
  have : FinTrdeg k (Y.scheme.residueField (f x)) :=
    pointBaseMap_finTrdeg Y.toBase (f x)
  have : FinTrdeg k (X.scheme.residueField x) := pointBaseMap_finTrdeg X.toBase x
  have : Algebra.EssFiniteType k (X.scheme.residueField x) :=
    pointBaseMap_essFiniteType X.toBase x
  have htr : Algebra.trdeg k (Y.scheme.residueField (f x)) =
      Algebra.trdeg k (X.scheme.residueField x) :=
    (Cardinal.toENat_eq_iff_of_le_aleph0
      (trdeg_lt_aleph0 k (Y.scheme.residueField (f x))).le
      (trdeg_lt_aleph0 k (X.scheme.residueField x)).le).mp (WithBot.coe_injective h)
  exact finite_of_essFiniteType_of_trdeg_eq k
    (Y.scheme.residueField (f x)) (X.scheme.residueField x) htr

end AlgebraicGeometry.Intersection
