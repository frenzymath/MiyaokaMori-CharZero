import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueFieldFiniteType
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree
import Mathlib.FieldTheory.FinTrdeg

/-!+# Essential finite type over the original base field

For a point of a locally finite type scheme over a field, the actual base map
to its residue field is essentially of finite type. Naturality factors this
map through the residue field of the corresponding point of the base spectrum.
That base point is closed, so its residue field is finite over the base field;
the remaining residue map is essentially of finite type by the stalk argument.

The resulting finite transcendence degree is for exactly the algebra structure
induced by the existing `pointBaseMap`. The source point need not be closed and
its residue field need not be finite over the base field. These are ordinary
prerequisites for MAIN C2, independent of its admitted dimension comparison.

Sources: Stacks Project, Morphisms, residue fields of locally finite type
morphisms (Tag 02NX), and Varieties, dimension and transcendence degree (0A21).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- The specified map from the original base field to any residue field is essentially
of finite type. -/
theorem pointBaseMap_essFiniteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X) :
    (pointBaseMap f x).hom.EssFiniteType := by
  have hbase := pointBaseMap_finite (𝟙 (Spec (CommRingCat.of k))) (f x)
    (isClosed_singleton : IsClosed ({f x} : Set (Spec (CommRingCat.of k))))
  have hcomp : pointBaseMap (𝟙 (Spec (CommRingCat.of k))) (f x) ≫
      f.residueFieldMap x = pointBaseMap f x := by
    apply Spec.map_injective
    simp only [Spec.map_comp, pointBaseMap, Spec.map_preimage, Category.comp_id]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x
  have h := hbase.finiteType.essFiniteType.comp (residueFieldMap_essFiniteType f x)
  change ((pointBaseMap (𝟙 (Spec (CommRingCat.of k))) (f x) ≫
    f.residueFieldMap x).hom).EssFiniteType at h
  simpa only [hcomp] using h

/-- The same actual base map gives the residue field finite transcendence degree. -/
theorem pointBaseMap_finTrdeg {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) := (pointBaseMap f x).hom.toAlgebra
    FinTrdeg k (X.residueField x) := by
  letI : Algebra k (X.residueField x) := (pointBaseMap f x).hom.toAlgebra
  have : Algebra.EssFiniteType k (X.residueField x) := pointBaseMap_essFiniteType f x
  infer_instance

end AlgebraicGeometry.Intersection
