import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Essential finite type of the actual residue-field extension

For a locally finite type morphism, the stalk map is essentially of finite type,
and the actual map of residue fields inherits that property. The over-field
adapter uses the given commuting triangle to obtain local finite type of the map.

These ordinary helpers do not assert finiteness of the residue extension. The
dimension-preserving pushforward theorem still needs the dimension/transcendence
degree comparison and algebraicity over the same residue field. In particular,
the residue field at a generic point need not be a finite type algebra over the
original base field.

Sources: Mathlib's stalk and residue essential-finite-type theorems; Stacks
Project, `morphisms.tex`, Lemma `finite-degree` (Tag 02NX). This is a proof
prerequisite of MAIN C2, not a construction from its admitted existence theorem.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- The actual residue-field map of a locally finite type morphism is essentially of finite type. -/
theorem residueFieldMap_essFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    (f.residueFieldMap x).hom.EssFiniteType := by
  change (IsLocalRing.ResidueField.map (f.stalkMap x).hom).EssFiniteType
  exact (LocallyOfFiniteType.stalkMap f x).residueFieldMap

/-- Local finite type of the source over the base field suffices for the actual residue map. -/
theorem overBase_residueFieldMap_essFiniteType {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Proj.SchemeOver k} (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase)
    [LocallyOfFiniteType X.toBase] (x : X.scheme) :
    (f.residueFieldMap x).hom.EssFiniteType := by
  have : LocallyOfFiniteType (f ≫ Y.toBase) := by
    rw [hf]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f Y.toBase
  exact residueFieldMap_essFiniteType f x

end AlgebraicGeometry.Intersection
