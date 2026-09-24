import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseTower
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Residue-field equivalences over the specified base field

An isomorphism on the actual residue fields of a morphism over `k` respects
the existing `pointBaseMap` maps from `k`. It therefore gives an equivalence
of `k`-algebras and preserves transcendence degree over this same field.

Open immersions already induce residue-field isomorphisms. For closed
immersions, surjectivity on stalks descends through the actual residue
quotients; injectivity of a field homomorphism then gives the isomorphism.
These two cases serve affine charts and the inclusions of the actual reduced
point closures in MAIN C2. No dimension formula or finiteness of an arbitrary
residue-field extension is assumed or asserted here.

Sources: Stacks, reduced closed subschemes (01J3), dimension of locally
algebraic schemes (0A21), and equal-dimension pushforward (02R1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- Surjectivity of the actual stalk map descends to the actual residue-field map. -/
theorem residueFieldMap_surjective_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, ht⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  have h := congrArg (fun m : Y.presheaf.stalk (f x) ⟶ X.residueField x => m t)
    (Scheme.residue_residueFieldMap f x)
  simpa only [CommRingCat.comp_apply, ht] using h

/-- An open immersion induces an isomorphism on the actual residue fields. -/
theorem residueFieldMap_isIso_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  infer_instance

/-- An actual residue-field isomorphism of a morphism over `k` is an equivalence over that `k`. -/
def residueFieldMapAlgEquiv
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme)
    [IsIso (f.residueFieldMap x)] :
    letI : Algebra k (Y.scheme.residueField (f x)) :=
      (pointBaseMap Y.toBase (f x)).hom.toAlgebra
    letI : Algebra k (X.scheme.residueField x) :=
      (pointBaseMap X.toBase x).hom.toAlgebra
    Y.scheme.residueField (f x) ≃ₐ[k] X.scheme.residueField x := by
  letI : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  letI : Algebra k (X.scheme.residueField x) :=
    (pointBaseMap X.toBase x).hom.toAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv) ?_
  intro t
  change (f.residueFieldMap x).hom
      ((pointBaseMap Y.toBase (f x)).hom t) =
    (pointBaseMap X.toBase x).hom t
  exact congrArg
    (fun m : CommRingCat.of k ⟶ X.scheme.residueField x ↦ m.hom t)
    (pointBaseMap_residueFieldMap f hf x)

/-- The algebra equivalence has precisely the original residue-field map as its function. -/
theorem residueFieldMapAlgEquiv_apply
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme)
    [IsIso (f.residueFieldMap x)]
    (z : Y.scheme.residueField (f x)) :
    letI : Algebra k (Y.scheme.residueField (f x)) :=
      (pointBaseMap Y.toBase (f x)).hom.toAlgebra
    letI : Algebra k (X.scheme.residueField x) :=
      (pointBaseMap X.toBase x).hom.toAlgebra
    residueFieldMapAlgEquiv f hf x z = f.residueFieldMap x z := rfl

/-- An actual residue-field isomorphism preserves transcendence degree over the specified base. -/
theorem residueFieldMap_trdeg_eq
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme)
    [IsIso (f.residueFieldMap x)] :
    letI : Algebra k (Y.scheme.residueField (f x)) :=
      (pointBaseMap Y.toBase (f x)).hom.toAlgebra
    letI : Algebra k (X.scheme.residueField x) :=
      (pointBaseMap X.toBase x).hom.toAlgebra
    Algebra.trdeg k (Y.scheme.residueField (f x)) =
      Algebra.trdeg k (X.scheme.residueField x) := by
  letI : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  letI : Algebra k (X.scheme.residueField x) :=
    (pointBaseMap X.toBase x).hom.toAlgebra
  exact (residueFieldMapAlgEquiv f hf x).trdeg_eq

end AlgebraicGeometry.Intersection
