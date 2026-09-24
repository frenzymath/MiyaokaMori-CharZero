import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite residue-field extensions of finite scheme morphisms

For a locally quasi-finite morphism, the actual residue-field map at every point
is finite. Quasi-finiteness of the stalk map passes through the residue quotient
and descends along the residue map of the base stalk. Over the resulting residue
field, quasi-finiteness implies module finiteness.

The finite-morphism corollary supplies the field extension used by the affine
weighted-point lift of Lemma 3.1 of the paper. It applies to
arbitrary points and does not assert module finiteness of the stalk map.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A locally quasi-finite morphism induces a finite extension of the actual residue fields. -/
theorem residueFieldMap_finite_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    (f.residueFieldMap x).hom.Finite := by
  have hq : (f.residueFieldMap x).hom.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := IsLocalRing.residue (Y.presheaf.stalk (f x)))
    change ((IsLocalRing.ResidueField.map (f.stalkMap x).hom).comp _).QuasiFinite
    rw [IsLocalRing.ResidueField.map_comp_residue]
    exact (RingHom.QuasiFinite.of_finite
      (RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective)).comp
        (f.quasiFiniteAt x)
  letI := (f.residueFieldMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.residueField (f x)) (X.residueField x) := hq
  exact Module.Finite.of_quasiFinite

/-- A finite morphism induces a finite extension of residue fields at every point. -/
theorem residueFieldMap_finite_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] (x : X) :
    (f.residueFieldMap x).hom.Finite :=
  residueFieldMap_finite_of_locallyQuasiFinite f x

end AlgebraicGeometry.Scheme
