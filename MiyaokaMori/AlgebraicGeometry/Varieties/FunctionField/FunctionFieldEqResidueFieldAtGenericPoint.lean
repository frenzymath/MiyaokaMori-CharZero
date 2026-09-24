import MiyaokaMori.Prelude

/-! # The function field is the residue field at the generic point

The stalk of an integral scheme at its generic point is already a field, so it coincides with
the residue field at that point. This matches Mathlib's `residueDegree` at the generic point with
the degree of the function field extension (the pushforward coefficient `[K(V) : K(f V)]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance AlgebraicGeometry.Scheme.isIso_residue_genericPoint (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] :
    CategoryTheory.IsIso (X.residue (genericPoint X)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have hz : X.residue (genericPoint X) (a - b) = 0 := by
      simpa using congrArg (fun z => z - X.residue (genericPoint X) b) hab
    change IsLocalRing.residue (X.presheaf.stalk (genericPoint X)) (a - b) = 0 at hz
    rw [IsLocalRing.residue_eq_zero_iff] at hz
    simpa [IsLocalRing.maximalIdeal_eq_bot] using hz
  · exact X.residue_surjective (genericPoint X)

/-- The isomorphism between the function field of an integral scheme and the residue field at its
generic point. -/
noncomputable def AlgebraicGeometry.Scheme.functionFieldIsoResidueField (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] :
    X.functionField ≅ X.residueField (genericPoint X) :=
  CategoryTheory.asIso (X.residue (genericPoint X))

end
