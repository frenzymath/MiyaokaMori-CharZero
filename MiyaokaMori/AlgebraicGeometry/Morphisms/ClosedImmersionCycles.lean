import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ProperPushforward
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Residue extensions for closed-immersion pushforward

A closed immersion induces an isomorphism of the actual residue fields. In particular its
residue extensions are finite, so the existing dimension-indexed proper pushforward applies
without an additional finiteness assumption. Its residue multiplicities are all one.

The B1 first-Chern-class relation uses this for the closed integral curves in a presentation
of a one-cycle. Sources: Stacks Project, Tags 02R4 and 02SO.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Intersection

universe u

variable {X Y : Scheme.{u}}

/-- A closed immersion is surjective on the actual residue fields. -/
theorem closedImmersion_residueFieldMap_surjective (i : X ⟶ Y) [IsClosedImmersion i]
    (x : X) : Function.Surjective (i.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, ht⟩ := i.stalkMap_surjective x s
  refine ⟨Y.residue (i x) t, ?_⟩
  have h := congrArg (fun g : Y.presheaf.stalk (i x) ⟶ X.residueField x => g t)
    (Scheme.residue_residueFieldMap i x)
  simpa only [CommRingCat.comp_apply, ht] using h

/-- A closed immersion induces a bijection of the actual residue fields. -/
theorem closedImmersion_residueFieldMap_bijective (i : X ⟶ Y) [IsClosedImmersion i]
    (x : X) : Function.Bijective (i.residueFieldMap x) :=
  ⟨(i.residueFieldMap x).hom.injective, closedImmersion_residueFieldMap_surjective i x⟩

/-- The actual residue-field morphism of a closed immersion is an isomorphism. -/
theorem closedImmersion_residueFieldMap_isIso (i : X ⟶ Y) [IsClosedImmersion i]
    (x : X) : IsIso (i.residueFieldMap x) :=
  (RingEquiv.ofBijective (i.residueFieldMap x).hom
    (closedImmersion_residueFieldMap_bijective i x)).toCommRingCatIso.isIso_hom

/-- Every residue extension of a closed immersion is finite. -/
theorem closedImmersion_residueFieldMap_finite (i : X ⟶ Y) [IsClosedImmersion i]
    (x : X) : (i.residueFieldMap x).hom.Finite :=
  RingHom.Finite.of_surjective _ (closedImmersion_residueFieldMap_surjective i x)

/-- The genuine residue-field degree of a closed immersion is one. -/
theorem closedImmersion_residueDegree_eq_one (i : X ⟶ Y) [IsClosedImmersion i]
    (x : X) : i.residueDegree x = 1 := by
  let : Algebra (Y.residueField (i x)) (X.residueField x) :=
    (i.residueFieldMap x).hom.toAlgebra
  change Module.finrank (Y.residueField (i x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap (closedImmersion_residueFieldMap_bijective i x)

/-- Closed immersions supply the finiteness required by `dimensionProperPushforward`. -/
theorem closedImmersion_finiteDimensionPreservingResidues (i : X ⟶ Y) [IsClosedImmersion i] :
    FiniteDimensionPreservingResidues i := by
  intro x _
  exact closedImmersion_residueFieldMap_finite i x

end AlgebraicGeometry.Intersection
