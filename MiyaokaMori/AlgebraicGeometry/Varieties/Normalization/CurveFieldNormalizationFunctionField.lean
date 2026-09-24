import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalizationFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FiniteCurveField
import Mathlib.RingTheory.Localization.Integral

/-!
# The actual function field of normalization in a finite extension

The canonical map from the generic stalk of `curveFieldNormalization X L` to `L`
is extracted from the already constructed morphism `Spec L → normalization`.
Its restriction to every lifted nonempty affine chart is the inclusion of that
chart's integral closure into `L`. Both rings have the expected fraction fields,
so this particular map is bijective when `L / X.functionField` is finite.

The resulting equivalence is over the function-field map of the same normalization
projection, and recovers the actual morphism from `Spec L`. No separability,
normality or Noetherian hypothesis on `X` is needed for this identification.
Finiteness, normality and the smooth projective curve properties of the scheme
remain separate geometric obligations.

Used for the rational coordinates and the ramified extension (§3 of the paper). Sources: the
integral-closure charts of
Stacks Project's relative normalization, and the fact that the integral closure
in an algebraic extension has that extension as its fraction field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Covers

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (L : Type u) [Field L] [Algebra X.functionField L]

/-- The unique point of `Spec L` maps to the generic point of the same normalization. -/
theorem curveFieldNormalizationGenericMap_closedPoint :
    curveFieldNormalizationGenericMap X L (IsLocalRing.closedPoint L) =
      genericPoint (curveFieldNormalization X L) := by
  have h : IsLocalRing.closedPoint L = genericPoint (Spec (CommRingCat.of L)) :=
    Subsingleton.elim _ _
  rw [h]
  exact dominantMap_genericPoint (curveFieldNormalizationGenericMap X L)

/-- The map of the generic stalk to `L` induced by the actual normalization factorization. -/
def curveFieldNormalizationFunctionFieldMap :
    (curveFieldNormalization X L).functionField ⟶ CommRingCat.of L :=
  ((curveFieldNormalization X L).presheaf.stalkCongr
      (.of_eq (curveFieldNormalizationGenericMap_closedPoint X L).symm)).hom ≫
    Scheme.stalkClosedPointTo (curveFieldNormalizationGenericMap X L)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical field map recovers the already specified `Spec L → normalization`. -/
theorem curveFieldNormalizationFunctionFieldMap_factorization :
    Spec.map (curveFieldNormalizationFunctionFieldMap X L) ≫
        (curveFieldNormalization X L).fromSpecStalk
          (genericPoint (curveFieldNormalization X L)) =
      curveFieldNormalizationGenericMap X L := by
  simp only [curveFieldNormalizationFunctionFieldMap, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map is compatible with the function-field map of the same projection. -/
theorem curveFieldNormalizationFunctionFieldMap_comp :
    dominantFunctionFieldMap (curveFieldNormalizationMap X L) ≫
        curveFieldNormalizationFunctionFieldMap X L =
      CommRingCat.ofHom (algebraMap X.functionField L) := by
  have hν :
      Spec.map (dominantFunctionFieldMap (curveFieldNormalizationMap X L)) ≫
          X.fromSpecStalk (genericPoint X) =
        (curveFieldNormalization X L).fromSpecStalk
            (genericPoint (curveFieldNormalization X L)) ≫
          curveFieldNormalizationMap X L := by
    simp only [dominantFunctionFieldMap, Spec.map_comp, Category.assoc,
      TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  rw [Spec.map_comp, Category.assoc, hν, ← Category.assoc,
    curveFieldNormalizationFunctionFieldMap_factorization, curveFieldNormalization_factorization]
  rfl

/-- A nonempty base open lifts to a nonempty open of this same normalization. -/
theorem curveFieldNormalizationMap_preimage_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty (curveFieldNormalizationMap X L ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint (curveFieldNormalization X L), ?_⟩⟩
  change curveFieldNormalizationMap X L (genericPoint (curveFieldNormalization X L)) ∈ U
  rw [dominantMap_genericPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))

set_option backward.isDefEq.respectTransparency false in
private theorem curveExtensionSectionsIso_eq_germ (U : X.Opens) [Nonempty U]
    (hU : IsLocalRing.closedPoint L ∈ curveExtensionGenericMap X L ⁻¹ᵁ U) :
    (curveExtensionSectionsIso X L U).hom =
      (Spec (CommRingCat.of L)).presheaf.germ
          (curveExtensionGenericMap X L ⁻¹ᵁ U) (IsLocalRing.closedPoint L) hU ≫
        (stalkClosedPointIso (CommRingCat.of L)).hom := by
  dsimp only [curveExtensionSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom]
  rw [← germ_stalkClosedPointIso_hom, ← Category.assoc, TopCat.Presheaf.germ_res']

set_option backward.isDefEq.respectTransparency false in
/-- On each nonempty affine chart, the canonical generic-stalk map is exactly the
inclusion of the chart's integral closure into the specified field. -/
theorem curveFieldNormalizationFunctionFieldMap_germ
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := curveExtensionSectionAlgebra X L U
    letI := curveFieldNormalizationMap_preimage_nonempty X L U
    (curveFieldNormalization X L).germToFunctionField
          (curveFieldNormalizationMap X L ⁻¹ᵁ U) ≫
        curveFieldNormalizationFunctionFieldMap X L =
      (curveFieldNormalizationSectionsFieldIso X L U hU).hom ≫
        CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) L) L) := by
  letI := curveExtensionSectionAlgebra X L U
  letI := curveFieldNormalizationMap_preimage_nonempty X L U
  letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
  let V := curveFieldNormalizationMap X L ⁻¹ᵁ U
  let W := curveExtensionGenericMap X L ⁻¹ᵁ U
  have hWV : W ≤ curveFieldNormalizationGenericMap X L ⁻¹ᵁ V := by
    dsimp only [W, V]
    rw [← Scheme.Hom.comp_preimage, curveFieldNormalization_factorization]
  have hW : IsLocalRing.closedPoint L ∈ W := by
    change curveExtensionGenericMap X L (IsLocalRing.closedPoint L) ∈ U
    rw [curveExtensionGenericMap_apply]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  have hchart :
      (curveFieldNormalizationSectionsFieldIso X L U hU).hom ≫
          CommRingCat.ofHom (algebraMap (integralClosure Γ(X, U) L) L) =
        (curveFieldNormalizationGenericMap X L).appLE V W hWV ≫
          (curveExtensionSectionsIso X L U).hom := by
    calc
      _ = ((curveExtensionGenericMap X L).normalizationObjIso hU).hom ≫
          CommRingCat.ofHom (Subalgebra.val
            (integralClosure Γ(X, U) Γ(Spec (CommRingCat.of L), W))).toRingHom ≫
          (curveExtensionSectionsIso X L U).hom := by
        ext a
        rfl
      _ = _ := by
        rw [← Category.assoc,
          (curveExtensionGenericMap X L).normalizationObjIso_hom_val hU]
        rfl
  rw [hchart, curveExtensionSectionsIso_eq_germ X L U hW]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res_assoc,
    ← Scheme.Hom.germ_stalkMap_assoc]
  simp only [curveFieldNormalizationFunctionFieldMap, Scheme.germToFunctionField,
    Scheme.stalkClosedPointTo, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes_assoc]
  rw [Scheme.Hom.germ_stalkMap_assoc, TopCat.Presheaf.germ_res'_assoc]

/-- The actual field map is injective, including for extensions not assumed finite. -/
theorem curveFieldNormalizationFunctionFieldMap_injective :
    Function.Injective (curveFieldNormalizationFunctionFieldMap X L) :=
  (curveFieldNormalizationFunctionFieldMap X L).hom.injective

/-- The canonical map as an algebra homomorphism for the projection's own scalar structure. -/
def curveFieldNormalizationFunctionFieldAlgHom :
    letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
    (curveFieldNormalization X L).functionField →ₐ[X.functionField] L := by
  letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
  refine { toRingHom := (curveFieldNormalizationFunctionFieldMap X L).hom, commutes' := ?_ }
  intro a
  change (dominantFunctionFieldMap (curveFieldNormalizationMap X L) ≫
      curveFieldNormalizationFunctionFieldMap X L) a =
    (CommRingCat.ofHom (algebraMap X.functionField L)) a
  exact congrArg (fun f : X.functionField ⟶ CommRingCat.of L ↦ f a)
    (curveFieldNormalizationFunctionFieldMap_comp X L)

variable [FiniteDimensional X.functionField L]

set_option backward.isDefEq.respectTransparency false in
/-- For a finite extension, the canonical generic-stalk map is bijective. The proof
uses one nonempty affine chart only to verify this property of the already defined map. -/
theorem curveFieldNormalizationFunctionFieldMap_bijective :
    Function.Bijective (curveFieldNormalizationFunctionFieldMap X L) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI := curveFieldNormalizationMap_preimage_nonempty X L U
  letI := curveExtensionSectionAlgebra X L U
  letI : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing (integralClosure Γ(X, U) L) L :=
    integralClosure.isFractionRing_of_finite_extension X.functionField L
  let V := curveFieldNormalizationMap X L ⁻¹ᵁ U
  letI : IsFractionRing Γ(curveFieldNormalization X L, V)
      (curveFieldNormalization X L).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ V
      (hU.preimage (curveFieldNormalizationMap X L))
  let e : (curveFieldNormalization X L).functionField ≃+* L :=
    IsFractionRing.ringEquivOfRingEquiv
      (curveFieldNormalizationSectionsFieldIso X L U hU).commRingCatIsoToRingEquiv
  have he : (curveFieldNormalizationFunctionFieldMap X L).hom = e.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := Γ(curveFieldNormalization X L, V))
    intro a
    rw [show e.toRingHom (algebraMap Γ(curveFieldNormalization X L, V)
        (curveFieldNormalization X L).functionField a) =
        algebraMap (integralClosure Γ(X, U) L) L
          ((curveFieldNormalizationSectionsFieldIso X L U hU).hom a) from
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a]
    exact congrArg
      (fun f : Γ(curveFieldNormalization X L, V) ⟶ CommRingCat.of L ↦ f a)
      (curveFieldNormalizationFunctionFieldMap_germ X L U hU)
  change Function.Bijective (curveFieldNormalizationFunctionFieldMap X L).hom
  rw [he]
  exact e.bijective

/-- The specified finite extension is the actual function field of this same normalization,
with the scalar structure induced by its canonical projection. -/
def curveFieldNormalizationFunctionFieldEquiv :
    letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
    (curveFieldNormalization X L).functionField ≃ₐ[X.functionField] L := by
  letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
  exact AlgEquiv.ofBijective (curveFieldNormalizationFunctionFieldAlgHom X L)
    (curveFieldNormalizationFunctionFieldMap_bijective X L)

/-- The equivalence's underlying map is the canonical map extracted from the actual morphism. -/
theorem curveFieldNormalizationFunctionFieldEquiv_toRingHom :
    letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
    CommRingCat.ofHom (curveFieldNormalizationFunctionFieldEquiv X L).toRingHom =
      curveFieldNormalizationFunctionFieldMap X L := rfl

/-- This specific equivalence, without a field-automorphism ambiguity, gives the
original generic-point morphism of the relative normalization. -/
theorem curveFieldNormalizationFunctionFieldEquiv_factorization :
    letI := dominantFunctionFieldAlgebra (curveFieldNormalizationMap X L)
    Spec.map (CommRingCat.ofHom (curveFieldNormalizationFunctionFieldEquiv X L).toRingHom) ≫
        (curveFieldNormalization X L).fromSpecStalk
          (genericPoint (curveFieldNormalization X L)) =
      curveFieldNormalizationGenericMap X L := by
  rw [curveFieldNormalizationFunctionFieldEquiv_toRingHom]
  exact curveFieldNormalizationFunctionFieldMap_factorization X L

end AlgebraicGeometry.Scheme.Covers
