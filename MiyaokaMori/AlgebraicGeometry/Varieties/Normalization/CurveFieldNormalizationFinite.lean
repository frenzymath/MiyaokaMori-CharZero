import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finiteness of the same function-field normalization

The nonempty-open sections of the actual extension-field spectrum are identified
with the specified field `L`, compatibly with the maps from the original scheme.
This identifies the affine sections of `curveFieldNormalization X L` with the
integral closure of the same affine coordinate ring in `L`.

For a finite separable extension of the function field, integral closure is finite
over a Noetherian integrally closed domain. Applying this on affine opens proves
that the already constructed normalization projection is finite. The empty open
is handled separately; no finiteness hypothesis on the projection is assumed.

Used for the generic weighted lift and the ramified cover (§3 of the paper). For a smooth
connected curve, integrality and the integral closedness of the affine section rings are
supplied separately.

Source: Stacks Project, `algebra.tex`,
`lemma-Noetherian-normal-domain-finite-separable-extension`, and `morphisms.tex`,
`definition-normalization-X-in-Y`. No smoothness or projectivity of the constructed
normalization is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Covers

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (L : Type u) [Field L] [Algebra X.functionField L]

/-- Sections of the extension-field spectrum over a nonempty base open are the
same field `L`, using the actual equality of its inverse image with the whole spectrum. -/
def curveExtensionSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec (CommRingCat.of L), curveExtensionGenericMap X L ⁻¹ᵁ U) ≅ CommRingCat.of L :=
  (Spec (CommRingCat.of L)).presheaf.mapIso
    (eqToIso (curveExtensionGenericMap_preimage_of_nonempty X L U).symm).op ≪≫
      Scheme.ΓSpecIso (CommRingCat.of L)

set_option backward.isDefEq.respectTransparency false in
/-- The section identification respects the original map through `K(X) → L`. -/
theorem curveExtensionGenericMap_app_sectionsIso (U : X.Opens) [Nonempty U] :
    (curveExtensionGenericMap X L).app U ≫ (curveExtensionSectionsIso X L U).hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
  have hU : curveExtensionGenericMap X L (IsLocalRing.closedPoint L) ∈ U := by
    rw [curveExtensionGenericMap_apply]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  calc
    _ = X.presheaf.germ U _ hU ≫
        Scheme.stalkClosedPointTo (curveExtensionGenericMap X L) :=
      (Scheme.germ_stalkClosedPointTo (curveExtensionGenericMap X L) U hU).symm
    _ = _ := by
      simpa only [curveExtensionGenericMap, Scheme.germToFunctionField] using
        Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
          (CommRingCat.ofHom (algebraMap X.functionField L)) U hU

/-- The canonical scalar structure on `L` from a nonempty open, via its generic germ. -/
def curveExtensionSectionAlgebra (U : X.Opens) [Nonempty U] : Algebra Γ(X, U) L :=
  ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The section identification is an equivalence over the actual affine coordinate ring. -/
def curveExtensionSectionsAlgEquiv (U : X.Opens) [Nonempty U] :
    letI := curveExtensionSectionAlgebra X L U
    letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
    Γ(Spec (CommRingCat.of L), curveExtensionGenericMap X L ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L := by
  letI := curveExtensionSectionAlgebra X L U
  letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
  refine
    { toRingEquiv := (curveExtensionSectionsIso X L U).commRingCatIsoToRingEquiv
      commutes' := ?_ }
  intro a
  change ((curveExtensionGenericMap X L).app U ≫ (curveExtensionSectionsIso X L U).hom) a =
    (X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L)) a
  exact congrArg (fun f : Γ(X, U) ⟶ CommRingCat.of L ↦ f a)
    (curveExtensionGenericMap_app_sectionsIso X L U)

/-- On a nonempty affine open, the same normalization has the integral-closure
coordinate ring in the specified field `L`. -/
def curveFieldNormalizationSectionsFieldIso (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := curveExtensionSectionAlgebra X L U
    Γ(curveFieldNormalization X L, curveFieldNormalizationMap X L ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U) L) := by
  letI := curveExtensionSectionAlgebra X L U
  letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
  exact curveFieldNormalizationSectionsIso X L U hU ≪≫
    (curveExtensionSectionsAlgEquiv X L U).mapIntegralClosure.toRingEquiv.toCommRingCatIso

set_option backward.isDefEq.respectTransparency false in
/-- Under the affine integral-closure identification, the projection is the canonical
inclusion of the original affine coordinate ring. -/
theorem curveFieldNormalizationMap_app_sectionsFieldIso
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := curveExtensionSectionAlgebra X L U
    (curveFieldNormalizationMap X L).app U ≫
        (curveFieldNormalizationSectionsFieldIso X L U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) := by
  letI := curveExtensionSectionAlgebra X L U
  letI := ((curveExtensionGenericMap X L).app U).hom.toAlgebra
  change (curveExtensionGenericMap X L).fromNormalization.app U ≫
      ((curveExtensionGenericMap X L).normalizationObjIso hU).hom ≫
        (curveExtensionSectionsAlgEquiv X L U).mapIntegralClosure.toRingEquiv.toCommRingCatIso.hom =
    CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L))
  rw [(curveExtensionGenericMap X L).fromNormalization_app hU]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext a
  exact congrArg Subtype.val ((curveExtensionSectionsAlgEquiv X L U).mapIntegralClosure.commutes a)

variable [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]

/-- A nonempty affine chart of the same normalization is finite over a Noetherian,
integrally closed affine coordinate ring. -/
theorem curveFieldNormalizationMap_finite_app
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsNoetherianRing Γ(X, U)] [IsIntegrallyClosed Γ(X, U)] :
    ((curveFieldNormalizationMap X L).app U).hom.Finite := by
  let := curveExtensionSectionAlgebra X L U
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) :=
    IsIntegralClosure.finite Γ(X, U) X.functionField L (integralClosure Γ(X, U) L)
  let e := curveFieldNormalizationSectionsFieldIso X L U hU
  have he : (curveFieldNormalizationMap X L).app U =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) ≫ e.inv := by
    rw [← curveFieldNormalizationMap_app_sectionsFieldIso X L U hU]
    simp only [Category.assoc, e, Iso.hom_inv_id, Category.comp_id]
  rw [he, CommRingCat.hom_comp]
  exact e.commRingCatIsoToRingEquiv.symm.finite.comp
    (RingHom.finite_algebraMap.mpr inferInstance)

/-- A finite separable extension gives a finite projection from the actual normalization
when the original scheme is locally Noetherian with integrally closed nonempty affine sections.
These are properties of the original scheme, not finiteness data for the target projection. -/
theorem curveFieldNormalizationMap_finite [IsLocallyNoetherian X]
    (hNormal : ∀ U : X.affineOpens, Nonempty U → IsIntegrallyClosed Γ(X, U)) :
    AlgebraicGeometry.IsFinite (curveFieldNormalizationMap X L) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · have : Nonempty U := hne
    have : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : IsIntegrallyClosed Γ(X, U) := hNormal ⟨U, hU⟩ hne
    exact curveFieldNormalizationMap_finite_app X L U hU
  · have hUbot : U = ⊥ := (Opens.not_nonempty_iff_eq_bot U).mp
      fun h ↦ hne (Opens.nonempty_coeSort.mpr h)
    subst U
    haveI : Subsingleton Γ(curveFieldNormalization X L,
        curveFieldNormalizationMap X L ⁻¹ᵁ (⊥ : X.Opens)) :=
      inferInstanceAs (Subsingleton Γ(curveFieldNormalization X L,
        (⊥ : (curveFieldNormalization X L).Opens)))
    apply RingHom.Finite.of_surjective
    intro a
    exact ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme.Covers
