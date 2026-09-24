import MiyaokaMori.Prelude

/-! # Pullback of the structure sheaf, restriction and pullback, and the free sheaf on a point

1. For any morphism of schemes `f : X ⟶ Y`, `f^*O_Y ≅ O_X` (`pullbackUnitIso`, an explicit
   isomorphism whose forward map is Mathlib's `pullbackObjUnitToUnit`: `pullbackUnitIso_hom`).
2. Restriction commutes with pullback: `(f^*M)|_{f⁻¹U} ≅ (f|_U)^*(M|_U)` (`pullbackRestrictIso`).
3. `O_X` is isomorphic to the free sheaf on a one-point index set (`unitIsoFreePUnit`).

These three facts are all the categorical input for "the pullback of a line bundle is a line
bundle" and "line bundles are locally free of finite type", independently of how line bundles are
encoded (no `IsLineBundle` appears). `pullbackUnitIso` and the instance `opensMap_final` are
defined only here.

Reference: the remark after Stacks 01CR; Mathlib `SheafOfModules.pullbackObjUnitToUnit` (an
isomorphism when the underlying functor is final).
-/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The preimage functor `Opens.map f.base` is final (the hypothesis of Mathlib's instance
`IsIso (pullbackObjUnitToUnit φ)`). -/
instance opensMap_final (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun _ ↦ ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

/-- `f^*O_Y ≅ O_X` (Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, an isomorphism since the
underlying functor is final). This is the only definition of this isomorphism in the library. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  @asIso (SheafOfModules.{u} X.ringCatSheaf) _ _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom)

/-- The forward map of `pullbackUnitIso` is Mathlib's canonical map `pullbackObjUnitToUnit`
(`IsRightAdjoint` is a `Prop`, so the instance supplied here is irrelevant). -/
theorem pullbackUnitIso_hom (f : X ⟶ Y) :
    haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
      (pullbackPushforwardAdjunction f).isRightAdjoint
    (pullbackUnitIso f).hom = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := rfl

/-- Restriction commutes with pullback: `(f^*M)|_{f⁻¹U} ≅ (f|_U)^*(M|_U)`. -/
def pullbackRestrictIso (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅ (pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (pullback (f ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).app M).symm

/-- Pullback of a local trivialization: `M|_U ≅ O_U` implies `(f^*M)|_{f⁻¹U} ≅ O_{f⁻¹U}`. -/
def pullbackTrivializationIso (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens}
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  pullbackRestrictIso f M U ≪≫ (pullback (f ∣_ U)).mapIso e ≪≫ pullbackUnitIso _

/-- `O_X` is isomorphic to the free sheaf on a one-point index set. -/
def unitIsoFreePUnit (X : Scheme.{u}) :
    SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} :=
  (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.ringCatSheaf)).symm

end AlgebraicGeometry.Scheme.Modules

end
