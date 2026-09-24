import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree

/-! # Binary biproducts of locally free sheaves

The binary direct sum `M ⊕ N` (the `biprod` in `X.Modules`) of two locally free (resp. finite type)
`O_X`-modules is locally free (resp. of finite type): locally `M|_U ≅ O^I`, `N|_U ≅ O^J`, so
`(M ⊕ N)|_U ≅ O^{I ⊔ J}`. Registered as instances, so that `projBundle (O ⊕ L)` finds the hypothesis
`IsLocallyFree` automatically (the construction of `P(O ⊕ L)` in the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The binary biproduct of two locally free sheaves is locally free. -/
instance AlgebraicGeometry.Scheme.Modules.biprod_isLocallyFree {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules) [M.IsLocallyFree] [N.IsLocallyFree] :
    (CategoryTheory.Limits.biprod (C := X.Modules) M N).IsLocallyFree :=
by
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun x => ?_
  obtain ⟨U, I, hxU, eI⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree M x
  obtain ⟨V, J, hxV, eJ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree N x
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have eIW := eI.some
  have eJW := eJ.some
  have eIW' := (AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le M
    (V := W) (U := U) inf_le_left I eIW).some
  have eJW' := (AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le N
    (V := W) (U := V) inf_le_right J eJW).some
  let F : X.Modules ⥤ W.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι
  have hF := (AlgebraicGeometry.Scheme.Modules.restrictAdjunction W.ι).leftAdjoint_preservesColimits.{0, 0}
  letI : PreservesColimitsOfShape (Discrete WalkingPair) F := hF.preservesColimitsOfShape
  letI : PreservesBiproductsOfShape WalkingPair F :=
    preservesBiproductsOfShape_of_preservesCoproductsOfShape F
  letI : PreservesBiproduct (pairFunction M N) F := inferInstance
  letI : PreservesBinaryBiproduct M N F := preservesBinaryBiproduct_of_preservesBiproduct F M N
  let hmap : F.obj (M ⊞ N) ≅ F.obj M ⊞ F.obj N := F.mapBiprod M N
  let rM := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app M
  let rN := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app N
  let rMN := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app (M ⊞ N)
  let eIW'' : F.obj M ≅ SheafOfModules.free I := rM ≪≫ eIW'
  let eJW'' : F.obj N ≅ SheafOfModules.free J := rN ≪≫ eJW'
  let K : W.toScheme.Modules := SheafOfModules.free (R := W.toScheme.ringCatSheaf) I
  let L : W.toScheme.Modules := SheafOfModules.free (R := W.toScheme.ringCatSheaf) J
  letI : HasBinaryBiproduct (F.obj M) (F.obj N) :=
    CategoryTheory.Abelian.hasBinaryBiproducts.has_binary_biproduct _ _
  letI : HasBinaryBiproduct K L := CategoryTheory.Abelian.hasBinaryBiproducts.has_binary_biproduct _ _
  exact ⟨W, Sum I J, hxW, ⟨rMN.symm ≪≫ hmap ≪≫ biprod.mapIso eIW'' eJW'' ≪≫
    (@biprod.isoCoprod W.toScheme.Modules _ _ K L _) ≪≫
      (SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J : K ⨿ L ≅ _ )⟩⟩

/-- The binary biproduct of two sheaves of finite type is of finite type. -/
instance AlgebraicGeometry.Scheme.Modules.biprod_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules) [M.IsFiniteType] [N.IsFiniteType] :
    (CategoryTheory.Limits.biprod (C := X.Modules) M N).IsFiniteType :=
by
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun x => ?_
  obtain ⟨U, I, hI, pI, hxU, hpI⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType M x
  obtain ⟨V, J, hJ, pJ, hxV, hpJ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType N x
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  obtain ⟨pIW, hpIW⟩ : ∃ pIW : (SheafOfModules.free (R := W.toScheme.ringCatSheaf) I : W.toScheme.Modules) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M, Epi pIW :=
    AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le M
      (V := W) (U := U) inf_le_left I pI hpI
  obtain ⟨pJW, hpJW⟩ : ∃ pJW : (SheafOfModules.free (R := W.toScheme.ringCatSheaf) J : W.toScheme.Modules) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj N, Epi pJW :=
    AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le N
      (V := W) (U := V) inf_le_right J pJ hpJ
  letI : Epi pIW := hpIW
  letI : Epi pJW := hpJW
  let F : X.Modules ⥤ W.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι
  have hF := (AlgebraicGeometry.Scheme.Modules.restrictAdjunction W.ι).leftAdjoint_preservesColimits.{0, 0}
  letI : PreservesColimitsOfShape (Discrete WalkingPair) F := hF.preservesColimitsOfShape
  letI : PreservesBiproductsOfShape WalkingPair F :=
    preservesBiproductsOfShape_of_preservesCoproductsOfShape F
  letI : PreservesBiproduct (pairFunction M N) F := inferInstance
  letI : PreservesBinaryBiproduct M N F := preservesBinaryBiproduct_of_preservesBiproduct F M N
  let hmap : F.obj (M ⊞ N) ≅ F.obj M ⊞ F.obj N := F.mapBiprod M N
  let rM := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app M
  let rN := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app N
  let rMN := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app (M ⊞ N)
  let K : W.toScheme.Modules := SheafOfModules.free (R := W.toScheme.ringCatSheaf) I
  let L : W.toScheme.Modules := SheafOfModules.free (R := W.toScheme.ringCatSheaf) J
  letI : HasBinaryBiproduct K L := CategoryTheory.Abelian.hasBinaryBiproducts.has_binary_biproduct _ _
  let pIW' : K ⟶ F.obj M := pIW ≫ rM.inv
  let pJW' : L ⟶ F.obj N := pJW ≫ rN.inv
  let hRMi : Epi rM.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv rM)
  let hRNi : Epi rN.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv rN)
  haveI : Epi pIW' := by
    dsimp [pIW']
    exact @epi_comp _ _ _ _ _ pIW hpIW rM.inv hRMi
  haveI : Epi pJW' := by
    dsimp [pJW']
    exact @epi_comp _ _ _ _ _ pJW hpJW rN.inv hRNi
  haveI : Epi rMN.hom := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom rMN)
  haveI : Epi (biprod.map pIW' pJW') := inferInstance
  let hfree : Epi (SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J))
  let hcop : Epi (@biprod.isoCoprod W.toScheme.Modules _ _ K L _).symm.hom :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (@biprod.isoCoprod W.toScheme.Modules _ _ K L _).symm)
  let hmapinv : Epi hmap.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv hmap)
  let q : (SheafOfModules.free (R := W.toScheme.ringCatSheaf) (I ⊕ J) : W.toScheme.Modules) ⟶
      F.obj (M ⊞ N) :=
    (SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J).inv ≫
      (@biprod.isoCoprod W.toScheme.Modules _ _ K L _).symm.hom ≫
      (@biprod.map W.toScheme.Modules _ _ K L (F.obj M) (F.obj N) _ _ pIW' pJW') ≫ hmap.inv
  have hq : Epi q := by
    dsimp [q]
    have h1 : Epi ((SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J).inv ≫
        (@biprod.isoCoprod W.toScheme.Modules _ _ K L _).symm.hom) :=
      @epi_comp _ _ _ _ _ _ hfree _ hcop
    have h2 : Epi ((@biprod.map W.toScheme.Modules _ _ K L (F.obj M) (F.obj N) _ _ pIW' pJW') ≫ hmap.inv) :=
      @epi_comp _ _ _ _ _ _ (by infer_instance) _ hmapinv
    exact @epi_comp _ _ _ _ _ _ h1 _ h2
  have hq' : Epi (q ≫ rMN.hom) :=
    @epi_comp _ _ _ _ _ q hq rMN.hom
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom rMN))
  exact ⟨W, I ⊕ J, inferInstance, q ≫ rMN.hom, hxW, hq'⟩

end
