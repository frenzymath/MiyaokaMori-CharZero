import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseDegreeOneTranspose
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackIdMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraSectionsRingEquivSym

/-! # Local pieces with the canonical trivializations

Used for the zero section of `Tot(L)` in `P(O ⊕ L)` (`zeroSection_toProjBundle_pieces`, `TotLineAffineOverBase`;
in the paper, "the section defined by the other summand `O` is the zero section of `Tot(L)`"; Stacks 01O4).
Notation as in `TotLineAffineOverBaseDegreeOneTranspose`: a piece
`(U, e, V' = U ⊓ f⁻¹W)` of `projBundle.lift V f M ψ`, `j : V' ↪ U`, `ι = j ≫ U.ι = localRingHomIncl f U W`,
`g = ι ≫ f = localRingHomBase f U W`, `e' = localRingHomTriv f M U e W : ι^*M ≅ O_{V'}`.

* `restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso` (**Lemma R**): for an open immersion `j`,
  `restrictFunctorIsoPullback⁻¹ ≫ restrictUnitIso = pullbackUnitIso` on the structure sheaf — both transposes
  `O_Y → j_* O_X` are the restriction maps `j^♯` on sections (Mathlib `restrictAdjunction_unit_app_app`,
  `Opens`-level `appIso`).
* `localRingHomTriv_mapIso_restrictUnitIso` (**Lemma T**): for a *global* trivialization `ε : M ≅ O_T` restricted to
  `U` (`e = (restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι`), `e'.hom = ι^*(ε.hom) ≫ (pullbackUnitIso ι).hom`
  (naturality of `restrictFunctorIsoPullback` and `pullbackComp`, Lemma R, `pullbackComp_hom_app_pullbackUnitIso_hom`).
  Special case `ε = 𝟙` (`localRingHomTriv_restrictUnitIso`): the canonical trivialization of `O_T` gives
  `e' = pullbackUnitIso ι`, i.e. the unit automorphism `k = localRingHomUnitAut` is the identity
  (`localRingHomUnitAut_restrictUnitIso_hom`).
* `homOfLE_appTop_localRingHom_genSections_restrictUnitIso`: for the canonical piece `(f⁻¹W, restrictUnitIso, f⁻¹W)` of a
  lift with `M = O_T`, the degree-one value on `genSections m` is exactly `topIso.inv ((homEquiv_f ψ)(m))` (no unit
  factor) — the `k = 𝟙` refinement of `canonicalPiece_genSections_eq_transpose`.
* `homOfLE_appTop_localRingHom_id_genSections_of_triv`: for `f = 𝟙`, `ψ = pullbackId ≫ φ` and `e` from a global `ε`,
  the degree-one value of the piece `(U, e, V₂ := W)` on `genSections m` is `topIso.inv (ε(φ(m)))`
  (`homEquiv_pullbackId_hom_app_comp`, `pushforwardId_inv_app_app`, restriction bookkeeping). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- On sections, `(restrictUnitIso j).hom` is `(j.appIso _).hom` (definitional). -/
theorem restrictUnitIso_hom_app_apply (j : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion j] (V : Y.Opens)
    (x : Γ(X, j ''ᵁ V)) :
    ((restrictUnitIso j).hom.app V) x = (j.appIso V).hom x := rfl

/-- **Lemma R**: `restrictFunctorIsoPullback⁻¹ ≫ restrictUnitIso = pullbackUnitIso` on the structure sheaf. -/
theorem restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso (j : Y ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion j] :
    (restrictFunctorIsoPullback j).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫ (restrictUnitIso j).hom =
      (pullbackUnitIso j).hom := by
  apply ((pullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackUnitIso_hom_pbup, restrictFunctorIsoPullback,
    Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply hom_ext
  intro U
  ext x
  rw [Hom.comp_app, pushforward_map_app]
  change ((restrictUnitIso j).hom.app (j ⁻¹ᵁ U))
    (((restrictAdjunction j).unit.app (SheafOfModules.unit X.ringCatSheaf)).app U x) = j.app U x
  rw [restrictAdjunction_unit_app_app, restrictUnitIso_hom_app_apply, Scheme.Hom.appIso_hom']
  change (j.appLE (j ''ᵁ (j ⁻¹ᵁ U)) (j ⁻¹ᵁ U) _).hom ((X.presheaf.map (homOfLE (j.image_preimage_le U)).op).hom x) =
    j.app U x
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]

/-- **Lemma T**: the transported trivialization `e'` of a piece, for `e` coming from a global `ε : M ≅ O_T`. -/
theorem localRingHomTriv_mapIso_restrictUnitIso (f : Y ⟶ X) (M : Y.Modules) (U : Y.Opens)
    (ε : M ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (W : X.Opens) :
    (projBundle.localRingHomTriv f M U ((restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W).hom =
      (Modules.pullback (projBundle.localRingHomIncl f U W)).map ε.hom ≫
        (pullbackUnitIso (projBundle.localRingHomIncl f U W)).hom := by
  unfold projBundle.localRingHomTriv projBundle.localRingHomIncl
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_inv]
  have h1 : (restrictFunctorIsoPullback U.ι).inv.app M ≫ (restrictFunctor U.ι).map ε.hom =
      (Modules.pullback U.ι).map ε.hom ≫ (restrictFunctorIsoPullback U.ι).inv.app _ :=
    ((restrictFunctorIsoPullback U.ι).inv.naturality ε.hom).symm
  rw [← Category.assoc ((restrictFunctorIsoPullback U.ι).inv.app M), h1, Category.assoc,
    restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso, CategoryTheory.Functor.map_comp, Category.assoc,
    ← pullbackComp_hom_app_pullbackUnitIso_hom]
  have h2 : (pullbackComp (Y.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)) U.ι).inv.app M ≫
      (Modules.pullback (Y.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U))).map ((Modules.pullback U.ι).map ε.hom) =
      (Modules.pullback (Y.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U) ≫ U.ι)).map ε.hom ≫
        (pullbackComp (Y.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)) U.ι).inv.app _ :=
    ((pullbackComp (Y.homOfLE (inf_le_left : U ⊓ f ⁻¹ᵁ W ≤ U)) U.ι).inv.naturality ε.hom).symm
  rw [← Category.assoc, ← Category.assoc, h2, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The canonical trivialization of `O_T` transports to `pullbackUnitIso ι` on the piece. -/
theorem localRingHomTriv_restrictUnitIso (f : Y ⟶ X) (U : Y.Opens) (W : X.Opens) :
    (projBundle.localRingHomTriv f (SheafOfModules.unit Y.ringCatSheaf) U (restrictUnitIso U.ι) W).hom =
      (pullbackUnitIso (projBundle.localRingHomIncl f U W)).hom := by
  have h := localRingHomTriv_mapIso_restrictUnitIso f (SheafOfModules.unit Y.ringCatSheaf) U (Iso.refl _) W
  rw [Functor.mapIso_refl, Iso.refl_trans, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- The unit automorphism `k` of the canonical trivialization is the identity. -/
theorem localRingHomUnitAut_restrictUnitIso_hom (f : Y ⟶ X) (U : Y.Opens) (W : X.Opens) :
    (projBundle.localRingHomUnitAut f U (restrictUnitIso U.ι) W).hom = 𝟙 _ := by
  unfold projBundle.localRingHomUnitAut
  rw [Iso.trans_hom, Iso.symm_hom, localRingHomTriv_restrictUnitIso]
  exact (pullbackUnitIso _).inv_hom_id

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.projBundle

open AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **Degree-one value of the canonical piece** `(f⁻¹W, restrictUnitIso, f⁻¹W)` of `projBundle.lift V f O_T ψ` on a
generator: `topIso.inv ((homEquiv_f ψ)(m))` (the unit automorphism `k` is the identity). -/
theorem homOfLE_appTop_localRingHom_genSections_restrictUnitIso (V : X.Modules) [V.IsLocallyFree]
    [V.IsFiniteType] (f : T ⟶ X)
    (ψ : (Modules.pullback f).obj (dual V) ⟶ (SheafOfModules.unit T.ringCatSheaf : T.Modules)) (W : X.Opens)
    (m : Γ(dual V, W)) :
    (T.homOfLE (le_inf le_rfl le_rfl : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ W)).appTop.hom
        (localRingHom V f (SheafOfModules.unit T.ringCatSheaf) ψ (f ⁻¹ᵁ W) (restrictUnitIso (f ⁻¹ᵁ W).ι) W
          (symGradedAlgebra.genSections (dual V) W m)) =
      (f ⁻¹ᵁ W).topIso.inv.hom (Modules.Hom.app ((pullbackPushforwardAdjunction f).homEquiv _ _ ψ) W m) := by
  show (T.homOfLE (le_inf le_rfl le_rfl : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ W)).appTop.hom
    (localRingHom V f (SheafOfModules.unit T.ringCatSheaf) ψ (f ⁻¹ᵁ W) (restrictUnitIso (f ⁻¹ᵁ W).ι) W
      (DirectSum.of _ 1 (((symGen (dual V)).val.app (op W)).hom m))) = _
  unfold localRingHom
  erw [DirectSum.toSemiring_of]
  rw [localRingHomComponent_one_symGen_apply_transpose, localRingHomUnitAut_restrictUnitIso_hom]
  exact homOfLE_appTop_map_localRingHomIncl_app f W _

/-- The restriction bookkeeping for a piece `(U, e, V₂ := W)` of a lift along `𝟙 X`: restricting `y ∈ Γ(X, W)` to
`U ⊓ 𝟙⁻¹W`, then to `⊤ ≤ g⁻¹W`, then to `W` along `homOfLE` is `topIso.inv`. -/
theorem homOfLE_appTop_map_localRingHomIncl_id_app (U W : X.Opens) (hW : W ≤ U) (y : Γ(X, W)) :
    (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge : W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
        (((AlgebraicGeometry.Scheme.Modules.presheaf
            (SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
          (homOfLE (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U W)).op).hom
          ((localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W).app ((CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W) y)) =
      W.topIso.inv.hom y := by
  unfold localRingHomIncl
  rw [Modules.unit_presheaf_map_apply, Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app,
    Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
  erw [CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => (X.presheaf.map k).hom y) (Subsingleton.elim _ _)

/-- **Degree-one value of a piece of a lift along `𝟙 X` with a global trivialization**: for
`ψ = (pullbackId X).hom.app _ ≫ φ`, `e = (restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι`, `V₂ := W ≤ U`,
the piece sends `genSections m` to `topIso.inv (ε(φ(m)))`. -/
theorem homOfLE_appTop_localRingHom_id_genSections_of_triv (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (M : X.Modules) [M.IsLineBundle] (φ : dual V ⟶ M) (U : X.Opens)
    (ε : M ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (W : X.Opens) (hW : W ≤ U) (m : Γ(dual V, W)) :
    (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge : W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
        (localRingHom V (CategoryTheory.CategoryStruct.id X) M ((pullbackId X).hom.app (dual V) ≫ φ) U
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W (symGradedAlgebra.genSections (dual V) W m)) =
      W.topIso.inv.hom (ε.hom.app W (φ.app W m)) := by
  show (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge : W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
    (localRingHom V (CategoryTheory.CategoryStruct.id X) M ((pullbackId X).hom.app (dual V) ≫ φ) U
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W
      (DirectSum.of _ 1 (((symGen (dual V)).val.app (op W)).hom m))) = _
  unfold localRingHom
  erw [DirectSum.toSemiring_of]
  rw [localRingHomComponent_one_symGen_apply]
  -- the transpose of the degree-one sheaf map, in two steps along `g = ι ≫ 𝟙`
  have hmor : (pullbackPushforwardAdjunction (localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).homEquiv _ _
      ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
          (CategoryTheory.CategoryStruct.id X)).inv.app (dual V) ≫
        (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
          ((pullbackId X).hom.app (dual V) ≫ φ) ≫
        (localRingHomTriv (CategoryTheory.CategoryStruct.id X) M U
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W).hom) =
      ((pushforwardId X).inv.app (dual V) ≫ (Modules.pushforward (CategoryTheory.CategoryStruct.id X)).map
        (φ ≫ ε.hom ≫ SheafOfModules.unitToPushforwardObjUnit
          (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W).toRingCatSheafHom)) ≫
        (pushforwardComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
          (CategoryTheory.CategoryStruct.id X)).hom.app _ := by
    unfold localRingHomBase
    have h1 := homEquiv_pullbackComp_hom_app_comp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
      (CategoryTheory.CategoryStruct.id X)
      ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
          (CategoryTheory.CategoryStruct.id X)).inv.app (dual V) ≫
        (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
          ((pullbackId X).hom.app (dual V) ≫ φ) ≫
        (localRingHomTriv (CategoryTheory.CategoryStruct.id X) M U
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W).hom)
    erw [Iso.hom_inv_id_app_assoc] at h1
    have h3 := congrArg (fun k => k ≫ (pushforwardComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
      (CategoryTheory.CategoryStruct.id X)).hom.app
      (SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)) h1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h3
    refine h3.symm.trans ?_
    refine congrArg (fun k => k ≫ (pushforwardComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
      (CategoryTheory.CategoryStruct.id X)).hom.app
      (SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)) ?_
    show (pullbackPushforwardAdjunction (CategoryTheory.CategoryStruct.id X)).homEquiv _ _
      ((pullbackPushforwardAdjunction (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).homEquiv _ _
        ((Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
          ((pullbackId X).hom.app (dual V) ≫ φ) ≫
        (localRingHomTriv (CategoryTheory.CategoryStruct.id X) M U
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W).hom)) = _
    rw [localRingHomTriv_mapIso_restrictUnitIso, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_left, homEquiv_pullbackUnitIso_hom_pbup, Category.assoc,
      homEquiv_pullbackId_hom_app_comp]
    rfl
  have hval : (((pullbackPushforwardAdjunction (localRingHomBase (CategoryTheory.CategoryStruct.id X) U W)).homEquiv _ _
      ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)
          (CategoryTheory.CategoryStruct.id X)).inv.app (dual V) ≫
        (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W)).map
          ((pullbackId X).hom.app (dual V) ≫ φ) ≫
        (localRingHomTriv (CategoryTheory.CategoryStruct.id X) M U
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso ε ≪≫ restrictUnitIso U.ι) W).hom)).val.app
        (op W)).hom m =
      (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U W).app ((CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)
        (ε.hom.app W (φ.app W m)) :=
    (congrArg (fun k => (k.val.app (op W)).hom m) hmor).trans rfl
  refine Eq.trans (congrArg (fun y => (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge :
      W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
    (((AlgebraicGeometry.Scheme.Modules.presheaf
        (SheafOfModules.unit (U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
      (homOfLE (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U W)).op).hom y)) hval) ?_
  exact homOfLE_appTop_map_localRingHomIncl_id_app U W hW _

/-- **Degree-zero value of a piece of a lift along `𝟙 X`** with `V₂ := W ≤ U`: `sectionsUnitHom r ↦ topIso.inv r`
(all maps are restriction maps of `O_X` between the same opens). -/
theorem homOfLE_appTop_localRingHom_id_sectionsUnitHom (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (M : X.Modules) [M.IsLineBundle]
    (ψ : (Modules.pullback (CategoryTheory.CategoryStruct.id X)).obj (dual V) ⟶ M) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) (hW : W ≤ U) (r : Γ(X, W)) :
    (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge : W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
        (localRingHom V (CategoryTheory.CategoryStruct.id X) M ψ U e W
          ((symGradedAlgebra (dual V)).sectionsUnitHom W r)) =
      W.topIso.inv.hom r := by
  show (X.homOfLE (le_inf hW (Scheme.Hom.id_preimage W).ge : W ≤ U ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)).appTop.hom
    (localRingHom V (CategoryTheory.CategoryStruct.id X) M ψ U e W ((symGradedAlgebra (dual V)).sectionsUnit W r).1) = _
  rw [localRingHom_sectionsUnit]
  unfold localRingHomBase localRingHomIncl
  have hid : (((CategoryTheory.CategoryStruct.id X).app W).hom r : Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W)) =
    r := rfl
  rw [Hom.comp_appLE, Hom.comp_appLE, CommRingCat.comp_apply, hid, Scheme.Opens.ι_app, Scheme.homOfLE_appLE,
    Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => (X.presheaf.map k).hom r) (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.projBundle

end
