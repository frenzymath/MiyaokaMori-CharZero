import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal

/-! # The degree-one component of `projBundle.localRingHom` as an adjoint transpose

For the local ring homomorphism `Φ = projBundle.localRingHom V f M ψ U e W : A(W) → Γ(V', O)` of a piece
`(U, e, V' = U ⊓ f⁻¹W)` of `projBundle.lift V f M ψ` (Stacks 01O4), the degree-one value on a generator
`symGen s`, `s ∈ Γ(W, V^∨)`, was computed in `TotLineAffineOverBaseDegreeOne` as the section
`(homEquiv_g (pullbackComp⁻¹ ≫ ι^*ψ ≫ e'))(s)` of the transpose along `g = ι ≫ f`. Here we transpose in two
steps (`homEquiv_g = homEquiv_f ∘ homEquiv_ι`, `Adjunction.comp_homEquiv`, `homEquiv_pullbackComp_hom_app_comp`):

`Φ(symGen s) = res (k ((ι^♯) ((homEquiv_f ψ)(s))))` (`localRingHomComponent_one_symGen_apply_transpose`),

where `homEquiv_f ψ : V^∨ → f_* M` is the transpose of the invertible quotient, `ι^♯ : Γ(T, f⁻¹W) → Γ(V', ι⁻¹f⁻¹W)`
the restriction to the piece, and `k = localRingHomUnitAut = (pullbackUnitIso ι)⁻¹ ≫ e'` the automorphism of `O_{V'}`
carrying the trivialization (an `O`-linear automorphism of `O`, i.e. multiplication by the unit `k(1)`).

This is the generic input for the degree-one generator computation of the canonical piece of `Tot(L) → P(O ⊕ L)`
(`canonicalPiece_genSections_sLinear`, `TotLineAffineOverBase`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.projBundle

open AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The automorphism `k = (pullbackUnitIso ι)⁻¹ ≫ e'` of `O_{V'}` carrying the trivialization `e` of `M` on the
piece `V' = U ⊓ f⁻¹W` (`e' = localRingHomTriv f M U e W : ι^*M ≅ O_{V'}`). -/
def localRingHomUnitAut (f : T ⟶ X) (U : T.Opens)
    (e : (show T.Modules from SheafOfModules.unit T.ringCatSheaf).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) :
    (SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf : (U ⊓ f ⁻¹ᵁ W).toScheme.Modules) ≅
      SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf :=
  (pullbackUnitIso (localRingHomIncl f U W)).symm ≪≫ localRingHomTriv f (SheafOfModules.unit T.ringCatSheaf) U e W

theorem localRingHomTriv_hom_eq (f : T ⟶ X) (U : T.Opens)
    (e : (show T.Modules from SheafOfModules.unit T.ringCatSheaf).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) :
    (localRingHomTriv f (SheafOfModules.unit T.ringCatSheaf) U e W).hom =
      (pullbackUnitIso (localRingHomIncl f U W)).hom ≫ (localRingHomUnitAut f U e W).hom := by
  unfold localRingHomUnitAut
  rw [Iso.trans_hom, Iso.symm_hom]
  erw [Iso.hom_inv_id_assoc]

/-- **Two-step transpose of the degree-one sheaf map.** With `Φ₁ = pullbackComp⁻¹ ≫ ι^*ψ ≫ e'`
(`= g^*(symGen) ≫ localRingHomSheafHom … 1`), its transpose along `g = ι ≫ f` is the transpose of `ψ` along `f`
followed by `f_*(unitToPushforwardObjUnit ι ≫ ι_* k)`. -/
theorem homEquiv_localRingHomSheafHom_one (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (ψ : (Modules.pullback f).obj (dual V) ⟶ (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (U : T.Opens)
    (e : (show T.Modules from SheafOfModules.unit T.ringCatSheaf).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) :
    (pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
        ((pullbackComp (localRingHomIncl f U W) f).inv.app (dual V) ≫
          (Modules.pullback (localRingHomIncl f U W)).map ψ ≫
          (localRingHomTriv f (SheafOfModules.unit T.ringCatSheaf) U e W).hom) =
      ((pullbackPushforwardAdjunction f).homEquiv _ _ ψ ≫
        (Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit (localRingHomIncl f U W).toRingCatSheafHom ≫
            (Modules.pushforward (localRingHomIncl f U W)).map (localRingHomUnitAut f U e W).hom)) ≫
        (pushforwardComp (localRingHomIncl f U W) f).hom.app _ := by
  unfold localRingHomBase
  have h := homEquiv_pullbackComp_hom_app_comp (localRingHomIncl f U W) f
    ((pullbackComp (localRingHomIncl f U W) f).inv.app (dual V) ≫
      (Modules.pullback (localRingHomIncl f U W)).map ψ ≫
      (localRingHomTriv f (SheafOfModules.unit T.ringCatSheaf) U e W).hom)
  erw [Iso.hom_inv_id_app_assoc] at h
  have h3 := congrArg (fun m => m ≫ (pushforwardComp (localRingHomIncl f U W) f).hom.app
    (SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h3
  refine h3.symm.trans ?_
  refine congrArg (fun m => m ≫ (pushforwardComp (localRingHomIncl f U W) f).hom.app
    (SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf)) ?_
  show (pullbackPushforwardAdjunction f).homEquiv _ _
    ((pullbackPushforwardAdjunction (localRingHomIncl f U W)).homEquiv _ _
      ((Modules.pullback (localRingHomIncl f U W)).map ψ ≫
        (localRingHomTriv f (SheafOfModules.unit T.ringCatSheaf) U e W).hom)) = _
  rw [localRingHomTriv_hom_eq, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, homEquiv_pullbackUnitIso_hom_pbup]
  rfl

/-- **Degree-one component on a generator, transposed in two steps**: for `s ∈ Γ(W, V^∨)`,
`localRingHomComponent … 1 (symGen s) = res_{⊤ ≤ g⁻¹W} (k (ι^♯ ((homEquiv_f ψ)(s))))`. -/
theorem localRingHomComponent_one_symGen_apply_transpose (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (ψ : (Modules.pullback f).obj (dual V) ⟶ (SheafOfModules.unit T.ringCatSheaf : T.Modules))
    (U : T.Opens)
    (e : (show T.Modules from SheafOfModules.unit T.ringCatSheaf).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) (s : (dual V).val.obj (op W)) :
    localRingHomComponent V f (SheafOfModules.unit T.ringCatSheaf) ψ U e W 1 (((symGen (dual V)).val.app (op W)).hom s) =
      ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
          (homOfLE (localRingHomBase_top_le f U W)).op).hom
        (AlgebraicGeometry.Scheme.Modules.Hom.app (localRingHomUnitAut f U e W).hom
          (localRingHomIncl f U W ⁻¹ᵁ (f ⁻¹ᵁ W))
          ((localRingHomIncl f U W).app (f ⁻¹ᵁ W)
            (AlgebraicGeometry.Scheme.Modules.Hom.app ((pullbackPushforwardAdjunction f).homEquiv _ _ ψ) W s))) := by
  rw [localRingHomComponent_one_symGen_apply, homEquiv_localRingHomSheafHom_one]
  rfl

/-- **Restriction bookkeeping for the canonical piece `U = f⁻¹W`**: restricting a section `y ∈ Γ(T, f⁻¹W)` to the
piece `V' = f⁻¹W ⊓ f⁻¹W` along `ι`, then to `⊤ ≤ g⁻¹W`, then back to `f⁻¹W` along `homOfLE`, is the identification
`topIso.inv : Γ(T, f⁻¹W) ≅ Γ(f⁻¹W, ⊤)` (all maps are restriction maps of `O_T` between the same opens). -/
theorem homOfLE_appTop_map_localRingHomIncl_app (f : T ⟶ X) (W : X.Opens) (y : Γ(T, f ⁻¹ᵁ W)) :
    (T.homOfLE (le_inf le_rfl le_rfl : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ W)).appTop.hom
        (((AlgebraicGeometry.Scheme.Modules.presheaf
            (SheafOfModules.unit (f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
          (homOfLE (localRingHomBase_top_le f (f ⁻¹ᵁ W) W)).op).hom
          ((localRingHomIncl f (f ⁻¹ᵁ W) W).app (f ⁻¹ᵁ W) y)) =
      (f ⁻¹ᵁ W).topIso.inv.hom y := by
  unfold localRingHomIncl
  rw [Modules.unit_presheaf_map_apply, Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app,
    Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
  erw [CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => (T.presheaf.map k).hom y) (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.projBundle

end
