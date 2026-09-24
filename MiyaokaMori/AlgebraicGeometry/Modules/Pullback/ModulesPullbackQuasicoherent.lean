import MiyaokaMori.Prelude

/-! # Pullback of quasi-coherent sheaves is quasi-coherent

The pullback of a quasi-coherent sheaf along any morphism of schemes is quasi-coherent: a local
presentation `O^{(J)} → O^{(I)} → M → 0` pulls back to a presentation, since pullback is right
exact and preserves free sheaves.

Reference: Stacks 01BG.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.PullbackQcAux

open AlgebraicGeometry

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- `f^*O_Y ≅ O_X`: Mathlib's `SheafOfModules.pullbackObjUnitToUnit` (the adjoint transpose of
`O_Y → f_*O_X`), an isomorphism by the Mathlib instance whose hypothesis "the underlying functor
`Opens.map f.base` is final" is supplied here (`Y.Opens` is directed, `f⁻¹⊤ = ⊤`, parallel
morphisms in a poset category are equal). The same isomorphism as `pullbackUnitIso`, restated to
keep the import closure of this file small. -/

def unitPullbackIso (f : X ⟶ Y) :
    SheafOfModules.unit X.ringCatSheaf ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.Functor.final_of_exists_of_isFiltered _
      (fun _ => ⟨⊤, ⟨CategoryTheory.homOfLE le_top⟩⟩)
      (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  (@CategoryTheory.asIso (SheafOfModules.{u} X.ringCatSheaf) _ _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport of a global presentation along pullback: `f^*` is a left adjoint (preserves colimits)
and `f^*O_Y ≅ O_X` (preserves free sheaves), so Mathlib's `SheafOfModules.Presentation.map` applies. -/

def presentationPullback (f : X ⟶ Y) {M : Y.Modules} (P : M.Presentation) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).Presentation := by
  have h : PreservesColimitsOfSize.{u, u} (AlgebraicGeometry.Scheme.Modules.pullback f) :=
    inferInstance
  exact @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (AlgebraicGeometry.Scheme.Modules.pullback f) h (unitPullbackIso f)

/-- Transport a global presentation of `N|_U` on the open subscheme `U` to `N.over U` on the slice
site: transport along the inverse of the equivalence `Scheme.Modules.overEquiv U`, then rewrite with
`Scheme.Modules.overFunctorEquiv` (`N.over U` corresponds to `N|_U` under the equivalence). -/

def presentationOver {N : X.Modules} (U : X.Opens) (P : (N.restrict U.ι).Presentation) :
    (N.over U).Presentation := by
  have h : PreservesColimitsOfSize.{u, u}
      (AlgebraicGeometry.Scheme.Modules.overEquiv U).inverse := inferInstance
  refine SheafOfModules.Presentation.ofIsIso
    (((AlgebraicGeometry.Scheme.Modules.overEquiv U).inverse.mapIso
        ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app N).symm) ≪≫
      ((AlgebraicGeometry.Scheme.Modules.overEquiv U).unitIso.app (N.over U)).symm).hom
    (@SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (AlgebraicGeometry.Scheme.Modules.overEquiv U).inverse h ?_)
  exact ((AlgebraicGeometry.Scheme.Modules.overEquiv U).unitIso.app
      (SheafOfModules.unit (X.ringCatSheaf.over U))) ≪≫
    (AlgebraicGeometry.Scheme.Modules.overEquiv U).inverse.mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app
          (SheafOfModules.unit X.ringCatSheaf) ≪≫
        AlgebraicGeometry.Scheme.Modules.restrictUnitIso U.ι)

set_option backward.isDefEq.respectTransparency.types false in
/-- Base change (the localization step of Stacks 01BG): `(f^*M)|_{f⁻¹V} ≅ (f|_{f⁻¹V})^*(M|_V)`.
Assembled from `restrictFunctorIsoPullback` (restriction along an open immersion is pullback) and
the pseudofunctoriality `pullbackComp` along `f.resLE V (f⁻¹V) ≫ V.ι = (f⁻¹V).ι ≫ f`. -/

def pullbackRestrictIso (f : X ⟶ Y) (M : Y.Modules) (V : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (f.resLE V (f ⁻¹ᵁ V) le_rfl)).obj (M.restrict V.ι) ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ V).ι :=
  (AlgebraicGeometry.Scheme.Modules.pullback (f.resLE V (f ⁻¹ᵁ V) le_rfl)).mapIso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app M) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (f.resLE V (f ⁻¹ᵁ V) le_rfl) V.ι).app M ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f le_rfl)).app M ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f).app M).symm ≪≫
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).symm

end AlgebraicGeometry.Scheme.Modules.PullbackQcAux

open AlgebraicGeometry.Scheme.Modules.PullbackQcAux in
set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of a quasi-coherent sheaf is quasi-coherent (Stacks 01BG). Proof: `M`
quasi-coherent gives an open cover `{V_i}` of `Y` with global presentations of `M|_{V_i}`
(`exists_isOpenCover_presentation`); `{f⁻¹V_i}` covers `X`, `(f^*M)|_{f⁻¹V_i} ≅ (f|)^*(M|_{V_i})`
(base change), and pullback preserves colimits and free sheaves, so pulling back the presentation
of `M|_{V_i}` gives a global presentation of `(f^*M)|_{f⁻¹V_i}`, i.e. of `(f^*M).over (f⁻¹V_i)`
on the slice site; each piece is quasi-coherent and `IsQuasicoherent.of_coversTop` glues. -/
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  obtain ⟨ι, U, pres, hU, -⟩ := M.exists_isOpenCover_presentation
  have : ∀ i, (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over
      (f ⁻¹ᵁ U i)).IsQuasicoherent := fun i =>
    (presentationOver _ (SheafOfModules.Presentation.ofIsIso
        (pullbackRestrictIso f M (U i)).hom
        (presentationPullback (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl) (pres i)))).isQuasicoherent
  refine SheafOfModules.IsQuasicoherent.of_coversTop
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (fun i => f ⁻¹ᵁ U i) ?_
  rw [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  refine le_antisymm le_top ?_
  rw [SetLike.le_def]
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show f.base x ∈ (⨆ i, U i) by rw [hU]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

end
