import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPresentation
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfRestrictPresentation
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentOfAffineLocalizing
-- Not used by this module's proofs; kept because `DeformedJetAlgebra` and `JetGrading` reach
-- `isQuasicoherent_kernel` only through this import.
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # Quasi-coherent sheaves are closed under tensor products and colimits (Stacks 01CE, 01ID)

Source: Stacks 01CE (the tensor product preserves quasi-coherence), 01ID (colimits of quasi-coherent
sheaves are quasi-coherent).

## Proof of `isQuasicoherent_tensor`

1. `F`, `G` quasi-coherent ⟹ there are open covers `{U_i}`, `{V_j}` with global presentations of
   `F|_{U_i}`, `G|_{V_j}` (Mathlib `Scheme.Modules.exists_isOpenCover_presentation`).
2. For every point `x` take `W = U_i ⊓ V_j ∋ x` and shrink both presentations to `W` with
   `presentationShrink` (`presentationRestrict` + `restrictFunctorComp`/`restrictFunctorCongr`).
3. `ModulesTensorPresentation` builds a presentation of `F|_W ⊗ G|_W` from those of `F|_W`, `G|_W`.
4. `(F ⊗ G)|_W ≅ F|_W ⊗ G|_W` (`restrictTensorObjIso`: restriction along an open immersion is strong
   monoidal) transports it to a presentation of `(tensor F G)|_W`; these `W` cover `X`, and
   `isQuasicoherent_of_restrict_presentation` concludes.

The affine criterion is not used: Mathlib's `tilde` carries no monoidal structure, so
`isQuasicoherent_iff_isIso_fromTildeΓ` is not available for this.

## Proof of `isQuasicoherent_colimit` (Stacks 01ID)

Instead of direct sums + cokernels + 01IC, use the tilde adjunction directly, treating arbitrary small
colimits at once:
1. **On `Spec`** (`isQuasicoherent_colimit_spec`): for `G : J ⥤ (Spec R).Modules` with each `G j`
   quasi-coherent, `fromTildeΓ : (Γ G j)^~ ⟶ G j` is an isomorphism (Mathlib
   `isIso_fromTildeΓ_of_isQuasicoherent`), natural in `j` (a component of `fromTildeΓNatTrans`), so
   `(G ⋙ Γ) ⋙ tilde ≅ G`. `tilde.functor R` is a left adjoint (`tilde.adjunction`) and preserves
   colimits: `colim G ≅ colim ((G ⋙ Γ) ⋙ tilde) ≅ (colim (G ⋙ Γ))^~`, a tilde, hence quasi-coherent;
   quasi-coherence is invariant under isomorphism.
2. **General schemes**: for an affine open `U`, restriction along the open immersion
   `hU.fromSpec : Spec Γ(U) → X` preserves colimits (`restrictFunctor` is a left adjoint) and
   quasi-coherence (`isQuasicoherent_restrictFunctor`), so `(colim F).restrict hU.fromSpec ≅ colim (F ⋙ restrict)`
   is quasi-coherent; `isQuasicoherent_iff_isIso_fromTildeΓ` + `isIso_fromTildeΓ_iff_isLocalizing` give
   `IsLocalizing`, and `QcOfAffineLocalizingAux.isQuasicoherent_over_of_isLocalizing`
   (`QuasicoherentOfAffineLocalizing`) gives that `(colim F).over U` is quasi-coherent; affine opens cover
   `X`, and `SheafOfModules.IsQuasicoherent.of_coversTop` glues.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Shrink a global presentation on an open `U` to a smaller open `V ≤ U`. -/
def presentationShrink {M : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (P : SheafOfModules.Presentation.{u} (M.restrict U.ι)) :
    SheafOfModules.Presentation.{u} (M.restrict V.ι) :=
  SheafOfModules.Presentation.ofIsIso.{u, u, u}
    ((((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp
        (X.homOfLE h) U.ι).app M).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).hom)
    (AlgebraicGeometry.Scheme.Modules.presentationRestrict (X.homOfLE h) P)

/-- `(F ⊗ G)|_W ≅ F|_W ⊗ G|_W` (in terms of `Modules.tensor`). -/
def restrictTensorIso (F G : X.Modules) (W : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.tensor F G).restrict W.ι ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := W.toScheme.Modules)
        (F.restrict W.ι) (G.restrict W.ι) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).mapIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G) ≪≫
    AlgebraicGeometry.Scheme.Modules.restrictTensorObjIso W.ι F G

end AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
instance AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor {X : AlgebraicGeometry.Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (AlgebraicGeometry.Scheme.Modules.tensor F G).IsQuasicoherent := by
  obtain ⟨ιF, UF, presF, hUF, -⟩ := F.exists_isOpenCover_presentation
  obtain ⟨ιG, UG, presG, hUG, -⟩ := G.exists_isOpenCover_presentation
  refine AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_restrict_presentation _
    (fun x => ?_)
  obtain ⟨i, hi⟩ : ∃ i, x ∈ UF i := by
    have hx : x ∈ (⨆ i, UF i) := by rw [hUF]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ : ∃ j, x ∈ UG j := by
    have hx : x ∈ (⨆ j, UG j) := by rw [hUG]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(UF i ⊓ UG j).toScheme, (UF i ⊓ UG j).ι, inferInstance, ?_, ⟨?_⟩⟩
  · rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact ⟨hi, hj⟩
  · exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (AlgebraicGeometry.Scheme.Modules.restrictTensorIso F G (UF i ⊓ UG j)).inv
      (AlgebraicGeometry.Scheme.Modules.tensorPresentation
        (AlgebraicGeometry.Scheme.Modules.presentationShrink inf_le_left (presF i))
        (AlgebraicGeometry.Scheme.Modules.presentationShrink inf_le_right (presG j)))

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The case of `Spec` (the core of Stacks 01ID): a colimit of quasi-coherent sheaves on `Spec R` is
quasi-coherent. Proof: each `G j ≅ (Γ G j)^~` (`isIso_fromTildeΓ_of_isQuasicoherent`, naturality from
`fromTildeΓNatTrans`), so `colim G ≅ colim ((G ⋙ Γ) ⋙ tilde) ≅ (colim (G ⋙ Γ))^~` (`tilde.functor` is a
left adjoint and preserves colimits); a tilde is quasi-coherent, and quasi-coherence is invariant under
isomorphism. -/
theorem isQuasicoherent_colimit_spec {R : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (G : J ⥤ (Spec R).Modules) (hG : ∀ j, (G.obj j).IsQuasicoherent) :
    (colimit G).IsQuasicoherent := by
  have hiso : ∀ j, IsIso ((G.obj j).fromTildeΓ) := fun j =>
    haveI := hG j
    isIso_fromTildeΓ_of_isQuasicoherent (G.obj j)
  let e : (G ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R ≅ G :=
    NatIso.ofComponents (fun j => haveI := hiso j; asIso ((G.obj j).fromTildeΓ))
      (fun f => (fromTildeΓNatTrans (R := R)).naturality (G.map f))
  let i : (tilde.functor R).obj (colimit (G ⋙ moduleSpecΓFunctor (R := R))) ≅ colimit G :=
    preservesColimitIso (tilde.functor R) (G ⋙ moduleSpecΓFunctor (R := R)) ≪≫
      HasColimit.isoOfNatIso e
  have ht : ((tilde.functor R).obj (colimit (G ⋙ moduleSpecΓFunctor (R := R)))).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso i ht

end AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
theorem AlgebraicGeometry.Scheme.Modules.isQuasicoherent_colimit {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type u} [CategoryTheory.SmallCategory J] (F : J ⥤ X.Modules)
    (hF : ∀ j, (F.obj j).IsQuasicoherent) : (CategoryTheory.Limits.colimit F).IsQuasicoherent := by
  have key : ∀ U : X.affineOpens, ((colimit F).over (U : X.Opens)).IsQuasicoherent := fun U => by
    have hU := U.2
    have hpres : PreservesColimitsOfSize.{u, u} (restrictFunctor hU.fromSpec) := inferInstance
    let i : (colimit F).restrict hU.fromSpec ≅ colimit (F ⋙ restrictFunctor hU.fromSpec) :=
      preservesColimitIso (restrictFunctor hU.fromSpec) F
    have hcol : (colimit (F ⋙ restrictFunctor hU.fromSpec)).IsQuasicoherent :=
      isQuasicoherent_colimit_spec (F ⋙ restrictFunctor hU.fromSpec) fun j => by
        have := hF j
        exact isQuasicoherent_restrictFunctor hU.fromSpec (F.obj j)
    have hqc : ((colimit F).restrict hU.fromSpec).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso i.symm hcol
    have hiso : IsIso ((colimit F).restrict hU.fromSpec).fromTildeΓ :=
      (isQuasicoherent_iff_isIso_fromTildeΓ _).mp hqc
    exact QcOfAffineLocalizingAux.isQuasicoherent_over_of_isLocalizing (colimit F) hU
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp hiso)
  refine SheafOfModules.IsQuasicoherent.of_coversTop (colimit F)
    (fun U : X.affineOpens => (U : X.Opens)) ?_
  rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
  exact iSup_affineOpens_eq_top X

end
