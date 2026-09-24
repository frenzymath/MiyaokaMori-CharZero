import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfRestrictFreeCover
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso

/-! # Quasi-coherent sheaves with free sections on an affine cover are locally free

If the sections of a quasi-coherent sheaf on the members of an affine open cover are finite free
modules, the sheaf is locally free; if all these ranks equal `n`, the rank at every point is `n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

open AlgebraicGeometry

/-- A quasi-coherent sheaf `N` on `Spec R` whose module of global sections has a basis indexed by `ι`
satisfies `N ≅ O^{(ι)}` (Stacks 01IB + `tildeFinsupp`). -/
private theorem freeAffine.spec_iso_free {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]
    (ι : Type u) (b : Module.Basis ι R ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤))) :
    Nonempty (N ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) ι) := by
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let P := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let l : P ≅ ModuleCat.of R (ι →₀ R) := b.repr.toModuleIso
  exact ⟨(asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso l ≪≫ tildeFinsupp ι⟩

/-- A basis of `Γ(U, M)` moved to `Γ(Spec Γ(U,O), M|_{Spec})` (through a semilinear bijection). -/
private theorem freeAffine.basis_restrict {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty (Module.Basis ι Γ(X, U) Γ(M.restrict hU.fromSpec, ⊤)) := by
  have hV : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let e : Γ(X, U) ≃+* Γ(X, U) :=
    ((X.presheaf.mapIso (eqToIso hV).op) ≪≫ (hU.fromSpec.appIso ⊤) ≪≫
      Scheme.ΓSpecIso Γ(X, U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  have key : ∀ (r : Γ(X, hU.fromSpec ''ᵁ ⊤)) (y : Γ(M, hU.fromSpec ''ᵁ ⊤)),
      (M.restrictAppIso hU.fromSpec ⊤).inv (r • y) =
        ((hU.fromSpec.appIso ⊤).hom r) • (M.restrictAppIso hU.fromSpec ⊤).inv y := fun r y => by
    have := Scheme.Modules.smul_restrictAppIso_inv_apply hU.fromSpec M ⊤ r y
    exact this
  let g : Γ(M, U) →ₛₗ[(e : Γ(X, U) →+* Γ(X, U))] Γ(M.restrict hU.fromSpec, ⊤) :=
    { toFun := fun m => (M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (eqToHom hV).op m)
      map_add' := fun a b => by simp
      map_smul' := fun a m => by
        rw [Scheme.Modules.map_smul, key, Scheme.Modules.smul_Spec_def]
        congr 1
        simp only [e]
        have h1 : (Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
        rw [h1, CategoryTheory.Functor.map_id]
        simp [Iso.commRingCatIsoToRingEquiv] }
  have hg : Function.Bijective g :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).inv).comp
      (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom hV).op))
  exact MiyaokaMori.basis_of_semilinearEquiv (LinearEquiv.ofBijective g hg) b

/-- If `Γ(U, M)` has a basis on an affine open `U`, then `M|_{Spec Γ(U,O)}` is free. -/
private theorem freeAffine.restrict_fromSpec_iso_free {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty (M.restrict hU.fromSpec ≅ SheafOfModules.free (R := (Spec Γ(X, U)).ringCatSheaf) ι) := by
  obtain ⟨b'⟩ := freeAffine.basis_restrict M hU ι b
  exact freeAffine.spec_iso_free (M.restrict hU.fromSpec) ι b'

/-- Moved back to the open subscheme `U`: `pullback U.ι M ≅ O_U^{(ι)}`. -/
private theorem freeAffine.pullback_iso_free {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) ι) := by
  obtain ⟨ψ⟩ := freeAffine.restrict_fromSpec_iso_free M hU ι b
  let F : SheafOfModules.{u} (Spec Γ(X, U)).ringCatSheaf ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor hU.isoSpec.hom
  have hF : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).leftAdjoint_preservesColimits.{u, u}
  have : PreservesColimitsOfShape (Discrete ι) F := hF.preservesColimitsOfShape
  exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M ≪≫
    F.mapIso ψ ≪≫
    (SheafOfModules.mapFreeIso F ι (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm).symm⟩

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_free_affine_sections
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : AlgebraicGeometry.IsAffineOpen U) (_ : x ∈ U),
      Module.Free Γ(X, U) Γ(M, U) ∧ Module.Finite Γ(X, U) Γ(M, U)) :
    M.IsLocallyFree := by
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_restrict_free M fun x => ?_
  obtain ⟨U, hU, hxU, hfree, -⟩ := h x
  refine ⟨Spec Γ(X, U), hU.fromSpec, inferInstance, Module.Free.ChooseBasisIndex Γ(X, U) Γ(M, U), ?_,
    freeAffine.restrict_fromSpec_iso_free M hU _ (Module.Free.chooseBasis _ _)⟩
  rw [hU.range_fromSpec]
  exact hxU

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_free_affine_sections
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (h : ∀ x : X, ∃ (U : X.Opens) (_ : AlgebraicGeometry.IsAffineOpen U) (_ : x ∈ U),
      Module.Free Γ(X, U) Γ(M, U) ∧ Module.Finite Γ(X, U) Γ(M, U) ∧
        Module.finrank Γ(X, U) Γ(M, U) = n) (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n := by
  obtain ⟨U, hU, hxU, hfree, hfin, hn⟩ := h x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let b := Module.Free.chooseBasis Γ(X, U) Γ(M, U)
  obtain ⟨ψ⟩ := freeAffine.pullback_iso_free M hU _ b
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U _ ψ x hxU,
    ← Module.finrank_eq_card_basis b, hn]

/-- Pointwise version: only one affine chart at `x` is needed, and the ranks at different points need
not agree. On a smooth but disconnected scheme the relative dimensions of the charts may differ; this
is the form needed for Stacks 02G1. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_free_affine_sections_at
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (x : X)
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (hxU : x ∈ U)
    (hfree : Module.Free Γ(X, U) Γ(M, U)) (hfin : Module.Finite Γ(X, U) Γ(M, U))
    (hn : Module.finrank Γ(X, U) Γ(M, U) = n) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n := by
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let b := Module.Free.chooseBasis Γ(X, U) Γ(M, U)
  obtain ⟨ψ⟩ := freeAffine.pullback_iso_free M hU _ b
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U _ ψ x hxU,
    ← Module.finrank_eq_card_basis b, hn]

end
