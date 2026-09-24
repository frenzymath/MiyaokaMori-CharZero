import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjBaseChangeTwistCone
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison

/-! # The local comparison maps of the base-changed twisting sheaf are isomorphisms

Statement: the local comparison map `σ_i = bcSigma[g, 𝒜, d, i] : (φ^* O_{Proj_S 𝒜}(d))|_{Proj (g^*𝒜)(V)} ⟶
O_{Proj (g^*𝒜)(V)}(d)` of `RelativeProjBaseChangeTwistCone` is an isomorphism, for every small
chart `i = (U, V)` (Stacks 01O3 on a chart, via 01N2 and 01LI); hence so is `ψ_i = bcPsi[g, 𝒜, d, i]`.

Proof. `σ_i` is the transpose of `c_i = twistπ d U ≫ twistPushTransition ψ_i` along the composite
adjunction `pullback φ ⋙ restrictFunctor ι'_V ⊣ pushforward ι'_V ⋙ pushforward φ`. The right adjoint
is isomorphic (`pushforwardComp`, `pushforwardCongr` along `ι'_V ≫ φ = ψ_i ≫ ι_U`) to
`pushforward ψ_i ⋙ pushforward ι_U`, the right adjoint of `restrictFunctor ι_U ⋙ pullback ψ_i`; so by
uniqueness of left adjoints (`Adjunction.leftAdjointUniq`) the two left adjoints are isomorphic and the
transposes correspond (`Adjunction.homEquiv_symm_eq_leftAdjointUniq'`). Under this identification
`σ_i` becomes `(pullback ψ_i).map τ_U ≫ twistPullbackHom ψ_i`, where `τ_U : O(d)|_{Proj 𝒜(U)} ≅ O_U(d)`
(Stacks 01LI, `isIso_restrictTranspose_twistπ`) and `twistPullbackHom ψ_i` is the θ of Stacks 01MX, an
isomorphism by Stacks 01N2 (`isIso_baseChangeProjMap_twistPullbackHom`). The bookkeeping identity `twistBaseChangeSigma_eq` is proved
with the naturality of `homEquiv` and the section-level triviality of `pushforwardComp`/`pushforwardCongr`.

Source: Stacks 01O3, 01N2, 01MX, 01LI; Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Undoing the identifications in a transition map: `T(f) ≫ pushforwardCongr w.symm ≫ pushforwardComp.inv`
is `(ι_A)_* θ_f` (all these maps are identities on sections). -/
theorem twistPushTransition_comp_congr_inv (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB) :
    twistPushTransition f hf n ιA ιB w ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr w.symm).hom.app (twist ℬ n) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (AlgebraicGeometry.Proj.map f hf) ιA).inv.app
        (twist ℬ n) =
    (AlgebraicGeometry.Scheme.Modules.pushforward ιA).map (twistToPushforward f hf n) := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  simp only [twistPushTransition, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_inv_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app, Category.assoc]
  erw [Category.id_comp, Category.comp_id]
  erw [AlgebraicGeometry.Scheme.Modules.glueAux_map2 (twist ℬ n).presheaf _ _ (𝟙 _),
    (twist ℬ n).presheaf.map_id]
  exact Category.comp_id _

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.Modules


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra) (d : ℤ)
  (i : BaseChangeChartIndex g)

/-- Variable-level shape of `h4` in `twistBaseChangeSigma_eq` (the concrete functors enter through `exact`,
so that the kernel compares small variable-level terms instead of unfolding them). -/
private theorem h4_aux {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F₁ F₂ F₃ F₄ : C ⥤ D} (α : F₁ ≅ F₂) (β : F₂ ≅ F₃) (γ : F₄ ≅ F₃) {X : C} {W A : D}
    (t : W ⟶ A) (T : A ⟶ F₂.obj X) :
    ((t ≫ T) ≫ α.inv.app X) ≫ (α ≪≫ β ≪≫ γ.symm).hom.app X =
      t ≫ T ≫ β.hom.app X ≫ γ.inv.app X := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]

/-! The identification of right adjoints `bcE[g, 𝒜, i] : (ι'_V)_* ⋙ φ_* ≅ (ψ_i)_* ⋙ (ι_U)_*` and the two
composite adjunctions `bcAdjL`, `bcAdjR` are notation (not definitions), for the same reason as in
`RelativeProjBaseChangeTwistCone`. -/

set_option quotPrecheck false in
scoped notation "bcE[" g ", " 𝒜 ", " i "]" =>
  Modules.pushforwardComp (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2) (baseChangeHom' g 𝒜) ≪≫
    Modules.pushforwardCongr (projMap_baseChangeUnit_comp_projChart g 𝒜 i).symm ≪≫
    (Modules.pushforwardComp (Proj.map (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i))
      ((𝒜).toGradedAffineAlgebra.projChart (i).1.1)).symm

set_option quotPrecheck false in
scoped notation "bcAdjL[" g ", " 𝒜 ", " i "]" =>
  (Modules.pullbackPushforwardAdjunction (baseChangeHom' g 𝒜)).comp
    (Modules.restrictAdjunction (((𝒜).pullback g).toGradedAffineAlgebra.projChart (i).1.2))

set_option quotPrecheck false in
scoped notation "bcAdjR[" g ", " 𝒜 ", " i "]" =>
  (Modules.restrictAdjunction ((𝒜).toGradedAffineAlgebra.projChart (i).1.1)).comp
    (Modules.pullbackPushforwardAdjunction (Proj.map (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i)))

/-- **The local comparison map through the pullback functors**: `σ_i` is, up to the canonical
identification of the left adjoints, `(pullback ψ_i).map τ_U ≫ twistPullbackHom ψ_i`. -/
theorem twistBaseChangeSigma_eq :
    bcSigma[g, 𝒜, d, i] =
      (Adjunction.leftAdjointUniq (bcAdjL[g, 𝒜, i].ofNatIsoRight bcE[g, 𝒜, i]) bcAdjR[g, 𝒜, i]).hom.app _ ≫
      (Modules.pullback (Proj.map (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i))).map (Modules.restrictTranspose (𝒜.toGradedAffineAlgebra.projChart i.1.1) (𝒜.toGradedAffineAlgebra.twistπ d i.1.1)) ≫
      Proj.twistPullbackHom (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d := by
  have h1 : bcSigma[g, 𝒜, d, i] = (bcAdjL[g, 𝒜, i].homEquiv _ _).symm bcLeg'[g, 𝒜, d, i] := by
    rw [Adjunction.comp_homEquiv, Modules.restrictTranspose]
    rfl
  have h2 : (bcAdjL[g, 𝒜, i].homEquiv _ _).symm bcLeg'[g, 𝒜, d, i] =
      ((bcAdjL[g, 𝒜, i].ofNatIsoRight bcE[g, 𝒜, i]).homEquiv _ _).symm
        (bcLeg'[g, 𝒜, d, i] ≫ bcE[g, 𝒜, i].hom.app _) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
    congr 1
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have h3 := Adjunction.homEquiv_symm_eq_leftAdjointUniq' (bcAdjL[g, 𝒜, i].ofNatIsoRight bcE[g, 𝒜, i])
    bcAdjR[g, 𝒜, i] (bcLeg'[g, 𝒜, d, i] ≫ bcE[g, 𝒜, i].hom.app _)
  have h4 : bcLeg'[g, 𝒜, d, i] ≫ bcE[g, 𝒜, i].hom.app _ =
      𝒜.toGradedAffineAlgebra.twistπ d i.1.1 ≫
        (Modules.pushforward (𝒜.toGradedAffineAlgebra.projChart i.1.1)).map
          (Proj.twistToPushforward (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d) :=
    (h4_aux _ _ _ _ _).trans (congrArg (fun y => 𝒜.toGradedAffineAlgebra.twistπ d i.1.1 ≫ y)
      (Proj.twistPushTransition_comp_congr_inv (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d
        _ _ (projMap_baseChangeUnit_comp_projChart g 𝒜 i)))
  have h5 : (bcAdjR[g, 𝒜, i].homEquiv _ _).symm (𝒜.toGradedAffineAlgebra.twistπ d i.1.1 ≫
        (Modules.pushforward (𝒜.toGradedAffineAlgebra.projChart i.1.1)).map
          (Proj.twistToPushforward (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d)) =
      (Modules.pullback (Proj.map (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i))).map (Modules.restrictTranspose (𝒜.toGradedAffineAlgebra.projChart i.1.1) (𝒜.toGradedAffineAlgebra.twistπ d i.1.1)) ≫
      Proj.twistPullbackHom (baseChangeUnit g 𝒜 i) (baseChangeUnit_irrelevant_le g 𝒜 i) d := by
    rw [Adjunction.comp_homEquiv]
    dsimp only [Equiv.symm_trans_apply]
    rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
      Modules.restrictTranspose, Proj.twistPullbackHom]
  rw [h1, h2, h3, h4, h5]

/-- **Stacks 01O3 on a chart**: the local comparison map `σ_i` is an isomorphism. -/
theorem isIso_twistBaseChangeSigma : IsIso bcSigma[g, 𝒜, d, i] := by
  rw [twistBaseChangeSigma_eq]
  haveI := 𝒜.toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.1
  haveI := isIso_twistPullbackHom_baseChangeUnit g 𝒜 d i
  infer_instance

/-- The local comparison map `ψ_i = σ_i ≫ τ_V⁻¹` is an isomorphism. -/
theorem isIso_twistBaseChangePsi :
    haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.2
    IsIso bcPsi[g, 𝒜, d, i] := by
  haveI := isIso_twistBaseChangeSigma g 𝒜 d i
  haveI := (𝒜.pullback g).toGradedAffineAlgebra.isIso_restrictTranspose_twistπ d i.1.2
  infer_instance

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
