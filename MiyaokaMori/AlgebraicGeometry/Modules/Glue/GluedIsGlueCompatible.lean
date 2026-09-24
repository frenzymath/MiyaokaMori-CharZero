import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueConstruction
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.Stacks00an

/-! # The glued sheaf is compatible with its gluing data

`AlgebraicGeometry.Scheme.Modules.GlueData.glued` (the kernel construction of Stacks 00AL) comes
with block isomorphisms compatible with the gluing data: there are `e_i : glued|_{U_i} ≅ F_i`
with `IsGlueCompatible U D glued e i j` for all `i j`.

`exists_glue` (Stacks 00AN) proves that *some* `M` exists, and its witness is by definition
`glueKernel U D.F (fun i j => (D.φ i j).hom) = D.glued`; this file makes the witness explicit,
repeating the proof of `exists_glue` (with the three private auxiliary lemmas of
`Stacks00an.lean`), so that `glue_unique` can be applied to `bundleFamilyOfCocycle` (= `glued`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- (Copy of the private `conj_restrictRestrictIso_app` of `Stacks00an.lean`.)
The section map on `A` of a single transition isomorphism (restricted to `T ≤ W` and aligned via
`restrictRestrictIso`), expressed through `overlapSectionMap`. -/
private theorem AlgebraicGeometry.Scheme.Modules.gluedCompat_conj_restrictRestrictIso_app
    {X : AlgebraicGeometry.Scheme.{u}} {T W W₁ W₂ : X.Opens} (h : T ≤ W) (h₁ : W ≤ W₁) (h₂ : W ≤ W₂)
    {F₁ : W₁.toScheme.Modules} {F₂ : W₂.toScheme.Modules}
    (θ : F₁.restrict (X.homOfLE h₁) ⟶ F₂.restrict (X.homOfLE h₂)) (A : T.toScheme.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.restrictRestrictIso h h₁ F₁).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)).map θ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictRestrictIso h h₂ F₂).hom).app A =
    F₁.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image (h.trans h₁) A rfl)).op ≫
      AlgebraicGeometry.Scheme.Modules.overlapSectionMap h₁ h₂ θ (T.ι ''ᵁ A) ((AlgebraicGeometry.Scheme.Modules.le_of_image_eq A rfl).trans h) ≫
      F₂.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image (h.trans h₂) A rfl).symm).op := by
  have hθ := AlgebraicGeometry.Scheme.Modules.app_eq_overlapSectionMap h₁ h₂ θ (X.homOfLE h ''ᵁ A) (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)
  simp only [AlgebraicGeometry.Scheme.Modules.restrictRestrictIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app, AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_inv_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_hom_app_app, AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app, Category.assoc]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_cat16 _ _ _ _ _ _ _ _ _ _ hθ
    (AlgebraicGeometry.Scheme.Modules.glueAux_map3 F₁.presheaf _ _ _ _)
    (AlgebraicGeometry.Scheme.Modules.glueAux_map3 F₂.presheaf _ _ _ _)

/-- (Copy of the private `GlueData.overlap_cocycle` of `Stacks00an.lean`.)
The cocycle condition on sections: for `V ≤ U_ijl`, the section maps of `φ_ij`, `φ_jl`, `φ_il`
on `V` satisfy `φ_jl ∘ φ_ij = φ_il`. -/
private theorem AlgebraicGeometry.Scheme.Modules.gluedCompat_overlap_cocycle
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (i j l : ι) (V : X.Opens)
    (hV : V ≤ U i ⊓ U j ⊓ U l) :
    AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i j).hom V (hV.trans inf_le_left) ≫
      AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ j l).hom V
        (hV.trans (inf_le_inf_right _ inf_le_right)) =
    AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i l).hom V
        (hV.trans (inf_le_inf_right _ inf_le_left)) := by
  obtain ⟨A, rfl⟩ : ∃ A : (U i ⊓ U j ⊓ U l).toScheme.Opens, (U i ⊓ U j ⊓ U l).ι ''ᵁ A = V :=
    ⟨(U i ⊓ U j ⊓ U l).ι ⁻¹ᵁ V, by
      rw [AlgebraicGeometry.Scheme.Modules.image_preimage_inf_aux, inf_eq_left.mpr hV]⟩
  have hi : U i ⊓ U j ⊓ U l ≤ U i := inf_le_left.trans inf_le_left
  have hj : U i ⊓ U j ⊓ U l ≤ U j := inf_le_left.trans inf_le_right
  have hl : U i ⊓ U j ⊓ U l ≤ U l := inf_le_right
  have pi : (U i).ι ⁻¹ᵁ (U i ⊓ U j ⊓ U l).ι ''ᵁ A = X.homOfLE hi ''ᵁ A :=
    AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image hi A rfl
  have pj : (U j).ι ⁻¹ᵁ (U i ⊓ U j ⊓ U l).ι ''ᵁ A = X.homOfLE hj ''ᵁ A :=
    AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image hj A rfl
  have pl : (U l).ι ⁻¹ᵁ (U i ⊓ U j ⊓ U l).ι ''ᵁ A = X.homOfLE hl ''ᵁ A :=
    AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image hl A rfl
  let L := (D.F i).presheaf.map (eqToHom pi).op
  let Mj := (D.F j).presheaf.map (eqToHom pj.symm).op
  let Mj' := (D.F j).presheaf.map (eqToHom pj).op
  let R := (D.F l).presheaf.map (eqToHom pl.symm).op
  let o1 := AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i j).hom
    ((U i ⊓ U j ⊓ U l).ι ''ᵁ A) (hV.trans inf_le_left)
  let o2 := AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ j l).hom
    ((U i ⊓ U j ⊓ U l).ι ''ᵁ A) (hV.trans (inf_le_inf_right _ inf_le_right))
  let o3 := AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i l).hom
    ((U i ⊓ U j ⊓ U l).ι ''ᵁ A) (hV.trans (inf_le_inf_right _ inf_le_left))
  have e_ij : _ = L ≫ o1 ≫ Mj := AlgebraicGeometry.Scheme.Modules.gluedCompat_conj_restrictRestrictIso_app
    (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) inf_le_left inf_le_right (D.φ i j).hom A
  have e_jl : _ = Mj' ≫ o2 ≫ R := AlgebraicGeometry.Scheme.Modules.gluedCompat_conj_restrictRestrictIso_app
    (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l) inf_le_left inf_le_right
    (D.φ j l).hom A
  have e_il : _ = L ≫ o3 ≫ R := AlgebraicGeometry.Scheme.Modules.gluedCompat_conj_restrictRestrictIso_app
    (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l) inf_le_left inf_le_right
    (D.φ i l).hom A
  have h := congrArg (fun e => e.hom) (D.cocycle.2 i j l)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
  have h' := congrArg (fun f => AlgebraicGeometry.Scheme.Modules.Hom.app f A) h
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app] at h' e_ij e_jl e_il
  rw [reassoc_of% e_ij, e_jl, e_il] at h'
  have hm : Mj ≫ Mj' = 𝟙 _ := AlgebraicGeometry.Scheme.Modules.glueAux_map2_endo (D.F j).presheaf _ _
  have hL : IsIso L := inferInstance
  have hR : IsIso R := inferInstance
  exact AlgebraicGeometry.Scheme.Modules.glueAux_cat17 L o1 Mj Mj' o2 R o3 (inv L) (inv R) h' hm
    (IsIso.inv_hom_id L) (IsIso.hom_inv_id R)

/-- (Copy of the private `restrictιIso_inv_app` of `Stacks00an.lean`.)
The section map on `A` of the inverse of `restrictιIso` is the restriction map of `M` (the two
opens are equal). -/
private theorem AlgebraicGeometry.Scheme.Modules.gluedCompat_restrictιIso_inv_app {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) (M : X.Modules) (A : V'.toScheme.Opens) :
    (AlgebraicGeometry.Scheme.Modules.restrictιIso h M).inv.app A =
      M.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)).op := by
  simp only [AlgebraicGeometry.Scheme.Modules.restrictιIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
    Iso.app_inv, AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app, AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_map2 M.presheaf _ _ _

/-- `D.glued` is by definition `glueKernel U D.F (fun i j => (D.φ i j).hom)`
(`pushforwardRestrictMap` and `pushforwardRestrictHom` have the same body; see
`ModulesGlueKernel.lean`). -/
theorem AlgebraicGeometry.Scheme.Modules.GlueData.glued_eq_glueKernel {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) :
    D.glued = AlgebraicGeometry.Scheme.Modules.glueKernel U D.F (fun i j => (D.φ i j).hom) := rfl

/-- `GlueData.glued` is compatible with its gluing data: there are block isomorphisms
`e_i : D.glued|_{U_i} ≅ D.F i` with `φ_ij ∘ e_i = e_j` on overlaps (`IsGlueCompatible`).

Reference: Stacks 00AL. The proof is that of `exists_glue` (whose witness
`glueKernel U D.F (fun i j => (D.φ i j).hom)` is by definition `D.glued`):
`isSectionwiseGlue_glueKernel` says that `(glued, block projections)` is sectionwise an
equalizer; the cocycle condition (reflexive part from `D.cocycle.1` and `overlapSectionMap_id`,
triple-overlap part from `D.cocycle.2` via the section form `overlap_cocycle`) gives
`IsSectionwiseGlue.exists_iso`, whose compatibility is exactly `IsGlueCompatible` unfolded
sectionwise (the inverse of `restrictιIso` is the restriction map on every open). -/
theorem AlgebraicGeometry.Scheme.Modules.GlueData.exists_glued_iso {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (D : AlgebraicGeometry.Scheme.Modules.GlueData U) :
    ∃ e : ∀ i, D.glued.restrict (U i).ι ≅ D.F i,
      ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D D.glued e i j := by
  have hrefl : ∀ i (V : X.Opens) (hV : V ≤ U i ⊓ U i),
      AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i i).hom V hV = 𝟙 _ := by
    intro i V hV
    rw [D.cocycle.1 i]
    exact AlgebraicGeometry.Scheme.Modules.overlapSectionMap_id inf_le_left (D.F i) V hV
  have hc := AlgebraicGeometry.Scheme.Modules.isSectionwiseGlue_glueKernel U D.F (fun i j => (D.φ i j).hom)
  rw [D.glued_eq_glueKernel]
  obtain ⟨e, he⟩ := hc.exists_iso hrefl (fun i j l V hV => AlgebraicGeometry.Scheme.Modules.gluedCompat_overlap_cocycle D i j l V hV)
  refine ⟨e, fun i j => ?_⟩
  unfold AlgebraicGeometry.Scheme.Modules.IsGlueCompatible
  apply Iso.ext
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro A
  simp only [Iso.trans_hom, Iso.symm_hom, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.gluedCompat_restrictιIso_inv_app]
  exact he i j A

end
