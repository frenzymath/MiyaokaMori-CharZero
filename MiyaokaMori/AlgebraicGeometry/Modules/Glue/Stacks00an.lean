import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueKernel

/-! # Gluing sheaves of modules along an open cover (Stacks 00AL, 00AM, 00AN, 04TN)

Sheaves of `O`-modules `F_i` on the members `U_i` of an open cover, together with isomorphisms
`φ_ij` on the overlaps satisfying the cocycle condition, glue to a sheaf of modules `F` on `X`
with `F|_{U_i} ≅ F_i` compatibly with the `φ_ij`; the glued sheaf is unique up to isomorphism.
Morphisms of sheaves of modules given on each `U_i` and agreeing on overlaps glue uniquely to a
global morphism (two morphisms that agree on each `U_i` are equal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `(F|_W)|_V ≅ F|_V` for opens `V ≤ W ≤ Z` and `F` on `Z`, from `restrictFunctorComp` and
`restrictFunctorCongr` (`homOfLE_homOfLE`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.restrictRestrictIso {X : AlgebraicGeometry.Scheme.{u}}
    {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z) (F : Z.toScheme.Modules) :
    (F.restrict (X.homOfLE hWZ)).restrict (X.homOfLE hVW) ≅ F.restrict (X.homOfLE (hVW.trans hWZ)) :=
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp (X.homOfLE hVW) (X.homOfLE hWZ)).app F).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr (X.homOfLE_homOfLE hVW hWZ)).app F

/-- `(M|_W)|_V ≅ M|_V` for `M` on `X`; as above, using `homOfLE_ι`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.restrictιIso {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Opens} (h : V ≤ W) (M : X.Modules) :
    (M.restrict W.ι).restrict (X.homOfLE h) ≅ M.restrict V.ι :=
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι).app M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

/-- The cocycle condition: `φ_ii = 𝟙`, and on `U_ijl = U_i ⊓ U_j ⊓ U_l` we have
`φ_jl ∘ φ_ij = φ_il` (restrictions aligned via `restrictRestrictIso`; the `homOfLE` for different
proofs of `≤` are definitionally equal by proof irrelevance). -/

def AlgebraicGeometry.Scheme.Modules.IsModulesGlueCocycle {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : ∀ i, (U i).toScheme.Modules)
    (φ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ≅
      (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))) : Prop :=
  (∀ i, φ i i = CategoryTheory.Iso.refl _) ∧
  ∀ i j l,
    (AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) inf_le_left (F i)).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j))).mapIso (φ i j) ≪≫
      AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) inf_le_right (F j) ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l) inf_le_left (F j)).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l))).mapIso (φ j l) ≪≫
      AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l) inf_le_right (F l)
    = (AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l) inf_le_left (F i)).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l))).mapIso (φ i l) ≪≫
      AlgebraicGeometry.Scheme.Modules.restrictRestrictIso (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l) inf_le_right (F l)

/-- Gluing data for sheaves of modules (Stacks 00AL): a sheaf of modules on each open, isomorphisms
on the overlaps, and the cocycle condition. -/

structure AlgebraicGeometry.Scheme.Modules.GlueData {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) where
  F : ∀ i, (U i).toScheme.Modules
  φ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ≅
    (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))
  cocycle : AlgebraicGeometry.Scheme.Modules.IsModulesGlueCocycle U F φ

/-- The glued `M` is compatible with the gluing data: `φ_ij ∘ e_i = e_j` on `U_ij` (aligned via
`restrictιIso`). -/

def AlgebraicGeometry.Scheme.Modules.IsGlueCompatible {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (M : X.Modules)
    (e : ∀ i, M.restrict (U i).ι ≅ D.F i) (i j : ι) : Prop :=
  (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U i ⊓ U j ≤ U i) M).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).mapIso (e i) ≪≫ D.φ i j
    = (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) M).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).mapIso (e j)

/-- The morphisms `f_i`, `f_j` on the pieces agree on `U_ij`. -/

def AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M N : X.Modules) (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι) (i j : ι) : Prop :=
  (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U i ⊓ U j ≤ U i) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map (f i) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U i ⊓ U j ≤ U i) N).hom
    = (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map (f j) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) N).hom

/-- The section map of one side of `AgreeOnOverlap` (`f` restricted to `V' ≤ W` and aligned via
`restrictιIso`). -/
private theorem AlgebraicGeometry.Scheme.Modules.conj_restrictιIso_app {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) {M N : X.Modules} (φ : M.restrict W.ι ⟶ N.restrict W.ι)
    (A : V'.toScheme.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.restrictιIso h M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)).map φ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictιIso h N).hom).app A =
    M.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)).op ≫
      φ.app (X.homOfLE h ''ᵁ A) ≫
      N.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A).symm).op := by
  simp only [AlgebraicGeometry.Scheme.Modules.restrictιIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Hom.comp_app, restrictFunctorComp_hom_app_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    Category.assoc]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_cat5 _ _ _ _ _ _ _
    (AlgebraicGeometry.Scheme.Modules.glueAux_map2 M.presheaf _ _ _)
    (AlgebraicGeometry.Scheme.Modules.glueAux_map2 N.presheaf _ _ _)

/-- Gluing of morphisms (Stacks 04TN); proved first because `glue_unique` uses it. -/
private theorem AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom_aux {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j, AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap U M N f i j) :
    ∃! g : M ⟶ N, ∀ i, (AlgebraicGeometry.Scheme.Modules.restrictFunctor (U i).ι).map g = f i := by
  have hsec : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (f i) V hi =
        AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (f j) V hj := by
    intro i j V hi hj
    have e1 := AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_eq_of_app_eq
      (inf_le_left : U i ⊓ U j ≤ U i) (f i) _
      (AlgebraicGeometry.Scheme.Modules.conj_restrictιIso_app _ (f i)) V (le_inf hi hj)
    have e2 := AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_eq_of_app_eq
      (inf_le_right : U i ⊓ U j ≤ U j) (f j) _
      (AlgebraicGeometry.Scheme.Modules.conj_restrictιIso_app _ (f j)) V (le_inf hi hj)
    exact e1.symm.trans ((congrArg (fun ψ =>
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom ψ V (le_inf hi hj)) (hf i j)).trans e2)
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_of_sectionMap_agree U hU M N f hsec
  have hg' : ∀ i, (AlgebraicGeometry.Scheme.Modules.restrictFunctor (U i).ι).map g = f i := fun i =>
    AlgebraicGeometry.Scheme.Modules.restrict_map_eq_of_app_eq_sectionMap g (f i) (hg i)
  refine ⟨g, hg', fun g' h' => ?_⟩
  exact AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hU g' g (fun i => (h' i).trans (hg' i).symm)

/-- Between two compatible gluings `(M, e)`, `(M', e')`, the morphisms `e_i ≫ e'_i⁻¹` on the
pieces agree on overlaps. -/
private theorem AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isGlueCompatible
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (D : AlgebraicGeometry.Scheme.Modules.GlueData U)
    (M M' : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ D.F i) (e' : ∀ i, M'.restrict (U i).ι ≅ D.F i)
    (he : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M e i j)
    (he' : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M' e' i j) (i j : ι) :
    AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap U M M' (fun i => (e i).hom ≫ (e' i).inv) i j := by
  have h1 := he i j
  have h2 := he' i j
  unfold AlgebraicGeometry.Scheme.Modules.IsGlueCompatible at h1 h2
  unfold AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap
  have key := congrArg Iso.hom (congrArg₂ (fun a b => a ≪≫ b.symm) h1 h2)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc] at key
  simp only [Functor.map_comp, Category.assoc]
  exact key

/-- The section map on `A` of a single transition isomorphism (restricted to `T ≤ W` and aligned via
`restrictRestrictIso`), expressed through `overlapSectionMap`. -/
private theorem AlgebraicGeometry.Scheme.Modules.conj_restrictRestrictIso_app
    {X : AlgebraicGeometry.Scheme.{u}} {T W W₁ W₂ : X.Opens} (h : T ≤ W) (h₁ : W ≤ W₁) (h₂ : W ≤ W₂)
    {F₁ : W₁.toScheme.Modules} {F₂ : W₂.toScheme.Modules}
    (θ : F₁.restrict (X.homOfLE h₁) ⟶ F₂.restrict (X.homOfLE h₂)) (A : T.toScheme.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.restrictRestrictIso h h₁ F₁).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)).map θ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictRestrictIso h h₂ F₂).hom).app A =
    F₁.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image
        (h.trans h₁) A rfl)).op ≫
      AlgebraicGeometry.Scheme.Modules.overlapSectionMap h₁ h₂ θ (T.ι ''ᵁ A)
        ((AlgebraicGeometry.Scheme.Modules.le_of_image_eq A rfl).trans h) ≫
      F₂.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.preimage_image_eq_homOfLE_image
        (h.trans h₂) A rfl).symm).op := by
  have hθ := AlgebraicGeometry.Scheme.Modules.app_eq_overlapSectionMap h₁ h₂ θ (X.homOfLE h ''ᵁ A)
    (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)
  simp only [AlgebraicGeometry.Scheme.Modules.restrictRestrictIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Hom.comp_app,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app, Category.assoc]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_cat16 _ _ _ _ _ _ _ _ _ _ hθ
    (AlgebraicGeometry.Scheme.Modules.glueAux_map3 F₁.presheaf _ _ _ _)
    (AlgebraicGeometry.Scheme.Modules.glueAux_map3 F₂.presheaf _ _ _ _)

/-- The cocycle condition on sections: for `V ≤ U_ijl`, the section maps of `φ_ij`, `φ_jl`, `φ_il`
on `V` satisfy `φ_jl ∘ φ_ij = φ_il`. -/
private theorem AlgebraicGeometry.Scheme.Modules.GlueData.overlap_cocycle
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (i j l : ι) (V : X.Opens)
    (hV : V ≤ U i ⊓ U j ⊓ U l) :
    AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i j).hom V
        (hV.trans inf_le_left) ≫
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
  have e_ij : _ = L ≫ o1 ≫ Mj := AlgebraicGeometry.Scheme.Modules.conj_restrictRestrictIso_app
    (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) inf_le_left inf_le_right (D.φ i j).hom A
  have e_jl : _ = Mj' ≫ o2 ≫ R := AlgebraicGeometry.Scheme.Modules.conj_restrictRestrictIso_app
    (inf_le_inf_right _ inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l) inf_le_left inf_le_right
    (D.φ j l).hom A
  have e_il : _ = L ≫ o3 ≫ R := AlgebraicGeometry.Scheme.Modules.conj_restrictRestrictIso_app
    (inf_le_inf_right _ inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l) inf_le_left inf_le_right
    (D.φ i l).hom A
  have h := congrArg (fun e => e.hom) (D.cocycle.2 i j l)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
  have h' := congrArg (fun f => AlgebraicGeometry.Scheme.Modules.Hom.app f A) h
  simp only [Hom.comp_app] at h' e_ij e_jl e_il
  rw [reassoc_of% e_ij, e_jl, e_il] at h'
  have hm : Mj ≫ Mj' = 𝟙 _ := AlgebraicGeometry.Scheme.Modules.glueAux_map2_endo (D.F j).presheaf _ _
  have hL : IsIso L := inferInstance
  have hR : IsIso R := inferInstance
  exact AlgebraicGeometry.Scheme.Modules.glueAux_cat17 L o1 Mj Mj' o2 R o3 (inv L) (inv R) h' hm
    (IsIso.inv_hom_id L) (IsIso.hom_inv_id R)

/-- The section map on `A` of the inverse of `restrictιIso` is the restriction map of `M`
(the two opens are equal). -/
private theorem AlgebraicGeometry.Scheme.Modules.restrictιIso_inv_app {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) (M : X.Modules) (A : V'.toScheme.Opens) :
    (AlgebraicGeometry.Scheme.Modules.restrictιIso h M).inv.app A =
      M.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)).op := by
  simp only [AlgebraicGeometry.Scheme.Modules.restrictιIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
    Iso.app_inv, Hom.comp_app, restrictFunctorComp_hom_app_app, restrictFunctorCongr_inv_app_app]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_map2 M.presheaf _ _ _

/-- Existence of the glued sheaf (Stacks 00AN): gluing data glue to a sheaf of modules `M` with
compatible isomorphisms `M|_{U_i} ≅ F_i`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_glue {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (D : AlgebraicGeometry.Scheme.Modules.GlueData U) :
    ∃ (M : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ D.F i),
      ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M e i j := by
  have hrefl : ∀ i (V : X.Opens) (hV : V ≤ U i ⊓ U i),
      AlgebraicGeometry.Scheme.Modules.overlapSectionMap inf_le_left inf_le_right (D.φ i i).hom V hV =
        𝟙 _ := by
    intro i V hV
    rw [D.cocycle.1 i]
    exact AlgebraicGeometry.Scheme.Modules.overlapSectionMap_id inf_le_left (D.F i) V hV
  have hc := AlgebraicGeometry.Scheme.Modules.isSectionwiseGlue_glueKernel U D.F
    (fun i j => (D.φ i j).hom)
  obtain ⟨e, he⟩ := hc.exists_iso hrefl (fun i j l V hV => D.overlap_cocycle i j l V hV)
  refine ⟨AlgebraicGeometry.Scheme.Modules.glueKernel U D.F (fun i j => (D.φ i j).hom), e,
    fun i j => ?_⟩
  unfold AlgebraicGeometry.Scheme.Modules.IsGlueCompatible
  apply Iso.ext
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro A
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.restrictιIso_inv_app]
  exact he i j A

/-- Uniqueness of the glued sheaf: two compatible gluings are isomorphic. -/
theorem AlgebraicGeometry.Scheme.Modules.glue_unique {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (D : AlgebraicGeometry.Scheme.Modules.GlueData U)
    (M M' : X.Modules) (e : ∀ i, M.restrict (U i).ι ≅ D.F i) (e' : ∀ i, M'.restrict (U i).ι ≅ D.F i)
    (he : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M e i j)
    (he' : ∀ i j, AlgebraicGeometry.Scheme.Modules.IsGlueCompatible U D M' e' i j) :
    ∃ g : M ≅ M', ∀ i, (AlgebraicGeometry.Scheme.Modules.restrictFunctor (U i).ι).mapIso g ≪≫ e' i = e i := by
  obtain ⟨g, hg, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom_aux U hU M M'
    (fun i => (e i).hom ≫ (e' i).inv)
    (AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isGlueCompatible U D M M' e e' he he')
  obtain ⟨h, hh, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom_aux U hU M' M
    (fun i => (e' i).hom ≫ (e i).inv)
    (AlgebraicGeometry.Scheme.Modules.agreeOnOverlap_of_isGlueCompatible U D M' M e' e he' he)
  have hgh : g ≫ h = 𝟙 M := AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hU _ _ (fun i => by
    rw [Functor.map_comp, hg, hh, CategoryTheory.Functor.map_id]; simp)
  have hhg : h ≫ g = 𝟙 M' := AlgebraicGeometry.Scheme.Modules.hom_ext_of_cover U hU _ _ (fun i => by
    rw [Functor.map_comp, hg, hh, CategoryTheory.Functor.map_id]; simp)
  refine ⟨⟨g, h, hgh, hhg⟩, fun i => ?_⟩
  ext1
  simp only [Iso.trans_hom, Functor.mapIso_hom, hg]
  simp

/-- Gluing of morphisms (Stacks 04TN): morphisms given on the pieces and agreeing on overlaps
glue uniquely to a global morphism. -/
theorem AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j, AlgebraicGeometry.Scheme.Modules.AgreeOnOverlap U M N f i j) :
    ∃! g : M ⟶ N, ∀ i, (AlgebraicGeometry.Scheme.Modules.restrictFunctor (U i).ι).map g = f i :=
  AlgebraicGeometry.Scheme.Modules.existsUnique_glue_hom_aux U hU M N f hf

end
