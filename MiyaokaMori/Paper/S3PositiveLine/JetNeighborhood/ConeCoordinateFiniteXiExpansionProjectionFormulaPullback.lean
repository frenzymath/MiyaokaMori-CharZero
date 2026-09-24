import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # The projection formula on a pulled-back section, pointwise

**Pulling back a section along a morphism = acting on the coefficient by the ring map** (variable level;
no relative Spec involved). For `j : S → Y`, a module `N` on `Y`, write `θ_j := projectionFormulaHom j N O_S :
N ⊗ j_*O_S → j_*(j^*N ⊗ O_S)` and `j^♯ := unitToPushforwardObjUnit : O_Y → j_*O_S` (the ring map of `j`).
Then `(N ◁ j^♯) ≫ θ_j = (ρ_ N).hom ≫ η_j ≫ j_*((ρ_ (j^*N)).inv)`
(`whiskerLeft_unitToPushforward_comp_projectionFormulaHom`), i.e. on global sections
`θ_j (s ⊗ j^♯(1)) = (j^*s) ⊗ 1` (`projectionFormulaHom_whiskerLeft_unitToPushforward_apply`).
Proof (`Adjunction.whiskerLeft_comp_projFormulaHom_unit`, for any adjunction `F ⊣ G` with `F` oplax monoidal):
`θ` is the adjoint transpose of `δ ≫ (F N ◁ ε)`; by naturality of the transpose in the first variable,
`(N ◁ u) ≫ θ` is the transpose of `F(N ◁ u) ≫ δ ≫ (F N ◁ ε) = δ ≫ (F N ◁ (F u ≫ ε))` (`δ_natural_right`), and
`F u ≫ ε = η` when `u` is the transpose of the oplax unit `η` (for `j^*`: Mathlib `pullbackObjUnitToUnit`,
`pullback_η`), so oplax right unitality gives `F((ρ_ N).hom) ≫ (ρ_ (F N)).inv`, whose transpose is
`(ρ_ N).hom ≫ η_adj ≫ G((ρ_ (F N)).inv)`.

Consequences (all proved here):
* `sectionPullbackAlong_id_eq_pullbackId_inv`: `𝟙^*s = (pullbackId X).inv s` (mate of `pullbackId`,
  Mathlib `conjugateEquiv_pullbackId_hom`, `unit_conjugateEquiv`).
* `unitToPushforward_comp_pushforward_map_comp_pushforwardComp`: `p^♯ ≫ p_*(j^♯) ≫ pushforwardComp = (j ≫ p)^♯`
  (ring maps compose); `unitToPushforward_comp_pushforwardCongr` (transport along `f = g`);
  `pushforwardCongr_rfl_hom_app_unit` (`pushforwardCongr rfl` is the identity on the structure sheaf);
  `unitToPushforward_id_comp_pushforwardId`: `𝟙^♯ ≫ pushforwardId = 𝟙`.
* **Main** (`rightUnitor_whiskerLeft_eq_pullback_section_of_comp_eq_id`, for a section `j` of `p`, i.e.
  `j ≫ p = 𝟙`): for `Q ∈ Γ(X, M ⊗ p_*O_Y)`, `ρ((M ◁ (p_*(j^♯) ≫ C)) Q) = Φ(j^*(pushforwardSectionToPullback p M Q))`,
  where `C : p_*j_*O_X → O_X` and `Φ : j^*p^*M → M` are the pseudofunctor identifications
  (`pushforwardComp`, `pushforwardCongr`, `pushforwardId`; `pullbackComp`, `pullbackCongr`, `pullbackId`).
  Proof: put `m := LHS`; since `C ≫ p^♯ ≫ p_*(j^♯) = 𝟙`, `(M ◁ p_*j^♯) Q = (M ◁ (p^♯ ≫ p_*j^♯)) (m ⊗ 1)`; then
  `θ_p` is natural in the second variable (`projFormulaHom_naturality_right`) and the two applications of the
  element form of G0 (to `p` and to `j`) give `j^*(pushforwardSectionToPullback p M Q) = j^*(p^*m)`, and
  `Φ(j^*(p^*m)) = m` by `pullback_comp`, `pullbackCongr_apply`, `sectionPullbackAlong_id_eq_pullbackId_inv`.
  This is the common core of `xiCoefficientThickening_zero_eq_restrictToZeroSection`
  (`ConeCoordinateFiniteXiExpansionZeroSection`) and `xiCoefficient_zero_eq_zeroSection` (`TotSectionsPolynomial`).

Source: Stacks 01E8 (projection formula) and its naturality; proved directly (pure adjunction/monoidal algebra).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [instF : F.OplaxMonoidal]

/-- **Abstract G0.** If `u : 𝟙 ⟶ G 𝟙` is the transpose of the oplax unit `η`, then
`(N ◁ u) ≫ θ_{N,𝟙} = (ρ_ N).hom ≫ unit_N ≫ G((ρ_ (F N)).inv)`. -/
theorem whiskerLeft_comp_projFormulaHom_unit (N : C) (u : 𝟙_ C ⟶ G.obj (𝟙_ D))
    (hu : (adj.homEquiv _ _).symm u = Functor.OplaxMonoidal.η F) :
    (N ◁ u) ≫ adj.projFormulaHom N (𝟙_ D) =
      (ρ_ N).hom ≫ adj.unit.app N ≫ G.map (ρ_ (F.obj N)).inv := by
  unfold projFormulaHom
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_unit,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_right, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← Adjunction.homEquiv_counit, hu]
  exact (Iso.eq_comp_inv _).mpr (by
    rw [Category.assoc]
    exact Functor.OplaxMonoidal.right_unitality_hom (F := F) N)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

variable {S Y : AlgebraicGeometry.Scheme.{u}}

/-- The adjoint transpose of `(pullbackUnitIso j).hom` (= oplax unit `η`) is the ring map `j^♯`
(Mathlib `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`). -/
theorem homEquiv_pullbackUnitIso_hom_ccp (j : S ⟶ Y) :
    (pullbackPushforwardAdjunction j).homEquiv _ _ (pullbackUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom :=
  haveI : (SheafOfModules.pushforward.{u} j.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction j).isRightAdjoint
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u} j.toRingCatSheafHom

/-- The ring map `j^♯ : 𝟙 ⟶ j_* 𝟙` is the transpose of the oplax unit `η` of `j^*`. -/
theorem homEquiv_symm_unitToPushforward (j : S ⟶ Y) :
    ((pullbackPushforwardAdjunction j).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      Functor.OplaxMonoidal.η (pullback j) (self := pullbackOplaxMonoidal j) :=
  ((Equiv.symm_apply_eq _).mpr (homEquiv_pullbackUnitIso_hom_ccp j).symm).trans (pullback_η j).symm

/-- **G0 (morphism form)**: `(N ◁ j^♯) ≫ θ_j = (ρ_ N).hom ≫ η_j ≫ j_*((ρ_ (j^*N)).inv)`. -/
theorem whiskerLeft_unitToPushforward_comp_projectionFormulaHom (j : S ⟶ Y) (N : Y.Modules) :
    (N ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        projectionFormulaHom j N (𝟙_ S.Modules) =
      (ρ_ N).hom ≫ (pullbackPushforwardAdjunction j).unit.app N ≫
        (pushforward j).map (ρ_ ((pullback j).obj N)).inv :=
  (pullbackPushforwardAdjunction j).whiskerLeft_comp_projFormulaHom_unit
    (instF := pullbackOplaxMonoidal j) N _ (homEquiv_symm_unitToPushforward j)

/-- **G0 (element form)**: `θ_j (s ⊗ j^♯ 1) = (j^*s) ⊗ 1` on global sections. -/
theorem projectionFormulaHom_whiskerLeft_unitToPushforward_apply (j : S ⟶ Y) (N : Y.Modules)
    (P : (N.val.obj (Opposite.op ⊤) : Type u)) :
    ((projectionFormulaHom j N (𝟙_ S.Modules)).val.app (Opposite.op ⊤)).hom
        (((N ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
          (((ρ_ N).inv.val.app (Opposite.op ⊤)).hom P)) =
      (show (((pushforward j).obj ((pullback j).obj N ⊗ 𝟙_ S.Modules)).val.obj (Opposite.op ⊤) : Type u) from
        ((ρ_ ((pullback j).obj N)).inv.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j P)) := by
  have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom (((ρ_ N).inv.val.app (Opposite.op ⊤)).hom P))
    (whiskerLeft_unitToPushforward_comp_projectionFormulaHom j N)
  refine h.trans ?_
  show ((pushforward j).map (ρ_ ((pullback j).obj N)).inv).val.app (Opposite.op ⊤)
      (((pullbackPushforwardAdjunction j).unit.app N).val.app (Opposite.op ⊤)
        (((ρ_ N).hom.val.app (Opposite.op ⊤)).hom (((ρ_ N).inv.val.app (Opposite.op ⊤)).hom P))) = _
  rw [app_top_inv_hom]
  rfl

/-- `𝟙^*s = (pullbackId X).inv s`: mate of `pullbackId` (Mathlib `conjugateEquiv_pullbackId_hom`). -/
theorem sectionPullbackAlong_id_eq_pullbackId_inv {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong (𝟙 X) s = (((pullbackId X).inv.app M).val.app (Opposite.op ⊤)).hom s := by
  have h := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  have h' := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom s) h
  have h'' : (((pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (𝟙 X) s) = s :=
    h'.symm
  calc sectionPullbackAlong (𝟙 X) s
      = (((pullbackId X).inv.app M).val.app (Opposite.op ⊤)).hom
          ((((pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (𝟙 X) s)) :=
        (app_top_hom_inv ((pullbackId X).app M) _).symm
    _ = _ := by rw [h'']

/-- Ring maps compose: `p^♯ ≫ p_*(j^♯) ≫ pushforwardComp = (j ≫ p)^♯`. -/
theorem unitToPushforward_comp_pushforward_map_comp_pushforwardComp {X : AlgebraicGeometry.Scheme.{u}}
    (j : S ⟶ Y) (p : Y ⟶ X) :
    SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
        (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (pushforwardComp j p).hom.app (𝟙_ S.Modules) =
      SheafOfModules.unitToPushforwardObjUnit (j ≫ p).toRingCatSheafHom := by
  ext U
  rfl

/-- Transport of the ring map along an equality of morphisms. -/
theorem unitToPushforward_comp_pushforwardCongr {f g : S ⟶ Y} (hg : f = g) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (pushforwardCongr hg).hom.app (𝟙_ S.Modules) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  subst hg
  have h1 : ∀ (Z : AlgebraicGeometry.Scheme.{u}) (V : Z.Opens) (e : V = V),
      Z.presheaf.map (CategoryTheory.eqToHom e).op = CategoryTheory.CategoryStruct.id _ := by
    intro Z V e; simp
  ext U
  exact congrArg (fun φ : Γ(S, f ⁻¹ᵁ U.unop) ⟶ Γ(S, f ⁻¹ᵁ U.unop) => φ.hom ((f.app U.unop).hom 1))
    (h1 S (f ⁻¹ᵁ U.unop) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- `pushforwardCongr rfl` is the identity on the structure sheaf (its components are
`presheaf.map (eqToHom rfl).op`). -/
theorem pushforwardCongr_rfl_hom_app_unit (f : S ⟶ Y) :
    (pushforwardCongr (rfl : f = f)).hom.app (𝟙_ S.Modules) = 𝟙 _ := by
  have h1 : ∀ (Z : AlgebraicGeometry.Scheme.{u}) (V : Z.Opens) (e : V = V),
      Z.presheaf.map (CategoryTheory.eqToHom e).op = CategoryTheory.CategoryStruct.id _ := by
    intro Z V e; simp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact congrArg (fun φ : S.presheaf.obj (Opposite.op (f ⁻¹ᵁ U.unop)) ⟶
    S.presheaf.obj (Opposite.op (f ⁻¹ᵁ U.unop)) => φ.hom a) (h1 S (f ⁻¹ᵁ U.unop) rfl)

/-- `𝟙^♯ ≫ pushforwardId = 𝟙`. -/
theorem unitToPushforward_id_comp_pushforwardId {X : AlgebraicGeometry.Scheme.{u}} :
    SheafOfModules.unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom ≫
        (pushforwardId X).hom.app (𝟙_ X.Modules) = 𝟙 _ := by
  ext U
  rfl

/-- `θ_p` is natural in the second variable (element form on global sections). -/
theorem projectionFormulaHom_whiskerLeft_pushforward_map_apply {X : AlgebraicGeometry.Scheme.{u}}
    (p : Y ⟶ X) (M : X.Modules) {N N' : Y.Modules} (h : N ⟶ N')
    (Q : ((M ⊗ (pushforward p).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    ((projectionFormulaHom p M N').val.app (Opposite.op ⊤)).hom
        (((M ◁ (pushforward p).map h).val.app (Opposite.op ⊤)).hom Q) =
      (((pushforward p).map ((pullback p).obj M ◁ h)).val.app (Opposite.op ⊤)).hom
        (((projectionFormulaHom p M N).val.app (Opposite.op ⊤)).hom Q) :=
  congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom Q)
    ((pullbackPushforwardAdjunction p).projFormulaHom_naturality_right (instF := pullbackOplaxMonoidal p) M h)

/-- The pseudofunctor identification `C : p_*j_*O_X ≅ O_X` for `j ≫ p = 𝟙 X`
(`pushforwardComp`, `pushforwardCongr`, `pushforwardId`). -/
def pushforwardCompCongrIdIso {X : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (p : Y ⟶ X) (hg : j ≫ p = 𝟙 X)
    (N : X.Modules) : (pushforward p).obj ((pushforward j).obj N) ≅ N :=
  (pushforwardComp j p).app N ≪≫ (pushforwardCongr hg).app N ≪≫ (pushforwardId X).app N

set_option backward.isDefEq.respectTransparency false in
/-- `C.inv = p^♯ ≫ p_*(j^♯)` for a section `j` of `p` (the ring map of `j ≫ p = 𝟙` is the identity). -/
theorem pushforwardCompCongrIdIso_inv_eq {X : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (p : Y ⟶ X)
    (hg : j ≫ p = 𝟙 X) :
    (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).inv =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
        (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) := by
  symm
  rw [← Iso.comp_hom_eq_id]
  show (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) ≫
    ((pushforwardComp j p).hom.app (𝟙_ X.Modules) ≫ (pushforwardCongr hg).hom.app (𝟙_ X.Modules) ≫
      (pushforwardId X).hom.app (𝟙_ X.Modules)) = 𝟙 _
  simp only [Category.assoc]
  rw [reassoc_of% (unitToPushforward_comp_pushforward_map_comp_pushforwardComp j p),
    reassoc_of% (unitToPushforward_comp_pushforwardCongr hg), unitToPushforward_id_comp_pushforwardId]

set_option backward.isDefEq.respectTransparency false in
/-- `Φ(j^*(p^*m)) = m` for `j ≫ p = 𝟙 X`, `Φ := pullbackComp ≫ pullbackCongr ≫ pullbackId`. -/
theorem pullbackCompCongrId_sectionPullbackAlong_sectionPullbackAlong {X : AlgebraicGeometry.Scheme.{u}}
    (j : X ⟶ Y) (p : Y ⟶ X) (hg : j ≫ p = 𝟙 X) (M : X.Modules) (m : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j p).hom.app M ≫ (pullbackCongr hg).hom.app M ≫
        (pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong j (sectionPullbackAlong p m)) = m := by
  rw [app_top_comp, app_top_comp]
  have h1 : (((pullbackComp j p).hom.app M).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong j (sectionPullbackAlong p m)) = sectionPullbackAlong (j ≫ p) m :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp j p m
  have h2 : (((pullbackCongr hg).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (j ≫ p) m) =
      sectionPullbackAlong (𝟙 X) m :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply hg m
  rw [h1, h2, sectionPullbackAlong_id_eq_pullbackId_inv]
  exact app_top_inv_hom ((pullbackId X).app M) m

set_option backward.isDefEq.respectTransparency false in
/-- **Main**: for a section `j` of `p` (`j ≫ p = 𝟙`) and `Q ∈ Γ(X, M ⊗ p_*O_Y)`,
`ρ((M ◁ (p_*(j^♯) ≫ C)) Q) = Φ(j^*(pushforwardSectionToPullback p M Q))`. See the module docstring. -/
theorem rightUnitor_whiskerLeft_eq_pullback_section_of_comp_eq_id {X : AlgebraicGeometry.Scheme.{u}}
    (j : X ⟶ Y) (p : Y ⟶ X) (hg : j ≫ p = 𝟙 X) (M : X.Modules)
    (Q : ((M ⊗ (pushforward p).obj (𝟙_ Y.Modules)).val.obj (Opposite.op ⊤) : Type u)) :
    ((ρ_ M).hom.val.app (Opposite.op ⊤)).hom
        (((M ◁ ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
            (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom)).val.app (Opposite.op ⊤)).hom Q) =
      (((pullbackComp j p).hom.app M ≫ (pullbackCongr hg).hom.app M ≫
          (pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong j (pushforwardSectionToPullback p M Q)) := by
  obtain ⟨m, hm⟩ : ∃ m : (M.val.obj (Opposite.op ⊤) : Type u), m = ((ρ_ M).hom.val.app (Opposite.op ⊤)).hom
      (((M ◁ ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom)).val.app (Opposite.op ⊤)).hom Q) := ⟨_, rfl⟩
  rw [← hm]
  -- (1) `(M ◁ p_*j^♯) Q = (M ◁ p_*j^♯) ((M ◁ p^♯) (m ⊗ 1))`
  have hb : (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) =
      ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom) ≫
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
        (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)) := by
    rw [← pushforwardCompCongrIdIso_inv_eq j p hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hd : ((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m =
      (((M ◁ ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
        (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom)).val.app (Opposite.op ⊤)).hom Q) := by
    rw [hm]
    exact app_top_hom_inv (ρ_ M) _
  have h1 : (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
        (Opposite.op ⊤)).hom Q) =
      (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
        (Opposite.op ⊤)).hom
        (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
          (((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m))) :=
    calc (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
          (Opposite.op ⊤)).hom Q)
        = (((M ◁ (((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
            (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom) ≫
            (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
              (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)))).val.app
            (Opposite.op ⊤)).hom Q) :=
          congrArg (fun φ => ((M ◁ φ).val.app (Opposite.op ⊤)).hom Q) hb
      _ = (((M ◁ (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
            (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom))).val.app
            (Opposite.op ⊤)).hom
            (((M ◁ ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
              (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom)).val.app (Opposite.op ⊤)).hom Q)) :=
          app_top_whiskerLeft_comp M _ _ Q
      _ = (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
            (Opposite.op ⊤)).hom
            (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
              (((M ◁ ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) ≫
                (pushforwardCompCongrIdIso j p hg (𝟙_ X.Modules)).hom)).val.app (Opposite.op ⊤)).hom Q))) :=
          app_top_whiskerLeft_comp M _ _ _
      _ = _ := by rw [← hd]
  -- (2) `P := pushforwardSectionToPullback p M Q = ρ(θ_p Q)`
  have hP : ((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (pushforwardSectionToPullback p M Q) =
      ((projectionFormulaHom p M (𝟙_ Y.Modules)).val.app (Opposite.op ⊤)).hom Q := by
    rw [pushforwardSectionToPullback_eq p M Q]
    exact app_top_hom_inv (ρ_ ((pullback p).obj M)) _
  -- (3) G0 for `j` applied to `P`, then naturality of `θ_p`, `h1`, naturality again, G0 for `p`, G0 for `j`
  have e1 := projectionFormulaHom_whiskerLeft_pushforward_map_apply p M
    (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) Q
  have e2 := projectionFormulaHom_whiskerLeft_pushforward_map_apply p M
    (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
    (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
      (((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m))
  have e3 := projectionFormulaHom_whiskerLeft_unitToPushforward_apply p M m
  have e4 := projectionFormulaHom_whiskerLeft_unitToPushforward_apply j ((pullback p).obj M)
    (pushforwardSectionToPullback p M Q)
  have e5 := projectionFormulaHom_whiskerLeft_unitToPushforward_apply j ((pullback p).obj M)
    (sectionPullbackAlong p m)
  have hΦ := pullbackCompCongrId_sectionPullbackAlong_sectionPullbackAlong j p hg M m
  -- assemble: `j^*P = ρ(θ_j((p^*M ◁ j^♯)(ρ⁻¹ P)))`, and `(p^*M ◁ j^♯)(ρ⁻¹ P) = (p^*M ◁ j^♯)(ρ⁻¹(p^*m))`
  have key : (((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
        (Opposite.op ⊤)).hom
        (((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (pushforwardSectionToPullback p M Q)) =
      (((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
        (Opposite.op ⊤)).hom
        (((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong p m)) := by
    rw [hP]
    have e1' : (((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
        (Opposite.op ⊤)).hom (((projectionFormulaHom p M (𝟙_ Y.Modules)).val.app (Opposite.op ⊤)).hom Q) =
        ((projectionFormulaHom p M ((pushforward j).obj (𝟙_ X.Modules))).val.app (Opposite.op ⊤)).hom
          (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
            (Opposite.op ⊤)).hom Q) := e1.symm
    have e2' : ((projectionFormulaHom p M ((pushforward j).obj (𝟙_ X.Modules))).val.app (Opposite.op ⊤)).hom
          (((M ◁ (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)).val.app
            (Opposite.op ⊤)).hom
            (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
              (((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m))) =
        (((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
          (Opposite.op ⊤)).hom
          (((projectionFormulaHom p M (𝟙_ Y.Modules)).val.app (Opposite.op ⊤)).hom
            (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
              (((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m))) := e2
    have e3' : ((projectionFormulaHom p M (𝟙_ Y.Modules)).val.app (Opposite.op ⊤)).hom
          (((M ◁ SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (Opposite.op ⊤)).hom
            (((ρ_ M).inv.val.app (Opposite.op ⊤)).hom m)) =
        ((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong p m) := e3
    rw [e1', h1, e2', e3']
  have e4' : sectionPullbackAlong j (pushforwardSectionToPullback p M Q) =
      ((ρ_ ((pullback j).obj ((pullback p).obj M))).hom.val.app (Opposite.op ⊤)).hom
        (((projectionFormulaHom j ((pullback p).obj M) (𝟙_ X.Modules)).val.app (Opposite.op ⊤)).hom
          ((((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
            (Opposite.op ⊤)).hom
            (((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (pushforwardSectionToPullback p M Q)))) := by
    have e4'' : ((projectionFormulaHom j ((pullback p).obj M) (𝟙_ X.Modules)).val.app (Opposite.op ⊤)).hom
          ((((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
            (Opposite.op ⊤)).hom
            (((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (pushforwardSectionToPullback p M Q))) =
        ((ρ_ ((pullback j).obj ((pullback p).obj M))).inv.val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j (pushforwardSectionToPullback p M Q)) := e4
    rw [e4'']
    exact (app_top_inv_hom (ρ_ ((pullback j).obj ((pullback p).obj M))) _).symm
  have e5' : ((projectionFormulaHom j ((pullback p).obj M) (𝟙_ X.Modules)).val.app (Opposite.op ⊤)).hom
        ((((pullback p).obj M ◁ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom).val.app
          (Opposite.op ⊤)).hom
          (((ρ_ ((pullback p).obj M)).inv.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong p m))) =
      ((ρ_ ((pullback j).obj ((pullback p).obj M))).inv.val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong j (sectionPullbackAlong p m)) := e5
  rw [e4', key, e5', app_top_inv_hom, hΦ]

end AlgebraicGeometry.Scheme.Modules

end
