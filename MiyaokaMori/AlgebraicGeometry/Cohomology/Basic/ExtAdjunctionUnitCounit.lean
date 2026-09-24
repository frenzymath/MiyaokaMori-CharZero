import MiyaokaMori.Prelude

/-! # Naturality of the unit and counit of an adjunction on `Ext`

Let `F ⊣ G` be an adjunction between abelian categories with `F` and `G` exact (additive,
preserving finite limits and finite colimits). Viewing the unit `η : 𝟭 ⟹ F ⋙ G` and the counit
`ε : G ⋙ F ⟹ 𝟭` as degree-`0` classes `Ext.mk₀`, they are natural with respect to elements of
`Ext`:

* (counit) for `e : Ext (F X) Y n`,
  `((e mapped by G, then by F)).comp (mk₀ ε_Y) = (mk₀ ε_{F X}).comp e`;
* (unit) for `e : Ext X (G Y) n`,
  `(mk₀ η_X).comp ((e mapped by F, then by G)) = e.comp (mk₀ η_{G Y})`.

These are the statement "a natural transformation between exact functors stays natural on `Ext`"
in the cases `τ = ε` (`H = G ⋙ F`, `K = 𝟭`) and `τ = η` (`H = 𝟭`, `K = F ⋙ G`), with the
compatibility of `Ext.mapExactFunctor` with composition of functors and with the identity functor
absorbed into the statements.

The three general facts about `Ext.mapExactFunctor` (`Ext.mapExactFunctor_id`,
`Ext.mapExactFunctor_comp_functor`, `Ext.mapExactFunctor_natTrans`), not available in Mathlib, are
proved as follows:

1. `Ext.mapExactFunctor` is defined via `LocalizerMorphism.smallShiftedHomMap`, and Mathlib's
   `LocalizerMorphism.equiv_smallShiftedHomMap` allows *any* choice of a lift `G' : D(C) ⥤ D(D)`
   together with a shift-compatible isomorphism `e : Φ.functor ⋙ Q ≅ Q ⋙ G'`, writing
   `(f.mapExactFunctor F).hom` as
   `mk₀(Q eX.inv ≫ e.hom.app _) ∘ (f.hom.map G') ∘ mk₀(e.inv.app _ ≫ Q eY.hom)`.
   * identity functor: take `G' = 𝟭`, with `e` given by `Functor.mapHomologicalComplexIdIso`;
   * composition: take `G' = F.mapDerivedCategory ⋙ G.mapDerivedCategory`, with `e` assembled
     from `Functor.mapHomologicalComplexCompIso` and two `mapDerivedCategoryFactors`.
   In both cases `NatTrans.CommShift` for `e.hom` is checked componentwise on cochain complexes
   (all components are identities).
2. Natural transformations: `τ : H ⟶ K` lifts via `Localization.liftNatTrans` to
   `ν : H.mapDerivedCategory ⟶ K.mapDerivedCategory`; shift compatibility of `ν` is the general
   lemma `Localization.liftNatTrans_commShift` (`whiskerLeft Q ν` is a composite of three
   shift-compatible natural transformations; descend along the localization functor with
   `NatTrans.CommShift.of_whiskerLeft_localization`). Then `ShiftedHom.map_naturality f.hom ν`
   together with the compatibility square of `ν` with `mapDerivedCategorySingleFunctor` (reduced to
   the naturality of `singleMapHomologicalComplex` on cochain complexes) gives the claim.
3. The three compatibilities on cochain complexes (identity / composition / natural transformation)
   are reduced to the degree-`0` component by `HomologicalComplex.from_single_hom_ext` /
   `to_single_hom_ext` and closed by `simp`.

Source: standard homological algebra (the adjunction comparison of Weibel 2.3.10 / Stacks 015F,
carried out in the derived category).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- Same setting as Mathlib's `Algebra/Homology/DerivedCategory/{ExactFunctor,Ext/Map}.lean`:
-- objects such as `(singleFunctor C 0).obj X` / `Q.obj ((CochainComplex.singleFunctor C 0).obj X)`
-- or `((F.mapHomologicalComplex _).obj K).X i` / `F.obj (K.X i)` are definitionally but not
-- syntactically equal, and `rw`/`simp` need this option to unify them.
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Category

noncomputable section

namespace CategoryTheory

/-! ## Shift compatibility of the basic natural transformations on cochain complexes

These are stated as lemmas (not instances): they are used through `have` in the proofs below. -/

section CochainComplexCommShift

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- The identification `(𝟭 C).mapHomologicalComplex ≅ 𝟭` commutes with the shift. -/
lemma NatTrans.commShift_mapHomologicalComplexIdIso_hom :
    NatTrans.CommShift (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplexIdIso_hom_app_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Functor.commShiftIso_id_hom_app,
    Functor.comp_obj, Functor.id_obj]
  erw [id_comp]

/-- `NatTrans.mapHomologicalComplex τ` commutes with the shift. -/
lemma NatTrans.commShift_mapHomologicalComplex {H K : C ⥤ D} (τ : H ⟶ K)
    [H.Additive] [K.Additive] :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro a
  ext X i
  simp [CochainComplex.shiftFunctor_map_f']

/-- The identification `F.mapHomologicalComplex ⋙ G.mapHomologicalComplex ≅ (F ⋙ G).mapHomologicalComplex`
commutes with the shift. -/
lemma NatTrans.commShift_mapHomologicalComplexCompIso_hom (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] :
    NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom ℤ := by
  constructor
  intro a
  ext X i
  simp [CochainComplex.shiftFunctor_map_f', Functor.commShiftIso_comp_hom_app]
  erw [id_comp]

end CochainComplexCommShift

/-! ## Lifting natural transformations along a localization preserves shift compatibility -/

namespace NatTrans.CommShift

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  {F₁' F₂' : D ⥤ E} [F₁'.CommShift A] [F₂'.CommShift A]

/-- If `L` is a localization functor commuting with the shift, a natural transformation `ν`
between functors out of the localized category commutes with the shift as soon as
`whiskerLeft L ν` does. -/
lemma of_whiskerLeft_localization (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [L.CommShift A] (ν : F₁' ⟶ F₂')
    [NatTrans.CommShift (Functor.whiskerLeft L ν) A] : NatTrans.CommShift ν A := by
  constructor
  intro a
  apply Localization.natTrans_ext L W
  intro X
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L ν) a X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app, Functor.comp_obj,
    assoc] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_epi (F₁'.map ((L.commShiftIso a).hom.app X)), h,
    ← NatTrans.naturality_assoc]

end NatTrans.CommShift

namespace Localization

variable {C D E : Type*} [Category C] [Category D] [Category E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [L.CommShift A]
  (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
  [F₁.CommShift A] [F₂.CommShift A] [F₁'.CommShift A] [F₂'.CommShift A]
  [NatTrans.CommShift (Lifting.iso L W F₁ F₁').hom A]
  [NatTrans.CommShift (Lifting.iso L W F₂ F₂').hom A]
  (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ A]

lemma whiskerLeft_liftNatTrans :
    Functor.whiskerLeft L (liftNatTrans L W F₁ F₂ F₁' F₂' τ) =
      (Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv := by
  ext X
  simp

/-- A lifted natural transformation commutes with the shift when the lifting isomorphisms
and the original natural transformation do. -/
lemma liftNatTrans_commShift : NatTrans.CommShift (liftNatTrans L W F₁ F₂ F₁' F₂' τ) A := by
  have : NatTrans.CommShift (Functor.whiskerLeft L (liftNatTrans L W F₁ F₂ F₁' F₂' τ)) A := by
    rw [whiskerLeft_liftNatTrans]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft_localization L W _

end Localization

/-! ## `mapDerivedCategorySingleFunctor` through `mapDerivedCategoryFactors` -/

section MapDerivedCategorySingleFunctor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma Functor.mapDerivedCategorySingleFunctor_inv_app_eq (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) ≫
        F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X) := by
  rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X)),
    assoc, Iso.inv_hom_id_app]
  erw [comp_id]
  exact F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X

lemma Functor.mapDerivedCategorySingleFunctor_hom_app_eq (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  rw [← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app X), Iso.inv_hom_id_app,
    Functor.mapDerivedCategorySingleFunctor_inv_app_eq, assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rfl

end MapDerivedCategorySingleFunctor

/-! ## Compatibilities of `mapCochainComplexSingleFunctor` (identity / composition / naturality) -/

section MapCochainComplexSingleFunctor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]

lemma Functor.mapCochainComplexSingleFunctor_id_inv_app_comp (X : C) :
    ((𝟭 C).mapCochainComplexSingleFunctor 0).inv.app X ≫
      (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj X) = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors]

lemma Functor.mapCochainComplexSingleFunctor_id_comp_hom_app (X : C) :
    (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).inv.app
        ((CochainComplex.singleFunctor C 0).obj X) ≫
      ((𝟭 C).mapCochainComplexSingleFunctor 0).hom.app X = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors]

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

lemma Functor.mapCochainComplexSingleFunctor_comp_inv_app (X : C) :
    ((F ⋙ G).mapCochainComplexSingleFunctor 0).inv.app X ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app
        ((CochainComplex.singleFunctor C 0).obj X) =
    (G.mapCochainComplexSingleFunctor 0).inv.app (F.obj X) ≫
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapCochainComplexSingleFunctor 0).inv.app X) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors]
  erw [comp_id]

lemma Functor.mapCochainComplexSingleFunctor_comp_hom_app (X : C) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj X) ≫
      ((F ⋙ G).mapCochainComplexSingleFunctor 0).hom.app X =
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapCochainComplexSingleFunctor 0).hom.app X) ≫
      (G.mapCochainComplexSingleFunctor 0).hom.app (F.obj X) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors]
  erw [id_comp]

lemma Functor.mapCochainComplexSingleFunctor_natTrans_hom_app {H K : C ⥤ D} (τ : H ⟶ K)
    [H.Additive] [K.Additive] (Y : C) :
    (H.mapCochainComplexSingleFunctor 0).hom.app Y ≫
      (CochainComplex.singleFunctor D 0).map (τ.app Y) =
    (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj Y) ≫
      (K.mapCochainComplexSingleFunctor 0).hom.app Y := by
  apply HomologicalComplex.to_single_hom_ext
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]

end MapCochainComplexSingleFunctor

end CategoryTheory

/-! ## Three general compatibilities of `Ext.mapExactFunctor`

The two main statements below follow from three **general** compatibilities of
`Ext.mapExactFunctor`, independent of adjunctions:

* `Abelian.Ext.mapExactFunctor_id`: the identity functor;
* `Abelian.Ext.mapExactFunctor_comp_functor`: composition of functors;
* `Abelian.Ext.mapExactFunctor_natTrans`: a natural transformation between exact functors stays
  natural on `Ext`.

The first two are the object part of "`E ↦ E.mapExactFunctor` is a pseudofunctor from exact
functors to actions on `Ext`", the third its morphism part. See the module docstring for the proofs.
-/

attribute [local instance] HasDerivedCategory.standard in
/-- `Ext.mapExactFunctor` is trivial for the identity functor. -/
theorem CategoryTheory.Abelian.Ext.mapExactFunctor_id {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] {X Y : C} {n : ℕ}
    (e : CategoryTheory.Abelian.Ext X Y n) :
    e.mapExactFunctor (CategoryTheory.Functor.id C) = e := by
  let e' : (𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ 𝟭 _ :=
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  have hcs : NatTrans.CommShift e'.hom ℤ := by
    have := NatTrans.commShift_mapHomologicalComplexIdIso_hom (C := C)
    simp only [e', Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  have hcs' : NatTrans.CommShift
      (F₁ := ((𝟭 C).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
        (ComplexShape.up ℤ)).functor ⋙ DerivedCategory.Q) e'.hom ℤ := hcs
  ext
  have : (e.mapExactFunctor (𝟭 C)).hom = _ :=
    ((𝟭 C).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
      (((𝟭 C).mapCochainComplexSingleFunctor 0).app X)
      (((𝟭 C).mapCochainComplexSingleFunctor 0).app Y) (𝟭 _) e' e
  rw [this, ShiftedHom.id_map]
  have h₁ : DerivedCategory.Q.map (((𝟭 C).mapCochainComplexSingleFunctor 0).app X).inv ≫
      e'.hom.app ((CochainComplex.singleFunctor C 0).obj X) = 𝟙 _ := by
    simp only [e', Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Iso.app_inv]
    erw [comp_id]
    rw [← Functor.map_comp, Functor.mapCochainComplexSingleFunctor_id_inv_app_comp,
      Functor.map_id]
  have h₂ : e'.inv.app ((CochainComplex.singleFunctor C 0).obj Y) ≫
      DerivedCategory.Q.map (((𝟭 C).mapCochainComplexSingleFunctor 0).app Y).hom = 𝟙 _ := by
    simp only [e', Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Iso.app_hom]
    erw [id_comp]
    erw [← Functor.map_comp, Functor.mapCochainComplexSingleFunctor_id_comp_hom_app,
      Functor.map_id]
    rfl
  erw [h₁, h₂]
  simp
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- `Ext.mapExactFunctor` is compatible with composition of functors. -/
theorem CategoryTheory.Abelian.Ext.mapExactFunctor_comp_functor {C D E : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D] [CategoryTheory.Category E]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [CategoryTheory.Abelian E]
    [CategoryTheory.HasExt C] [CategoryTheory.HasExt D] [CategoryTheory.HasExt E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    {X Y : C} {n : ℕ} (e : CategoryTheory.Abelian.Ext X Y n) :
    e.mapExactFunctor (F ⋙ G) = (e.mapExactFunctor F).mapExactFunctor G := by
  let e' : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex _) G.mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm G.mapDerivedCategory ≪≫
    Functor.associator _ _ _
  have hcs : NatTrans.CommShift e'.hom ℤ := by
    have := NatTrans.commShift_mapHomologicalComplexCompIso_hom F G
    simp only [e', Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom]
    infer_instance
  have hcs' : NatTrans.CommShift
      (F₁ := ((F ⋙ G).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
        (ComplexShape.up ℤ)).functor ⋙ DerivedCategory.Q) e'.hom ℤ := hcs
  have nat : ∀ {A B : CochainComplex D ℤ} (f : A ⟶ B),
      G.mapDerivedCategoryFactors.inv.app A ≫ G.mapDerivedCategory.map (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
        G.mapDerivedCategoryFactors.inv.app B :=
    fun f => (G.mapDerivedCategoryFactors.inv.naturality f).symm
  have nat' : ∀ {A B : CochainComplex D ℤ} (f : A ⟶ B),
      G.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ G.mapDerivedCategoryFactors.hom.app B =
      G.mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    fun f => G.mapDerivedCategoryFactors.hom.naturality f
  ext
  have : (e.mapExactFunctor (F ⋙ G)).hom = _ :=
    ((F ⋙ G).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
      (((F ⋙ G).mapCochainComplexSingleFunctor 0).app X)
      (((F ⋙ G).mapCochainComplexSingleFunctor 0).app Y)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) e' e
  rw [this, Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.comp_map]
  have h₁ : DerivedCategory.Q.map (((F ⋙ G).mapCochainComplexSingleFunctor 0).app X).inv ≫
      e'.hom.app ((CochainComplex.singleFunctor C 0).obj X) =
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) := by
    simp only [e', Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.app_inv, comp_id, id_comp,
      Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor_inv_app_eq, Functor.map_comp,
      assoc]
    rw [← Functor.map_comp_assoc, Functor.mapCochainComplexSingleFunctor_comp_inv_app,
      Functor.map_comp_assoc, reassoc_of% (nat _)]
  have h₂ : e'.inv.app ((CochainComplex.singleFunctor C 0).obj Y) ≫
      DerivedCategory.Q.map (((F ⋙ G).mapCochainComplexSingleFunctor 0).app Y).hom =
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj Y) := by
    simp only [e', Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.app_hom, id_comp,
      Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor_hom_app_eq, Functor.map_comp,
      assoc]
    rw [reassoc_of% (nat' _), ← Functor.map_comp, ← Functor.map_comp,
      Functor.mapCochainComplexSingleFunctor_comp_hom_app]
  rw [h₁, h₂]
  simp only [ShiftedHom.map, Functor.map_comp, assoc]
  first
    | rw [Functor.commShiftIso_hom_naturality_assoc]
    | erw [Functor.commShiftIso_hom_naturality_assoc]
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- A natural transformation `τ : H ⟹ K` between exact functors stays natural on `Ext`.
For `n = 0` this is the naturality of `τ` (`Ext.mapExactFunctor_mk₀` + `Ext.mk₀_comp_mk₀`);
general `n` is handled in the derived category (step 2 of the module docstring). -/
theorem CategoryTheory.Abelian.Ext.mapExactFunctor_natTrans {C D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    [CategoryTheory.HasExt C] [CategoryTheory.HasExt D]
    {H K : C ⥤ D} (τ : H ⟶ K) [H.Additive] [K.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    [CategoryTheory.Limits.PreservesFiniteLimits K]
    [CategoryTheory.Limits.PreservesFiniteColimits K]
    {X Y : C} {n : ℕ} (e : CategoryTheory.Abelian.Ext X Y n) :
    (e.mapExactFunctor H).comp (CategoryTheory.Abelian.Ext.mk₀ (τ.app Y)) (add_zero n)
      = (CategoryTheory.Abelian.Ext.mk₀ (τ.app X)).comp (e.mapExactFunctor K) (zero_add n) := by
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let ν : H.mapDerivedCategory ⟶ K.mapDerivedCategory :=
    Localization.liftNatTrans DerivedCategory.Q W
      (H.mapHomologicalComplex _ ⋙ DerivedCategory.Q) (K.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      H.mapDerivedCategory K.mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) DerivedCategory.Q)
  have hν : NatTrans.CommShift ν ℤ := by
    have := NatTrans.commShift_mapHomologicalComplex τ
    have h₁ : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q W
        (H.mapHomologicalComplex _ ⋙ DerivedCategory.Q) H.mapDerivedCategory).hom ℤ :=
      inferInstanceAs (NatTrans.CommShift H.mapDerivedCategoryFactors.hom ℤ)
    have h₂ : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q W
        (K.mapHomologicalComplex _ ⋙ DerivedCategory.Q) K.mapDerivedCategory).hom ℤ :=
      inferInstanceAs (NatTrans.CommShift K.mapDerivedCategoryFactors.hom ℤ)
    exact Localization.liftNatTrans_commShift _ _ _ _ _ _ _
  have hν_app : ∀ (A : CochainComplex C ℤ), ν.app (DerivedCategory.Q.obj A) =
      H.mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app A) ≫
        K.mapDerivedCategoryFactors.inv.app A := fun A => by
    simp only [ν, Localization.liftNatTrans_app, Functor.whiskerRight_app]
    rfl
  have hν_single : ∀ (A : C), ν.app ((DerivedCategory.singleFunctor C 0).obj A) =
      H.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj A) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj A)) ≫
        K.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj A) :=
    fun A => hν_app _
  -- compatibility of `ν` with the single functors
  have hsingle : ∀ (A : C), (H.mapDerivedCategorySingleFunctor 0).hom.app A ≫
      (DerivedCategory.singleFunctor D 0).map (τ.app A) =
      ν.app ((DerivedCategory.singleFunctor C 0).obj A) ≫
        (K.mapDerivedCategorySingleFunctor 0).hom.app A := by
    intro A
    rw [hν_single, Functor.mapDerivedCategorySingleFunctor_hom_app_eq,
      Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
    simp only [assoc, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp]
    change _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = _
    rw [← Functor.map_comp, Functor.mapCochainComplexSingleFunctor_natTrans_hom_app]
  have hX : (H.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ν.app ((DerivedCategory.singleFunctor C 0).obj X) =
      (DerivedCategory.singleFunctor D 0).map (τ.app X) ≫
        (K.mapDerivedCategorySingleFunctor 0).inv.app X := by
    rw [← cancel_mono ((K.mapDerivedCategorySingleFunctor 0).hom.app X)]
    simp only [assoc, Iso.inv_hom_id_app]
    erw [comp_id]
    rw [← hsingle, Iso.inv_hom_id_app_assoc]
  ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom,
    Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.mapExactFunctor_hom,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  have key := ShiftedHom.map_naturality e.hom ν (a := (n : ℤ))
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at key
  rw [assoc, assoc, ← Functor.map_comp, hsingle, Functor.map_comp, ← assoc (e.hom.map _), key,
    assoc, reassoc_of% hX]

/-- Naturality of the counit `ε : G ⋙ F ⟹ 𝟭` on `Ext` (see the module docstring). -/
theorem CategoryTheory.Adjunction.ext_comp_mk₀_counit {C D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    [CategoryTheory.HasExt C] [CategoryTheory.HasExt D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (X : C) (Y : D) (n : ℕ) (e : CategoryTheory.Abelian.Ext (F.obj X) Y n) :
    ((e.mapExactFunctor G).mapExactFunctor F).comp
        (CategoryTheory.Abelian.Ext.mk₀ (adj.counit.app Y)) (add_zero n)
      = (CategoryTheory.Abelian.Ext.mk₀ (adj.counit.app (F.obj X))).comp e (zero_add n) := by
  rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_comp_functor G F e]
  have h := CategoryTheory.Abelian.Ext.mapExactFunctor_natTrans
    (H := G ⋙ F) (K := CategoryTheory.Functor.id D) adj.counit e
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_id] at h
  exact h

/-- Naturality of the unit `η : 𝟭 ⟹ F ⋙ G` on `Ext` (see the module docstring). -/
theorem CategoryTheory.Adjunction.ext_mk₀_unit_comp {C D : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    [CategoryTheory.HasExt C] [CategoryTheory.HasExt D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (X : C) (Y : D) (n : ℕ) (e : CategoryTheory.Abelian.Ext X (G.obj Y) n) :
    (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app X)).comp
        ((e.mapExactFunctor F).mapExactFunctor G) (zero_add n)
      = e.comp (CategoryTheory.Abelian.Ext.mk₀ (adj.unit.app (G.obj Y))) (add_zero n) := by
  rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_comp_functor F G e]
  have h := CategoryTheory.Abelian.Ext.mapExactFunctor_natTrans
    (H := CategoryTheory.Functor.id C) (K := F ⋙ G) adj.unit e
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_id] at h
  exact h.symm

end
