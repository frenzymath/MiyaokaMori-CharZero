import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # The composition isomorphism of pullbacks is monoidal

For morphisms of schemes `f : X ⟶ Y`, `g : Y ⟶ Z`, Mathlib's natural isomorphism
`pullbackComp f g : g^* ⋙ f^* ≅ (f ≫ g)^*` is a monoidal natural isomorphism, i.e. it is compatible
with the (oplax) monoidal structure of the pullback functors:

* (U) unit: `pullbackComp.hom.app O_Z ≫ (pullbackUnitIso (f ≫ g)).hom =
  f^*((pullbackUnitIso g).hom) ≫ (pullbackUnitIso f).hom` (`pullbackComp_hom_app_pullbackUnitIso_hom`);
* (T) tensor: `pullbackComp.hom.app (M ⊗ N) ≫ δ_{f≫g} =
  f^*(δ_g) ≫ δ_f ≫ (pullbackComp.hom.app M ⊗ pullbackComp.hom.app N)`, where
  `δ_h := pullbackTensorObjHom h` (`pullbackComp_hom_app_pullbackTensorObjHom`);
* consequences: `ε_pullbackComp_inv` / `ε_pullbackComp_hom`, `μ_pullbackComp_inv` / `μ_pullbackComp_hom`
  (compatibility of `LaxMonoidal.ε`, `μ` with `pullbackComp`; `μ = δ⁻¹`, `ε = pullbackUnitIso⁻¹` by `rfl`).

Proof.
1. Transpose lemma `homEquiv_pullbackComp_hom_app_comp`: for `h : (f≫g)^*A ⟶ B`, the transpose of
   `pullbackComp.hom.app A ≫ h` under the composite adjunction `adj_g.comp adj_f` equals the
   transpose of `h` under `adj_{f≫g}` followed by `(pushforwardComp f g).inv.app B`. From Mathlib's
   `conjugateEquiv_pullbackComp_inv` (the conjugate of `pullbackComp.inv` is `pushforwardComp.hom`),
   `unit_conjugateEquiv`, and naturality of `pushforwardComp.inv`.
2. Transpose lemma `homEquiv_comp_pullback_map_comp`: under the composite adjunction the transpose of
   `f^*(a) ≫ b` is `adj_g`-transpose of `a` followed by `g_*(adj_f`-transpose of `b)`
   (`Adjunction.comp_homEquiv` and the two naturality lemmas of `homEquiv`).
3. (U): take composite-adjunction transposes (injective). The transpose of `pullbackUnitIso h` is
   Mathlib's `unitToPushforwardObjUnit h` (on sections the ring map `h^♯(U)`,
   `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`); `pushforwardComp.inv` is the
   identity on sections, so the identity reduces to `(f≫g)^♯(U) = f^♯(g⁻¹U) ∘ g^♯(U)`, which is `rfl`
   sectionwise.
4. (T): take composite-adjunction transposes and reduce with 1 and 2; then check on pairings of
   sections with `tensorObj_hom_ext`, using `homEquiv_pullbackTensorObjHom_tensorSections` for the
   values of `δ_h`, `tensorToSheafify_tensorSections`, `tensorHom_tensorSections`,
   `sheafification_homEquiv_symm_unit` (`sh⁻¹(P) ∘ η^{sh} = P`) and `unit_comp_app`
   (`η_{f≫g} = c ∘ η_f ∘ η_g` on sections, step 1 with `h = 𝟙`).
5. The `μ`, `ε` statements: write (U), (T) as equalities of isomorphisms (`Iso.ext`) and take
   inverses (`congrArg Iso.inv`); the `hom` versions follow by composing with `pullbackComp.hom`.

Reference: Stacks 01CD (compatibility of the canonical isomorphism with composition); cf. the
adjoint-transpose argument of Stacks 01AG.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem adjunction_comp_homEquiv_map_comp {C D E : Type*} [Category C] [Category D]
    [Category E] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {A : C} {A' : D} {B : E}
    (a : L₁.obj A ⟶ A') (b : L₂.obj A' ⟶ B) :
    (adj₁.comp adj₂).homEquiv A B (L₂.map a ≫ b) =
      adj₁.homEquiv A A' a ≫ R₁.map (adj₂.homEquiv A' B b) := by
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem homEquiv_pullbackComp_hom_app_comp {A : Z.Modules} {B : X.Modules}
    (h : (pullback (f ≫ g)).obj A ⟶ B) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv A B
        ((pullbackComp f g).hom.app A ≫ h) =
      (pullbackPushforwardAdjunction (f ≫ g)).homEquiv A B h ≫ (pushforwardComp f g).inv.app B := by
  have hu := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv A
  rw [conjugateEquiv_pullbackComp_inv] at hu
  have hn := (pushforwardComp f g).inv.naturality ((pullbackComp f g).hom.app A ≫ h)
  have hu' : ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).unit.app A =
      (pullbackPushforwardAdjunction (f ≫ g)).unit.app A ≫
        (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app A) ≫
          (pushforwardComp f g).inv.app _ := by
    rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hu', Category.assoc, Category.assoc,
    ← hn, ← Category.assoc ((pushforward (f ≫ g)).map _), ← Functor.map_comp,
    Iso.inv_hom_id_app_assoc, Category.assoc]

theorem homEquiv_comp_pullback_map_comp {A : Z.Modules} {A' : Y.Modules} {B : X.Modules}
    (a : (pullback g).obj A ⟶ A') (b : (pullback f).obj A' ⟶ B) :
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).homEquiv A B
        ((pullback f).map a ≫ b) =
      (pullbackPushforwardAdjunction g).homEquiv A A' a ≫
        (pushforward g).map ((pullbackPushforwardAdjunction f).homEquiv A' B b) := by
  exact adjunction_comp_homEquiv_map_comp _ _ a b

theorem pullbackComp_hom_app_pullbackUnitIso_hom :
    (pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso (f ≫ g)).hom =
      (pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom := by
  refine (((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)).homEquiv _ _).injective ?_
  refine (homEquiv_pullbackComp_hom_app_comp f g _).trans ?_
  refine Eq.trans ?_ (homEquiv_comp_pullback_map_comp f g _ _).symm
  have e : ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := fun f =>
    haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
      (pullbackPushforwardAdjunction f).isRightAdjoint
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      f.toRingCatSheafHom
  rw [e, e, e]
  ext U x
  rfl

/-- The inverse transpose of the sheafification adjunction on the image of the sheafification unit:
`sh⁻¹(P)(η^{sh} y) = P y`. -/
private theorem sheafification_homEquiv_symm_unit {X : AlgebraicGeometry.Scheme.{u}}
    {Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj} {A : X.Modules}
    (P : Q ⟶ (SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
    (U : X.Opensᵒᵖ) (y : Q.obj U) :
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv Q A).symm P).val.app U
        (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q).app U y) =
      P.app U y := by
  have h := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (f := ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv Q A).symm P)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun k => k.app U y) h).symm

/-- On sections, `η_{f≫g} = c ∘ η_f ∘ η_g` (step 1 with `h = 𝟙`). -/
private theorem unit_comp_app (M : Z.Modules) (U : Z.Opensᵒᵖ) (m : M.val.obj U) :
    ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app U m =
      ((pullbackComp f g).hom.app M).val.app (Opposite.op ((f ≫ g) ⁻¹ᵁ U.unop))
        (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).val.app
          (Opposite.op (g ⁻¹ᵁ U.unop))
          (((pullbackPushforwardAdjunction g).unit.app M).val.app U m)) := by
  have h := homEquiv_pullbackComp_hom_app_comp f g (A := M) (𝟙 _)
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.comp_id]
    at h
  exact (congrArg (fun k => k.val.app U m) h).symm

/-- (T): compatibility of the comparison morphisms `δ_h = pullbackTensorObjHom h` with composition
(see step 4 of the module docstring). -/
theorem pullbackComp_hom_app_pullbackTensorObjHom (M N : Z.Modules) :
    (pullbackComp f g).hom.app (MonoidalCategoryStruct.tensorObj M N) ≫
        pullbackTensorObjHom (f ≫ g) M N =
      (pullback f).map (pullbackTensorObjHom g M N) ≫
        pullbackTensorObjHom f ((pullback g).obj M) ((pullback g).obj N) ≫
        MonoidalCategoryStruct.tensorHom ((pullbackComp f g).hom.app M)
          ((pullbackComp f g).hom.app N) := by
  refine (((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)).homEquiv _ _).injective ?_
  refine (homEquiv_pullbackComp_hom_app_comp f g _).trans ?_
  refine Eq.trans ?_ (homEquiv_comp_pullback_map_comp f g _ _).symm
  rw [Adjunction.homEquiv_naturality_right]
  -- both sides are morphisms out of `M ⊗ N`; check them on pairings of sections `m ⊗ n` with
  -- `tensorObj_hom_ext`, using `homEquiv_pullbackTensorObjHom_tensorSections` for the values of `δ`.
  apply tensorObj_hom_ext
  intro U m n
  have d1 := homEquiv_pullbackTensorObjHom_tensorSections (f ≫ g) M N U m n
  have d2 := homEquiv_pullbackTensorObjHom_tensorSections g M N U m n
  have d3 := homEquiv_pullbackTensorObjHom_tensorSections f ((pullback g).obj M)
    ((pullback g).obj N) (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app M).val.app (Opposite.op U) m)
    (((pullbackPushforwardAdjunction g).unit.app N).val.app (Opposite.op U) n)
  have r3 := tensorHom_tensorSections ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N)
    (f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).val.app
      (Opposite.op (g ⁻¹ᵁ U)) (((pullbackPushforwardAdjunction g).unit.app M).val.app (Opposite.op U) m))
    (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj N)).val.app
      (Opposite.op (g ⁻¹ᵁ U)) (((pullbackPushforwardAdjunction g).unit.app N).val.app (Opposite.op U) n))
  have e1 := unit_comp_app f g M (Opposite.op U) m
  have e2 := unit_comp_app f g N (Opposite.op U) n
  refine (congrArg (fun z => ((pushforwardComp f g).inv.app _).val.app (Opposite.op U) z) d1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((pushforward g).map
    ((pullbackPushforwardAdjunction f).homEquiv _ _
        (pullbackTensorObjHom f ((pullback g).obj M) ((pullback g).obj N)) ≫
      (pushforward f).map (MonoidalCategoryStruct.tensorHom ((pullbackComp f g).hom.app M)
        ((pullbackComp f g).hom.app N)))).val.app (Opposite.op U) z) d2.symm)
  refine Eq.trans ?_ (congrArg (fun z => ((pushforward f).map
    (MonoidalCategoryStruct.tensorHom ((pullbackComp f g).hom.app M)
      ((pullbackComp f g).hom.app N))).val.app (Opposite.op (g ⁻¹ᵁ U)) z) d3.symm)
  refine Eq.trans ?_ r3.symm
  refine Eq.trans ?_ (congrArg₂ (tensorSections ((pullback (f ≫ g)).obj M)
    ((pullback (f ≫ g)).obj N) ((f ≫ g) ⁻¹ᵁ U)) e1 e2)
  rfl

theorem μ_pullback_eq {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) M N = (pullbackTensorObjIso f M N).inv := rfl

theorem ε_pullback_eq {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    Functor.LaxMonoidal.ε (pullback f) = (pullbackUnitIso f).inv := pullback_ε_eq f

theorem μ_pullbackComp_inv (M N : Z.Modules) :
    Functor.LaxMonoidal.μ (pullback (f ≫ g)) M N ≫
        (pullbackComp f g).inv.app (MonoidalCategoryStruct.tensorObj M N) =
      MonoidalCategoryStruct.tensorHom ((pullbackComp f g).inv.app M)
          ((pullbackComp f g).inv.app N) ≫
        Functor.LaxMonoidal.μ (pullback f) ((pullback g).obj M) ((pullback g).obj N) ≫
        (pullback f).map (Functor.LaxMonoidal.μ (pullback g) M N) := by
  have h : (pullbackComp f g).app (MonoidalCategoryStruct.tensorObj M N) ≪≫
        pullbackTensorObjIso (f ≫ g) M N =
      (pullback f).mapIso (pullbackTensorObjIso g M N) ≪≫
        pullbackTensorObjIso f ((pullback g).obj M) ((pullback g).obj N) ≪≫
        MonoidalCategory.tensorIso ((pullbackComp f g).app M) ((pullbackComp f g).app N) :=
    Iso.ext (pullbackComp_hom_app_pullbackTensorObjHom f g M N)
  have h' := congrArg Iso.inv h
  simpa [μ_pullback_eq] using h'

theorem μ_pullbackComp_hom (M N : Z.Modules) :
    Functor.LaxMonoidal.μ (pullback f) ((pullback g).obj M) ((pullback g).obj N) ≫
        (pullback f).map (Functor.LaxMonoidal.μ (pullback g) M N) ≫
        (pullbackComp f g).hom.app (MonoidalCategoryStruct.tensorObj M N) =
      MonoidalCategoryStruct.tensorHom ((pullbackComp f g).hom.app M)
          ((pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (pullback (f ≫ g)) M N := by
  have h := μ_pullbackComp_inv f g M N
  rw [← cancel_epi (MonoidalCategory.tensorIso ((pullbackComp f g).app M)
      ((pullbackComp f g).app N)).inv,
    ← cancel_mono ((pullbackComp f g).app (MonoidalCategoryStruct.tensorObj M N)).inv]
  simp only [MonoidalCategory.tensorIso_inv, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app]
  have k : MonoidalCategoryStruct.tensorHom ((pullbackComp f g).hom.app M)
        ((pullbackComp f g).hom.app N) ≫
      MonoidalCategoryStruct.tensorHom ((pullbackComp f g).inv.app M)
        ((pullbackComp f g).inv.app N) = 𝟙 _ := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id]
  rw [h, reassoc_of% k]
  congr 2

theorem ε_pullbackComp_inv :
    Functor.LaxMonoidal.ε (pullback (f ≫ g)) ≫
        (pullbackComp f g).inv.app (MonoidalCategoryStruct.tensorUnit Z.Modules) =
      Functor.LaxMonoidal.ε (pullback f) ≫ (pullback f).map (Functor.LaxMonoidal.ε (pullback g)) := by
  have h : (pullbackComp f g).app (SheafOfModules.unit Z.ringCatSheaf) ≪≫ pullbackUnitIso (f ≫ g) =
      (pullback f).mapIso (pullbackUnitIso g) ≪≫ pullbackUnitIso f :=
    Iso.ext (pullbackComp_hom_app_pullbackUnitIso_hom f g)
  rw [ε_pullback_eq, ε_pullback_eq, ε_pullback_eq]
  exact congrArg Iso.inv h

theorem ε_pullbackComp_hom :
    Functor.LaxMonoidal.ε (pullback f) ≫ (pullback f).map (Functor.LaxMonoidal.ε (pullback g)) ≫
        (pullbackComp f g).hom.app (MonoidalCategoryStruct.tensorUnit Z.Modules) =
      Functor.LaxMonoidal.ε (pullback (f ≫ g)) := by
  rw [← Category.assoc, ← ε_pullbackComp_inv, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules
