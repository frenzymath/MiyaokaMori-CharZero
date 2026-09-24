import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.RestrictScalarsIsoMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidalReduction
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.CategoryTheory.LocalizedBraidedOfComp

/-! # Sheafification commutes with restriction along an open immersion; restriction is monoidal

**Sheafification commutes with restriction along an open immersion**, and consequently
restriction along an open immersion is a strong monoidal (indeed braided) functor.

Let `f : X ⟶ Y` be an open immersion of schemes.

1. `restrictPre f`: restriction at the level of presheaves of modules (pushforward along
   `f.opensFunctor`, with scalar map the isomorphism `f.appIso⁻¹`). It is
   `pushforward₀OfCommRingCat` (strong monoidal in Mathlib) composed with `restrictScalarsC` along
   an isomorphism (strong monoidal), hence **strong monoidal**.
2. `sheafifyRestrictIso`: the natural isomorphism `L_X (P|_X) ≅ (L_Y P)|_X` (sheafification
   commutes with restriction). The comparison morphism is the transpose under the sheafification
   adjunction of `(restrictPre f).map η_P`, i.e. `L_X((restrictPre f).map η_P) ≫ ε`. The counit `ε`
   is an isomorphism (Mathlib); the first factor is an isomorphism because `η_P` is `toSheafify` at
   the level of abelian groups, hence locally bijective (Mathlib instance), and **precomposition
   with a cocontinuous functor preserves local injectivity/surjectivity** (Mathlib
   `Presheaf.isLocallyInjective_whisker` / `isLocallySurjective_whisker`;
   `f.opensFunctor.IsCocontinuous` is a Mathlib instance), so `(restrictPre f).map η_P` is locally
   bijective, i.e. lies in `J_X.W`, and is inverted by sheafification.
3. From 2 we get a `Localization.Lifting`, and `Localization.Monoidal.functorMonoidalOfComp` lifts
   the strong monoidal structure of 1 along sheafification to `Scheme.Modules.restrictFunctor f`.
4. **Braiding**: the braiding compatibility of `restrictPre f` is, open by open, `TensorProduct.comm`
   of `ModuleCat` (`rfl`); the sheafification functor is braided (Mathlib instance); so
   `functorBraidedOfComp` (`LocalizedBraidedOfComp.lean`) gives **`(restrictFunctor f).Braided`**.

This route only uses pushforwards; it does not depend on the strong monoidality of
`PresheafOfModules.pullback`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f]

/-- The scalar comparison used by `restrictFunctor`: `O_X(V) ≅ O_Y(f(V))`. -/
def restrictAlpha : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf where
  app U := (f.appIso U.unop).inv

instance isIso_restrictAlpha : IsIso (restrictAlpha f) := by
  have happ : ∀ U, IsIso ((restrictAlpha f).app U) := fun U =>
    inferInstanceAs (IsIso (f.appIso U.unop).inv)
  exact NatIso.isIso_of_isIso_app _

/-- Restriction along an open immersion at the level of presheaves of modules. -/
abbrev restrictPre :
    _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.pushforward.{u} (_root_.PresheafOfModules.forgetToRingHom (restrictAlpha f))

/-- Restriction of presheaves of modules is a **strong** monoidal functor. -/
noncomputable instance restrictPre_monoidal : (restrictPre f).Monoidal :=
  letI h1 : (_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u}
      f.opensFunctor Y.presheaf).Monoidal := inferInstance
  letI h2 : (_root_.PresheafOfModules.restrictScalarsC.{u}
      (R := X.presheaf) (R' := f.opensFunctor.op ⋙ Y.presheaf) (restrictAlpha f)).Monoidal :=
    @_root_.PresheafOfModules.restrictScalarsC_monoidal _ _ _ _ (restrictAlpha f)
      (isIso_restrictAlpha f)
  inferInstanceAs ((_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u}
      f.opensFunctor Y.presheaf ⋙
    _root_.PresheafOfModules.restrictScalarsC.{u}
      (R := X.presheaf) (R' := f.opensFunctor.op ⋙ Y.presheaf) (restrictAlpha f)).Monoidal)

/-- The right adjoint of the sheafification adjunction (forget to presheaves of modules). -/
abbrev forgetZ (Z : AlgebraicGeometry.Scheme.{u}) :
    Z.Modules ⥤ _root_.PresheafOfModules.{u} Z.ringCatSheaf.obj :=
  SheafOfModules.forget Z.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)

abbrev sheafifyZ (Z : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ Z.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)

abbrev adjZ (Z : AlgebraicGeometry.Scheme.{u}) : sheafifyZ Z ⊣ forgetZ Z :=
  _root_.PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)

/-- The key definitional equality: forgetting commutes with restriction (both sides are "take the
underlying presheaf, then restrict along `f.opensFunctor`"). -/
theorem forget_restrictFunctor_obj (A : Y.Modules) :
    (forgetZ X).obj ((restrictFunctor f).obj A) = (restrictPre f).obj ((forgetZ Y).obj A) := rfl

/-- `η_P` restricted, written as landing in the image of `forgetZ X` (definitionally equal to
`(restrictPre f).map η_P`). -/
def restrictUnit (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    (restrictPre f).obj P ⟶ (forgetZ X).obj ((restrictFunctor f).obj ((sheafifyZ Y).obj P)) :=
  (restrictPre f).map ((adjZ Y).unit.app P)

theorem restrictUnit_naturality {P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj}
    (φ : P ⟶ Q) :
    (restrictPre f).map φ ≫ restrictUnit f Q =
      restrictUnit f P ≫ (forgetZ X).map ((restrictFunctor f).map ((sheafifyZ Y).map φ)) :=
  ((restrictPre f).map_comp φ ((adjZ Y).unit.app Q)).symm.trans
    ((congrArg (restrictPre f).map ((adjZ Y).unit.naturality φ)).trans
      ((restrictPre f).map_comp _ _))

/-- The comparison morphism `L_X (P|_X) ⟶ (L_Y P)|_X`: the transpose of `(restrictPre f).map η_P`
under the sheafification adjunction. -/
def sheafifyRestrictHom (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    (sheafifyZ X).obj ((restrictPre f).obj P) ⟶ (restrictFunctor f).obj ((sheafifyZ Y).obj P) :=
  ((adjZ X).homEquiv _ _).symm (restrictUnit f P)

theorem sheafifyRestrictHom_eq (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    sheafifyRestrictHom f P =
      (sheafifyZ X).map (restrictUnit f P) ≫
        (adjZ X).counit.app ((restrictFunctor f).obj ((sheafifyZ Y).obj P)) :=
  Adjunction.homEquiv_counit (adjZ X) _ _ _

theorem sheafifyRestrictHom_naturality {P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj}
    (φ : P ⟶ Q) :
    (sheafifyZ X).map ((restrictPre f).map φ) ≫ sheafifyRestrictHom f Q =
      sheafifyRestrictHom f P ≫ (restrictFunctor f).map ((sheafifyZ Y).map φ) :=
  ((Adjunction.homEquiv_naturality_left_symm (adjZ X) ((restrictPre f).map φ)
      (restrictUnit f Q)).symm.trans
    ((congrArg (fun z => ((adjZ X).homEquiv ((restrictPre f).obj P)
        ((restrictFunctor f).obj ((sheafifyZ Y).obj Q))).symm z)
      (restrictUnit_naturality f φ)).trans
      (Adjunction.homEquiv_naturality_right_symm (adjZ X) _ _)))

/-- `η_P` restricted is still locally bijective, hence becomes an isomorphism under `L_X`. -/
theorem isIso_sheafify_map_restrict_unit (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    IsIso ((sheafifyZ X).map ((restrictPre f).map ((adjZ Y).unit.app P))) := by
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).map
        ((restrictPre f).map ((adjZ Y).unit.app P))) := by
    show Presheaf.IsLocallyInjective _ (CategoryTheory.Functor.whiskerLeft f.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf))
    exact Presheaf.isLocallyInjective_whisker (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) f.opensFunctor _
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).map
        ((restrictPre f).map ((adjZ Y).unit.app P))) := by
    show Presheaf.IsLocallySurjective _ (CategoryTheory.Functor.whiskerLeft f.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf))
    exact Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) f.opensFunctor _
  have hW := GrothendieckTopology.W_of_isLocallyBijective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).map
        ((restrictPre f).map ((adjZ Y).unit.app P)))
  rw [GrothendieckTopology.W_iff] at hW
  have := hW
  have h2 : IsIso ((CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map
      ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((_root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).map
          ((restrictPre f).map ((adjZ Y).unit.app P))))) := inferInstance
  have h3 : IsIso ((SheafOfModules.forget.{u} X.ringCatSheaf ⋙
      _root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).map
      ((sheafifyZ X).map ((restrictPre f).map ((adjZ Y).unit.app P)))) := h2
  have hrefl : (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
      _root_.PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj).ReflectsIsomorphisms := inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ _ h3 hrefl

instance isIso_sheafifyRestrictHom (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    IsIso (sheafifyRestrictHom f P) := by
  rw [sheafifyRestrictHom_eq]
  have h := isIso_sheafify_map_restrict_unit f P
  have hciso : IsIso (_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit := inferInstance
  have hc : IsIso ((adjZ X).counit.app ((restrictFunctor f).obj ((sheafifyZ Y).obj P))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hciso _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h hc

/-- **Sheafification commutes with restriction along an open immersion**:
`L_X ∘ (·|_X) ≅ (·|_X) ∘ L_Y`, naturally. -/
def sheafifyRestrictIso : restrictPre f ⋙ sheafifyZ X ≅ sheafifyZ Y ⋙ restrictFunctor f :=
  NatIso.ofComponents (fun P => asIso (sheafifyRestrictHom f P))
    (fun φ => sheafifyRestrictHom_naturality f φ)

/-- Sheafification lifts the restriction of presheaves of modules to the restriction of sheaves of
modules. -/
noncomputable instance liftingRestrict :
    CategoryTheory.Localization.Lifting (sheafifyZ Y) (sheafificationW Y)
      (restrictPre f ⋙ sheafifyZ X) (restrictFunctor f) :=
  ⟨(sheafifyRestrictIso f).symm⟩

/-- **Restriction along an open immersion is a strong monoidal functor.** -/
@[instance_reducible]
noncomputable def restrictFunctor_monoidal : (restrictFunctor f).Monoidal :=
  CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    (sheafifyZ Y) (sheafificationW Y) (restrictFunctor f) (restrictPre f ⋙ sheafifyZ X)

/-- `(M ⊗ N)|_X ≅ M|_X ⊗ N|_X` (the open immersion case of Stacks 01CD). -/
def restrictTensorObjIso (M N : Y.Modules) :
    (restrictFunctor f).obj (M ⊗ N) ≅
      (restrictFunctor f).obj M ⊗ (restrictFunctor f).obj N :=
  letI := restrictFunctor_monoidal f
  (Functor.Monoidal.μIso (restrictFunctor f) M N).symm

/-- `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` (**open immersion case**, Stacks 01CD).

Same statement as `ModulesPullbackMonoidal.pullbackTensorObjIso`, but obtained from
`restrictTensorObjIso` above via Mathlib's `restrictFunctorIsoPullback`, without using
`pullbackTensorObjHom_isIso`. -/
def pullbackTensorObjIsoOpen (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  ((restrictFunctorIsoPullback f).app (M ⊗ N)).symm ≪≫ restrictTensorObjIso f M N ≪≫
    tensorIso ((restrictFunctorIsoPullback f).app M) ((restrictFunctorIsoPullback f).app N)

/-- `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` (**open immersion case**, written with `Modules.tensor`).

Same statement as `ModulesPullbackMonoidal.pullbackTensorIso`, obtained independently of it. -/
def pullbackTensorIsoOpen (M N : Y.Modules) :
    (pullback f).obj (tensor M N) ≅ tensor ((pullback f).obj M) ((pullback f).obj N) :=
  (pullback f).mapIso (tensorIsoTensorObj M N) ≪≫ pullbackTensorObjIsoOpen f M N ≪≫
    (tensorIsoTensorObj _ _).symm

/-- The braided structure on presheaves of modules on a scheme (the same spelling conversion as
`Scheme.PresheafOfModules.monoidalCategory`: Mathlib's instance recognizes
`Z.presheaf ⋙ forget₂ CommRingCat RingCat` but not `Z.ringCatSheaf.obj`). -/
instance _root_.AlgebraicGeometry.Scheme.PresheafOfModules.braidedCategory
    (Z : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.BraidedCategory (_root_.PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (CategoryTheory.BraidedCategory
    (_root_.PresheafOfModules.{u} (Z.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat)))

/-- The braiding compatibility of `restrictPre f`: on each open both sides are `TensorProduct.comm`
on `ModuleCat`, so this is `rfl`. -/
theorem restrictPre_braided_aux (M N : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    Functor.LaxMonoidal.μ (restrictPre f) M N ≫ (restrictPre f).map (β_ M N).hom =
      (β_ ((restrictPre f).obj M) ((restrictPre f).obj N)).hom ≫
        Functor.LaxMonoidal.μ (restrictPre f) N M := by
  apply _root_.PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- Restriction of presheaves of modules is a **braided** functor. -/
@[instance_reducible]
noncomputable def restrictPre_braided : (restrictPre f).Braided :=
  { toMonoidal := restrictPre_monoidal f
    braided := restrictPre_braided_aux f }

/-- The sheafification functor is braided (monoidal localization, Mathlib instance, up to spelling). -/
@[instance_reducible]
noncomputable def sheafifyZ_braided (Z : AlgebraicGeometry.Scheme.{u}) : (sheafifyZ Z).Braided :=
  inferInstanceAs ((LX Z).Braided)

/-- **Restriction along an open immersion is a braided monoidal functor.**

Mathlib's `Localization.Monoidal.functorMonoidalOfComp` only gives `Monoidal`; the braided version
`functorBraidedOfComp` is in `LocalizedBraidedOfComp.lean`. -/
@[instance_reducible]
noncomputable def restrictFunctor_braided :
    letI := restrictFunctor_monoidal f
    (restrictFunctor f).Braided :=
  letI := sheafifyZ_braided Y
  letI := sheafifyZ_braided X
  letI := restrictPre_braided f
  letI : (restrictPre f ⋙ sheafifyZ X).Braided := inferInstance
  CategoryTheory.Localization.Monoidal.functorBraidedOfComp
    (sheafifyZ Y) (sheafificationW Y) (restrictFunctor f) (restrictPre f ⋙ sheafifyZ X)

end AlgebraicGeometry.Scheme.Modules

end
