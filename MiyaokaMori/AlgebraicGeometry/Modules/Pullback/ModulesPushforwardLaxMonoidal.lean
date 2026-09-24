import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidalReduction
import MiyaokaMori.CategoryTheory.PresheafModulesPushforwardMonoidal
import MiyaokaMori.CategoryTheory.LaxMonoidalTransport

/-! # Pushforward is lax monoidal, pullback is oplax monoidal

Let `f : X ⟶ Y` be a morphism of schemes. The pushforward `Scheme.Modules.pushforward f` of sheaves
of modules is a lax monoidal functor; hence (doctrinal adjunction) the pullback
`Scheme.Modules.pullback f` is an **oplax** monoidal functor, with canonical comparison morphisms
`δ : f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` and `η : f^*O_Y ⟶ O_X`, whose naturality, associativity and
unitality come for free.

Proof:
1. Let `G_Z := SheafOfModules.forget ⋙ restrictScalars 𝟙` (the right adjoint of sheafification
   `L_Z`). `L_Z` is strong monoidal (`sheafify_monoidal`), so `G_Z` is lax monoidal
   (`Adjunction.rightAdjointLaxMonoidal`).
2. The pushforward of presheaves of modules is lax monoidal (`PresheafOfModules.pushforward_lax`
   with `φ := f.c`).
3. The functor identity `G_X ⋙ f_*^{pre} = f_* ⋙ G_Y` is `rfl` (Mathlib defines the underlying
   presheaf of the sheaf pushforward as the presheaf pushforward). Hence
   `G_X ⋙ f_*^{pre} ⋙ L_Y = f_* ⋙ (G_Y ⋙ L_Y) ≅ f_*`, the last step being the counit of the
   sheafification adjunction (an isomorphism on sheaves).
4. A composite of three lax monoidal functors is lax monoidal; transport along the isomorphism of
   step 3 with `Functor.LaxMonoidal.transport`.
5. `Adjunction.leftAdjointOplaxMonoidal` gives the oplax structure of `f^*`.

References: Stacks 01CD (categorical construction of the comparison morphism); Mathlib
`CategoryTheory/Monoidal/Functor.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The right adjoint of sheafification `sheafify Z`: forget to presheaves of modules. -/
abbrev forgetPre (Z : AlgebraicGeometry.Scheme.{u}) :
    Z.Modules ⥤ _root_.PresheafOfModules.{u} Z.ringCatSheaf.obj :=
  SheafOfModules.forget Z.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)

/-- The sheafification adjunction, written as `sheafify Z ⊣ forgetPre Z`. -/
abbrev sheafifyAdj (Z : AlgebraicGeometry.Scheme.{u}) : sheafify Z ⊣ forgetPre Z :=
  _root_.PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)

/-- Forgetting to presheaves of modules is lax monoidal (right adjoint of the strong monoidal
sheafification functor). Not registered as a global instance. -/
@[instance_reducible]
def forgetPre_lax (Z : AlgebraicGeometry.Scheme.{u}) : (forgetPre Z).LaxMonoidal :=
  (sheafifyAdj Z).rightAdjointLaxMonoidal

/-- The pushforward of presheaves of modules (along the morphism of sheaves of rings of `f`). -/
abbrev pushforwardPre :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj :=
  _root_.PresheafOfModules.pushforward.{u} (f.toRingCatSheafHom).hom

/-- The pushforward of presheaves of modules is lax monoidal (`PresheafOfModules.pushforward_lax` with
`φ := f.c`). -/
@[instance_reducible]
def pushforwardPre_lax : (pushforwardPre f).LaxMonoidal :=
  _root_.PresheafOfModules.pushforward_lax (F := TopologicalSpace.Opens.map f.base)
    (RD := X.presheaf) (SC := Y.presheaf) f.c

/-- The underlying presheaf of the sheaf pushforward is the presheaf pushforward (an equality of
functors, `rfl`). -/
theorem forgetPre_comp_pushforwardPre :
    forgetPre X ⋙ pushforwardPre f = pushforward f ⋙ forgetPre Y := rfl

/-- The counit of the sheafification adjunction is an isomorphism (Mathlib instance; `G_Z ⋙ L_Z ≅ 𝟭`). -/
def sheafifyCounitIso (Z : AlgebraicGeometry.Scheme.{u}) :=
  asIso (_root_.PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Z.ringCatSheaf.obj)).counit

/-- The natural isomorphism `G_X ⋙ f_*^{pre} ⋙ L_Y ≅ f_*`: the left side is `f_* ⋙ (G_Y ⋙ L_Y)` by
`rfl`, then apply the counit of the sheafification adjunction (an isomorphism on sheaves). -/
def forgetPushforwardSheafifyIso :
    forgetPre X ⋙ pushforwardPre f ⋙ sheafify Y ≅ pushforward f :=
  NatIso.ofComponents (fun A => (sheafifyCounitIso Y).app ((pushforward f).obj A))
    (fun φ => (sheafifyCounitIso Y).hom.naturality ((pushforward f).map φ))

/-- **The pushforward of sheaves of modules is lax monoidal.** Not registered as a global instance
(use `letI` / `attribute [local instance]`). -/
@[instance_reducible]
def pushforwardLaxMonoidal : (pushforward f).LaxMonoidal :=
  letI := forgetPre_lax X
  letI := pushforwardPre_lax f
  Functor.LaxMonoidal.transport (forgetPushforwardSheafifyIso f)

section Eps
open Functor.LaxMonoidal

/-- The `ε` of `G_Z` is the identity: a triangle identity of the adjunction (`G_Z(O_Z)` is
definitionally the presheaf unit). -/
theorem forgetPre_ε (Z : AlgebraicGeometry.Scheme.{u}) :
    letI := forgetPre_lax Z
    ε (forgetPre Z) = 𝟙 _ :=
  (sheafifyAdj Z).right_triangle_components (SheafOfModules.unit Z.ringCatSheaf)

/-- The `ε` of the presheaf pushforward is `f^♯` on sections (`ModuleCat.restrictScalars_η`). -/
theorem pushforwardPre_ε :
    letI := pushforwardPre_lax f
    ε (pushforwardPre f) = (forgetPre Y).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (ModuleCat.restrictScalars_η (f.c.app U).hom x).trans rfl

/-- The `ε` of sheafification is the inverse of the counit isomorphism (definition of the monoidal
localization). -/
theorem sheafify_ε (Z : AlgebraicGeometry.Scheme.{u}) :
    ε (sheafify Z) = (sheafifyCounitIso Z).inv.app (𝟙_ Z.Modules) := rfl

/-- **The `ε` of the lax structure of pushforward is Mathlib's `unitToPushforwardObjUnit`** (`f^♯` on
sections). Hence the `η` of the oplax structure of pullback is `pullbackObjUnitToUnit`, an
isomorphism (Mathlib; the underlying functor is final). -/
theorem pushforwardLaxMonoidal_ε :
    letI := pushforwardLaxMonoidal f
    ε (pushforward f) = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let _ := forgetPre_lax X
  let _ := pushforwardPre_lax f
  unfold pushforwardLaxMonoidal
  rw [Functor.LaxMonoidal.transport_ε]
  erw [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_ε]
  rw [forgetPre_ε, pushforwardPre_ε, sheafify_ε]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hi : (forgetPushforwardSheafifyIso f).hom.app (𝟙_ X.Modules) =
      (sheafifyCounitIso Y).hom.app ((pushforward f).obj (𝟙_ X.Modules)) := rfl
  rw [hi]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (sheafifyCounitIso Y).inv.app (𝟙_ Y.Modules) ≫ t)
      ((sheafifyCounitIso Y).hom.naturality
        (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom f)))).trans
      (Iso.inv_hom_id_app_assoc (sheafifyCounitIso Y) _ _))

end Eps

/-- **The pullback of sheaves of modules is oplax monoidal** (doctrinal adjunction). `δ` is the
comparison morphism `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` of Stacks 01CD. Registered as a global instance. -/
instance pullbackOplaxMonoidal : (pullback f).OplaxMonoidal :=
  letI := pushforwardLaxMonoidal f
  (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal

/-- The pullback–pushforward adjunction is compatible with the two (op)lax structures above. -/
theorem pullbackPushforwardAdjunction_isMonoidal :
    letI := pushforwardLaxMonoidal f
    (pullbackPushforwardAdjunction f).IsMonoidal :=
  letI := pushforwardLaxMonoidal f
  inferInstance

end AlgebraicGeometry.Scheme.Modules
end
