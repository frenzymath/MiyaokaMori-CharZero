import MiyaokaMori.Prelude

/-! # Pushforward of presheaves of modules is lax monoidal

Let `F : C ⥤ D`, `S : Cᵒᵖ ⥤ CommRingCat`, `R : Dᵒᵖ ⥤ CommRingCat` and `φ : S ⟶ F.op ⋙ R` a morphism of
presheaves of commutative rings. Then the restriction of scalars `PresheafOfModules.restrictScalars φ`
is lax monoidal, and so is the pushforward `PresheafOfModules.pushforward φ`; consequently (when the
pushforward is a right adjoint) the pullback `PresheafOfModules.pullback φ` is oplax monoidal, with a
canonical comparison map `δ : f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` whose naturality, associativity and unitality
hold automatically.

Proof:
1. Open set by open set: `ModuleCat.restrictScalars f` (for a homomorphism of commutative rings) is
   lax monoidal (`ModuleCat/Monoidal/Adjunction.lean`, from `extendScalars` strong monoidal by
   doctrinal adjunction), with `ε` given by `r ↦ f r` (`ModuleCat.restrictScalars_η`) and `μ` the
   identity on pure tensors (`ModuleCat.restrictScalars_μ_tmul`).
2. Assemble the `ε`, `μ` of step 1 into morphisms of presheaves of modules: naturality of `ε` follows
   from the naturality of `α`; naturality of `μ` is checked on pure tensors with
   `PresheafOfModules.Monoidal.tensorObj_map_tmul` and `ModuleCat.restrictScalars_μ_tmul`
   (`ModuleCat.MonoidalCategory.tensor_ext`).
3. The five lax monoidal axioms hold open set by open set, by the axioms of the same name in
   `ModuleCat` (the monoidal structure of `PresheafOfModules` is objectwise; all `app` lemmas are `rfl`).
4. `PresheafOfModules.pushforward φ = pushforward₀ F R ⋙ restrictScalars φ` holds by `rfl`
   (`pushforward_eq_comp`), and `pushforward₀OfCommRingCat` is strong monoidal
   (Mathlib `Presheaf/PushforwardZeroMonoidal.lean`), so the pushforward is lax monoidal (composite
   instance).
5. `Adjunction.leftAdjointOplaxMonoidal` (doctrinal adjunction, `CategoryTheory/Monoidal/Functor.lean`)
   gives the oplax monoidal structure on the pullback.

References: Mathlib `Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`,
`Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`, `CategoryTheory/Monoidal/Functor.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u u' v'
open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules
variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ R')

noncomputable abbrev restrictScalarsC :
    PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  restrictScalars (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

noncomputable def rsEps : 𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) ⟶
    (restrictScalarsC α).obj (𝟙_ _) where
  app X := Functor.LaxMonoidal.ε (ModuleCat.restrictScalars (α.app X).hom)
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    show (α.app Y).hom ((R.map f).hom r) = (R'.map f).hom ((α.app X).hom r)
    exact congrArg (fun g : R.obj X ⟶ R'.obj Y => g.hom r) (α.naturality f)

noncomputable def rsMu (M N : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat)) :
    (restrictScalarsC α).obj M ⊗ (restrictScalarsC α).obj N ⟶ (restrictScalarsC α).obj (M ⊗ N) where
  app X := Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app X).hom) (M.obj X) (N.obj X)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rfl

noncomputable instance restrictScalarsC_lax : (restrictScalarsC α).LaxMonoidal where
  ε := rsEps α
  μ M N := rsMu α M N
  μ_natural_left f X' := by
    ext1 Z
    exact Functor.LaxMonoidal.μ_natural_left
      (ModuleCat.restrictScalars (α.app Z).hom) (f.app Z) (X'.obj Z)
  μ_natural_right X' f := by
    ext1 Z
    exact Functor.LaxMonoidal.μ_natural_right
      (ModuleCat.restrictScalars (α.app Z).hom) (X'.obj Z) (f.app Z)
  associativity M N P := by
    ext1 Z
    exact Functor.LaxMonoidal.associativity
      (ModuleCat.restrictScalars (α.app Z).hom) (M.obj Z) (N.obj Z) (P.obj Z)
  left_unitality M := by
    ext1 Z
    exact Functor.LaxMonoidal.left_unitality
      (ModuleCat.restrictScalars (α.app Z).hom) (M.obj Z)
  right_unitality M := by
    ext1 Z
    exact Functor.LaxMonoidal.right_unitality
      (ModuleCat.restrictScalars (α.app Z).hom) (M.obj Z)

section Pushforward
variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
  {RD : Dᵒᵖ ⥤ CommRingCat.{u}} {SC : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : SC ⟶ F.op ⋙ RD)

/-- `φ` with commutativity forgotten, with type of the shape `S ⟶ F.op ⋙ R` expected by
`pushforward` / `pullback` (definitionally equal to `whiskerRight φ _`, up to bracketing). -/
noncomputable abbrev forgetToRingHom :
    SC ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ (RD ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

theorem pushforward_eq_comp :
    pushforward.{u} (forgetToRingHom φ) =
      pushforward₀OfCommRingCat F RD ⋙ restrictScalarsC (R := SC) (R' := F.op ⋙ RD) φ := rfl

/-- The pushforward of presheaves of modules is lax monoidal: `pushforward₀` (strong monoidal, Mathlib)
composed with restriction of scalars (lax, above). -/
noncomputable instance pushforward_lax : (pushforward.{u} (forgetToRingHom φ)).LaxMonoidal :=
  inferInstanceAs ((pushforward₀OfCommRingCat F RD ⋙
    restrictScalarsC (R := SC) (R' := F.op ⋙ RD) φ).LaxMonoidal)

/-- The pullback of presheaves of modules is oplax monoidal (doctrinal adjunction). -/
@[instance_reducible]
noncomputable def pullback_oplax [(pushforward.{u} (forgetToRingHom φ)).IsRightAdjoint] :
    (pullback.{u} (forgetToRingHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (forgetToRingHom φ)).leftAdjointOplaxMonoidal

end Pushforward

end PresheafOfModules
