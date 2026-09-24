import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebraMap

/-! # Pullback transports multiplication by a global function

Statement: the pullback functor `f^* : Y.Modules ⥤ X.Modules` of a morphism of schemes `f : X ⟶ Y` transports
"multiplication by a global function" to "multiplication by its pullback":
* `pullback_map_unitMul`: `f^*(unitMul a) ≫ pullbackUnitIso.hom = pullbackUnitIso.hom ≫ unitMul (f^♯ a)` for
  `a ∈ Γ(Y, O_Y)` (`unitMul a : O_Y → O_Y` is `x ↦ x·a`, `PushforwardQcAlgebraMap.lean`);
* `pullback_map_unitScalar`: for any `M : Y.Modules`, `f^*` of the endomorphism
  `(λ_ M).inv ≫ (unitMul a ▷ M) ≫ (λ_ M).hom` ("multiplication by `a` on `M`") is the endomorphism
  "multiplication by `f^♯ a`" of `f^*M`.

Proof (self-contained). The adjoint transpose of `pullbackUnitIso.hom` is Mathlib's `unitToPushforwardObjUnit`,
whose sections are the ring maps `f^♯_U : O_Y(U) → O_X(f⁻¹U)`; by naturality of the adjunction bijection both sides
of the first identity transpose to maps `O_Y → f_*O_X` sending a section `x` over `U` to `f^♯_U(x·a|_U)` resp.
`f^♯_U(x)·(f^♯a)|_{f⁻¹U}`, equal because `f^♯_U` is a ring map compatible with restriction
(`Scheme.Hom.naturality`). The second identity is the general fact that a strong monoidal functor `F` transports
the action of `End(𝟙_)` on objects (`Functor.Monoidal.map_leftUnitor_conj`: expand `F.map` of unitors and whiskerings
with `map_leftUnitor`, `map_leftUnitor_inv`, `map_whiskerRight` and cancel `μ`/`δ`), applied with
`ε = pullbackUnitIso.inv`, `η = pullbackUnitIso.hom` (`pullback_ε_eq`, `pullback_η`).

Source: Stacks 01CD (pullback of a tensor product); Stacks 01AJ (the sheaf-of-rings map `f^♯`).
Used by `reesDeformation_restrictToLambda_one` (`DeformedJetAlgebra.lean`): along the section `λ = 1`, multiplication
by `λ^e` pulls back to the identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

/-- A strong monoidal functor transports "multiplication by `φ ∈ End(𝟙_)`" on `M` to multiplication by the
conjugate `ε ≫ F.map φ ≫ η ∈ End(𝟙_)` on `F.obj M`. -/
theorem CategoryTheory.Functor.Monoidal.map_leftUnitor_conj {C : Type u} {D : Type v} [Category.{w} C]
    [Category.{w} D] [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (M : C)
    (φ : 𝟙_ C ⟶ 𝟙_ C) :
    F.map ((λ_ M).inv ≫ (φ ▷ M) ≫ (λ_ M).hom) =
      (λ_ (F.obj M)).inv ≫
        ((Functor.LaxMonoidal.ε F ≫ F.map φ ≫ Functor.OplaxMonoidal.η F) ▷ F.obj M) ≫
          (λ_ (F.obj M)).hom := by
  rw [F.map_comp, F.map_comp, Functor.Monoidal.map_leftUnitor_inv, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor]
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight]
  simp

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Sections of `unitMul a`: `x ↦ x · a|_U`. -/
theorem unitMul_val_app_apply (a : Γ(Y, ⊤)) (U : (Opens Y)ᵒᵖ) (x : Y.ringCatSheaf.obj.obj U) :
    ((AlgebraicGeometry.Scheme.Modules.unitMul a).val.app U).hom x =
      x * (show Y.ringCatSheaf.obj.obj U from (Y.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom a) := by
  have h3 : ((AlgebraicGeometry.Scheme.Modules.unitMul a).val.app U).hom (1 : Y.ringCatSheaf.obj.obj U) =
      (Y.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom a := by
    have h := SheafOfModules.unitHomEquiv_apply_coe _ (AlgebraicGeometry.Scheme.Modules.unitMul a) U
    unfold AlgebraicGeometry.Scheme.Modules.unitMul at h ⊢
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have h1 : ((AlgebraicGeometry.Scheme.Modules.unitMul a).val.app U).hom
      (x • (1 : Y.ringCatSheaf.obj.obj U)) =
      x • ((AlgebraicGeometry.Scheme.Modules.unitMul a).val.app U).hom (1 : Y.ringCatSheaf.obj.obj U) :=
    _root_.map_smul _ _ _
  have h2 : x • (1 : Y.ringCatSheaf.obj.obj U) = x := mul_one x
  rw [h2] at h1
  rw [h1, h3]
  rfl

/-- `f^♯` commutes with restriction from `⊤`: `f^♯_U (a|_U) = (f^♯ a)|_{f⁻¹U}`. -/
theorem app_res_top (U : Y.Opens) (a : Γ(Y, ⊤)) :
    (f.app U).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a) =
      (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op).hom (f.appTop a) := by
  have h := congrArg (fun g => g.hom a) (AlgebraicGeometry.Scheme.Hom.naturality f (homOfLE (le_top : U ≤ ⊤)).op)
  exact h

/-- Pullback of multiplication by a global function: `f^*(x ↦ x·a) = (x ↦ x·f^♯a)` under `pullbackUnitIso`. -/
theorem pullback_map_unitMul (a : Γ(Y, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (AlgebraicGeometry.Scheme.Modules.unitMul a) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
        AlgebraicGeometry.Scheme.Modules.unitMul (f.appTop a) := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  refine (Adjunction.homEquiv_naturality_left _ _ _).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  have e : (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom f) :=
    haveI : (SheafOfModules.pushforward.{u} (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom f)).IsRightAdjoint :=
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom f)
  refine (congrArg (fun q => AlgebraicGeometry.Scheme.Modules.unitMul a ≫ q) e).trans ?_
  refine Eq.trans ?_ (congrArg (fun q => q ≫ (AlgebraicGeometry.Scheme.Modules.pushforward f).map
    (AlgebraicGeometry.Scheme.Modules.unitMul (f.appTop a))) e.symm)
  ext U
  change (f.app U.unop).hom (((AlgebraicGeometry.Scheme.Modules.unitMul a).val.app U).hom
      (1 : Y.ringCatSheaf.obj.obj U)) =
    ((AlgebraicGeometry.Scheme.Modules.unitMul (f.appTop a)).val.app (op (f ⁻¹ᵁ U.unop))).hom
      ((f.app U.unop).hom (1 : Y.ringCatSheaf.obj.obj U))
  refine Eq.trans ?_ (unitMul_val_app_apply (f.appTop a) (op (f ⁻¹ᵁ U.unop)) _).symm
  rw [unitMul_val_app_apply]
  dsimp only
  exact (map_mul (f.app U.unop).hom (1 : Y.ringCatSheaf.obj.obj U) _).trans
    (congrArg (fun q => (f.app U.unop).hom (1 : Y.ringCatSheaf.obj.obj U) * q) (app_res_top f U.unop a))

/-- Pullback of "multiplication by `a`" on a module `M` is "multiplication by `f^♯ a`" on `f^*M`. -/
theorem pullback_map_unitScalar (a : Γ(Y, ⊤)) (M : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map
        ((λ_ M).inv ≫
          ((show 𝟙_ Y.Modules ⟶ 𝟙_ Y.Modules from AlgebraicGeometry.Scheme.Modules.unitMul a) ▷ M) ≫
            (λ_ M).hom) =
      (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).inv ≫
        ((show 𝟙_ X.Modules ⟶ 𝟙_ X.Modules from
            AlgebraicGeometry.Scheme.Modules.unitMul (f.appTop a)) ▷
          (AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ≫
          (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).hom := by
  rw [CategoryTheory.Functor.Monoidal.map_leftUnitor_conj]
  have hη : Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f) =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom := pullback_η f
  have hc : Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback f) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (AlgebraicGeometry.Scheme.Modules.unitMul a) ≫
        Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f) =
      AlgebraicGeometry.Scheme.Modules.unitMul (f.appTop a) := by
    rw [hη, pullback_ε_eq]
    exact (Iso.inv_comp_eq _).2 (pullback_map_unitMul f a)
  dsimp only
  exact congrArg (fun q : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules =>
    (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).inv ≫
      (q ▷ (AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ≫
        (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).hom) hc

end AlgebraicGeometry.Scheme.Modules

end
