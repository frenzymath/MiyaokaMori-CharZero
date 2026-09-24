import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The identity pullback isomorphism is monoidal

Statement: Mathlib's identification `pullbackId X : pullback (𝟙 X) ≅ 𝟭 X.Modules` is a **monoidal** natural
isomorphism, i.e. it is compatible with the strong monoidal structure of the pullback functor
(`ModulesPullbackMonoidal.lean`):
(U) `ε ≫ (pullbackId X).hom.app 𝟙_ = 𝟙`  (`ε_pullbackId`);
(T) `μ A B ≫ (pullbackId X).hom.app (A ⊗ B) = (pullbackId X).hom.app A ⊗ₘ (pullbackId X).hom.app B`
    (`μ_pullbackId`).

Proof (self-contained). `pullbackId` is the left-adjoint mate of `pushforwardId` (Mathlib
`conjugateEquiv_pullbackId_hom`), so by `unit_conjugateEquiv` the adjoint transpose of
`(pullbackId X).hom.app A ≫ h` is `(pushforwardId X).inv.app A ≫ (𝟙 X)_* h` (`homEquiv_pullbackId_hom_app_comp`);
the components of `pushforwardId` are identities on sections (Mathlib `pushforwardId_inv_app_app`).
(U): both sides of `(pullbackId X).hom.app 𝟙_ = (pullbackUnitIso (𝟙 X)).hom` have adjoint transposes
`𝟙_ → (𝟙 X)_* 𝟙_` whose sections are the identity (`unitToPushforwardObjUnit` of `𝟙 X` is the identity ring map).
(T): both sides of `(pullbackId X).hom.app (A ⊗ B) = δ ≫ (pId A ⊗ₘ pId B)` are maps out of `𝟙^*(A ⊗ B)`; their
transposes are maps `A ⊗ B → (𝟙 X)_*(A ⊗ B)`, compared on section pairs `a ⊗ b` with `tensorObj_hom_ext`: the
transpose of `δ` sends `a ⊗ b` to `η a ⊗ η b` (`homEquiv_pullbackTensorObjHom_tensorSections`), `μ` of the pushforward
is the identity on section pairs (`pushforwardLaxMonoidal_μ_tensorSections`), and `pId ∘ η = 𝟙` on sections.
Then (U), (T) are restated with `ε = pullbackUnitIso.inv`, `μ = pullbackTensorObjIso.inv`.

Source: Stacks 01CD (canonicity of the pullback of a tensor product); the mate calculus of Mathlib
`CategoryTheory.Adjunction.Mates`. Used by `GradedQCAlgebra.pullbackId` (`GradedQcAlgebraPullbackId.lean`), which is
needed for `reesDeformation_restrictToLambda_one` (fibre of the Rees deformation at `λ = 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u})

/-- The adjoint transpose of `(pullbackId X).hom.app A` is `(pushforwardId X).inv.app A`
(`pullbackId` is the mate of `pushforwardId`: Mathlib `conjugateEquiv_pullbackId_hom` + `unit_conjugateEquiv`). -/
theorem homEquiv_pullbackId_hom_app (A : X.Modules) :
    (pullbackPushforwardAdjunction (𝟙 X)).homEquiv A ((𝟭 X.Modules).obj A) ((pullbackId X).hom.app A) =
      (pushforwardId X).inv.app A := by
  have hu := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom A
  rw [conjugateEquiv_pullbackId_hom] at hu
  rw [Adjunction.homEquiv_unit, ← hu]
  simp

/-- The adjoint transpose of `(pullbackId X).hom.app A ≫ h` is `(pushforwardId X).inv.app A ≫ (𝟙 X)_* h`. -/
theorem homEquiv_pullbackId_hom_app_comp {A B : X.Modules} (h : A ⟶ B) :
    (pullbackPushforwardAdjunction (𝟙 X)).homEquiv A B ((pullbackId X).hom.app A ≫ h) =
      (pushforwardId X).inv.app A ≫ (pushforward (𝟙 X)).map h := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackId_hom_app]

/-- On sections, `(pullbackId X).hom.app A` inverts the adjunction unit. -/
theorem pullbackId_hom_app_unit_app_apply (A : X.Modules) (U : X.Opens) (a : A.val.obj (op U)) :
    ((pullbackId X).hom.app A).val.app (op ((𝟙 X) ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction (𝟙 X)).unit.app A).val.app (op U) a) = a := by
  have h := homEquiv_pullbackId_hom_app X A
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.val.app (op U) a) h

/-- (U) `(pullbackId X).hom` on the unit is the canonical `pullbackUnitIso (𝟙 X)`. -/
theorem pullbackId_hom_app_unit :
    (pullbackId X).hom.app (MonoidalCategoryStruct.tensorUnit X.Modules) =
      (pullbackUnitIso (𝟙 X)).hom := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have e : (pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _ (pullbackUnitIso (𝟙 X)).hom =
      SheafOfModules.unitToPushforwardObjUnit (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (𝟙 X)) :=
    haveI : (SheafOfModules.pushforward.{u} (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (𝟙 X))).IsRightAdjoint :=
      (pullbackPushforwardAdjunction (𝟙 X)).isRightAdjoint
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (𝟙 X))
  refine (homEquiv_pullbackId_hom_app X _).trans (Eq.trans ?_ e.symm)
  ext U x
  rfl

/-- (T) `(pullbackId X).hom` on a tensor product is the comparison map `δ` followed by the tensor product of
the components. -/
theorem pullbackId_hom_app_tensorObj (A B : X.Modules) :
    (pullbackId X).hom.app (MonoidalCategoryStruct.tensorObj A B) =
      pullbackTensorObjHom (𝟙 X) A B ≫
        MonoidalCategoryStruct.tensorHom ((pullbackId X).hom.app A) ((pullbackId X).hom.app B) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [homEquiv_pullbackId_hom_app, Adjunction.homEquiv_naturality_right, homEquiv_pullbackTensorObjHom]
  apply tensorObj_hom_ext
  intro U a b
  have d1 := tensorHom_tensorSections ((pullbackPushforwardAdjunction (𝟙 X)).unit.app A)
    ((pullbackPushforwardAdjunction (𝟙 X)).unit.app B) U a b
  have d2 := pushforwardLaxMonoidal_μ_tensorSections (𝟙 X) ((pullback (𝟙 X)).obj A)
    ((pullback (𝟙 X)).obj B) U
    (((pullbackPushforwardAdjunction (𝟙 X)).unit.app A).val.app (op U) a)
    (((pullbackPushforwardAdjunction (𝟙 X)).unit.app B).val.app (op U) b)
  have d3 := tensorHom_tensorSections ((pullbackId X).hom.app A) ((pullbackId X).hom.app B)
    ((𝟙 X) ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction (𝟙 X)).unit.app A).val.app (op U) a)
    (((pullbackPushforwardAdjunction (𝟙 X)).unit.app B).val.app (op U) b)
  have e1 := pullbackId_hom_app_unit_app_apply X A U a
  have e2 := pullbackId_hom_app_unit_app_apply X B U b
  refine Eq.trans ?_ (congrArg (fun z => ((Functor.LaxMonoidal.μ (pushforward (𝟙 X))
      (self := pushforwardLaxMonoidal (𝟙 X)) ((pullback (𝟙 X)).obj A) ((pullback (𝟙 X)).obj B) ≫
    (pushforward (𝟙 X)).map (MonoidalCategoryStruct.tensorHom ((pullbackId X).hom.app A)
      ((pullbackId X).hom.app B))).val.app (op U) z)) d1.symm)
  refine Eq.trans ?_ (congrArg (fun z => ((pushforward (𝟙 X)).map
    (MonoidalCategoryStruct.tensorHom ((pullbackId X).hom.app A)
      ((pullbackId X).hom.app B))).val.app (op U) z) d2.symm)
  refine Eq.trans ?_ d3.symm
  refine Eq.trans ?_ (congrArg₂ (tensorSections A B ((𝟙 X) ⁻¹ᵁ U)) e1.symm e2.symm)
  rfl

/-- `ε` of the strong monoidal structure of `pullback (𝟙 X)` is inverted by `pullbackId`. -/
theorem ε_pullbackId :
    Functor.LaxMonoidal.ε (pullback (𝟙 X)) ≫
        (pullbackId X).hom.app (MonoidalCategoryStruct.tensorUnit X.Modules) = 𝟙 _ := by
  rw [pullback_ε_eq]
  exact (congrArg (fun q => (pullbackUnitIso (𝟙 X)).inv ≫ q) (pullbackId_hom_app_unit X)).trans
    (Iso.inv_hom_id _)

/-- `μ` of the strong monoidal structure of `pullback (𝟙 X)` is compatible with `pullbackId`. -/
theorem μ_pullbackId (A B : X.Modules) :
    Functor.LaxMonoidal.μ (pullback (𝟙 X)) A B ≫
        (pullbackId X).hom.app (MonoidalCategoryStruct.tensorObj A B) =
      MonoidalCategoryStruct.tensorHom ((pullbackId X).hom.app A) ((pullbackId X).hom.app B) := by
  rw [pullback_μ_eq, pullbackId_hom_app_tensorObj, ← Category.assoc]
  have h : (pullbackTensorObjIso (𝟙 X) A B).inv ≫ pullbackTensorObjHom (𝟙 X) A B = 𝟙 _ :=
    (pullbackTensorObjIso (𝟙 X) A B).inv_hom_id
  rw [h, Category.id_comp]

end AlgebraicGeometry.Scheme.Modules

end
