import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # Bilinearity of the section pairing of the tensor product

The section pairing `tensorSections A B U : Γ(A,U) × Γ(B,U) → Γ(A ⊗ B, U)` of
`ModulesTensorMonoidalIso` (`a, b ↦` the image of `a ⊗ b` under sheafification) is `Γ(X,U)`-bilinear
and commutes with restriction to open subsets:
`(A ⊗ B).map i (tensorSections A B U a b) = tensorSections A B V (A.map i a) (B.map i b)`.

Proof: by definition `tensorSections A B U a b` is the component at `U` of `sheafifyTensorTo A B`
applied to the component at `U` of the sheafification unit applied to `a ⊗ₜ b`. Both components are
morphisms in a module category, hence additive and homogeneous; additivity then follows from
`add_tmul / tmul_add` for `TensorProduct`. Compatibility with restriction: both components are
morphisms of presheaves of modules, so two applications of `PresheafOfModules.naturality_apply` move
the restriction innermost, where `(G A ⊗ G B).map i (a ⊗ₜ b) = a|_V ⊗ₜ b|_V` holds by definition of
`tensorObjMap`.

Used for the currying and evaluation of the tensor–Hom adjunction (Stacks 01CM).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (A B : X.Modules)

/-- The section pairing is additive in the second variable. -/
theorem tensorSections_add_right (U : X.Opens) (a : Γ(A, U)) (b b' : Γ(B, U)) :
    tensorSections A B U a (b + b') = tensorSections A B U a b + tensorSections A B U a b' := by
  unfold AlgebraicGeometry.Scheme.Modules.tensorSections
  erw [TensorProduct.tmul_add, map_add, map_add]

/-- The section pairing is additive in the first variable. -/
theorem tensorSections_add_left (U : X.Opens) (a a' : Γ(A, U)) (b : Γ(B, U)) :
    tensorSections A B U (a + a') b = tensorSections A B U a b + tensorSections A B U a' b := by
  unfold AlgebraicGeometry.Scheme.Modules.tensorSections
  erw [TensorProduct.add_tmul, map_add, map_add]

/-- Notation: the underlying presheaf of modules of a sheaf of modules (scalars restricted along the
identity). -/
abbrev toPre (A : X.Modules) : X.PresheafOfModules :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A

/-- Notation: the component of the sheafification unit at the presheaf tensor product
`toPre A ⊗ toPre B`. -/
abbrev tensorUnitApp (A B : X.Modules) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (toPre A) (toPre B) ⟶
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (toPre A) (toPre B))) :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (toPre A) (toPre B))

/-- The section pairing is homogeneous in the first variable. To avoid the two spellings of the
scalar ring (`Γ(X, U)` and `(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)`), which instance
search does not identify, the result is stated with an explicit variable `z : Γ(A ⊗ B, U)` (pass
`_ rfl` at call sites). Proof: `r • (a ⊗ₜ b) = (r • a) ⊗ₜ b` is `rfl` in Mathlib
(`TensorProduct.smul_tmul'`); then move the scalar through the two module-category morphisms, the
sheafification unit and `sheafifyTensorTo`. -/
theorem tensorSections_smul_left (U : X.Opens) (r : Γ(X, U)) (a : Γ(A, U)) (b : Γ(B, U))
    (z : Γ(CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B, U))
    (hz : z = tensorSections A B U a b) :
    tensorSections A B U (r • a) b = r • z := by
  subst hz
  exact ((congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
      (Opposite.op U) w)
      (((tensorUnitApp A B).app (Opposite.op U)).hom.map_smul r
        (TensorProduct.tmul _ a b))).trans
    (((AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
      (Opposite.op U)).hom.map_smul r _))

set_option backward.isDefEq.respectTransparency false in
/-- The section pairing commutes with restriction to open subsets. -/
theorem tensorSections_restrict {U V : X.Opens} (i : V ⟶ U) (a : A.val.obj (Opposite.op U))
    (b : B.val.obj (Opposite.op U)) :
    ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).val.map i.op)
        (tensorSections A B U a b) =
      tensorSections A B V ((A.val.map i.op) a) ((B.val.map i.op) b) := by
  have h1 := _root_.PresheafOfModules.naturality_apply
    (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val i.op
    ((((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app
      (Opposite.op U)) (TensorProduct.tmul _ a b))
  have h2 := _root_.PresheafOfModules.naturality_apply
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))) i.op
    (TensorProduct.tmul _ a b)
  exact h1.symm.trans
    (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
      (Opposite.op V) z) h2.symm)

/-- The section pairing is homogeneous in the **second** variable, stated like
`tensorSections_smul_left` (explicit variable `z` on the result side; pass `_ rfl` at call sites).

Extracting a scalar from the right factor with `TensorProduct.tmul_smul` would need `CompatibleSMul`,
which instance search cannot supply because of the two spellings of the scalar ring. Instead,
`fun y ↦ a ⊗ₜ y` is the linear map `TensorProduct.mk _ _ _ a`, whose `map_smul` gives
`a ⊗ₜ (r • b) = r • (a ⊗ₜ b)` directly, with the scalar ring fixed by the goal inside `congrArg`. The
rest is as in `tensorSections_smul_left`: move the scalar through the sheafification unit and
`sheafifyTensorTo`. -/
theorem tensorSections_smul_right (U : X.Opens) (r : Γ(X, U)) (a : Γ(A, U)) (b : Γ(B, U))
    (z : Γ(CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B, U))
    (hz : z = tensorSections A B U a b) :
    tensorSections A B U a (r • b) = r • z := by
  subst hz
  unfold AlgebraicGeometry.Scheme.Modules.tensorSections
  exact Eq.trans
    (congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
        (Opposite.op U) (((tensorUnitApp A B).app (Opposite.op U)) w))
      ((TensorProduct.mk _ _ _ a).map_smul r b))
    ((congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
          (Opposite.op U) w)
        (((tensorUnitApp A B).app (Opposite.op U)).hom.map_smul r
          (TensorProduct.tmul _ a b))).trans
      (((AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A B).val.app
        (Opposite.op U)).hom.map_smul r _))

end AlgebraicGeometry.Scheme.Modules

end
