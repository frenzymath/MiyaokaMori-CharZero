import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong

/-! # Pullback commutes with the tensor product

The pullback of `O_X`-modules commutes with the tensor product: `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N`
(Stacks 01CD), and the isomorphism sends a section `s ⊗ t` to `g^*s ⊗ g^*t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem sheafifyTensorTo_sectionTensor {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo M N).val.app (Opposite.op (⊤ : X.Opens))
      (sectionTensor s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := by
  rfl

private theorem tensorToSheafify_tensorSections_eq_sectionTensor
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorToSheafify M N).val.app (Opposite.op (⊤ : X.Opens))
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t) = sectionTensor s t := by
  set_option maxHeartbeats 0 in
    have h := AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections M N ⊤ s t
    exact h.trans (by rfl)

private theorem sectionPullbackAlong_map' {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    {M M' : Y.Modules} (φ : M ⟶ M')
    (a : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (φ.app ⊤ a) =
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map φ).app ⊤
        (sectionPullbackAlong g a) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h2 := congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) a) h
  exact h2

private theorem homEquiv_app_top {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    {A : Y.Modules} {B : X.Modules} (φ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj A ⟶ B)
    (a : (A.val.obj (Opposite.op ⊤) : Type u)) :
    φ.app ⊤ (sectionPullbackAlong g a) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv A B φ).app ⊤ a := by
  have h := Adjunction.homEquiv_unit
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g) A B φ
  exact congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) a) h

private theorem sheafification_homEquiv_symm_unit'
    {X : AlgebraicGeometry.Scheme.{u}}
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

/-- `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N` (Stacks 01CD), as an existence statement. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_tensor {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (M N : Y.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.tensor M N) ≅
      AlgebraicGeometry.Scheme.Modules.tensor ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N)) :=
  ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorIso g M N⟩

/-- Section formula: the canonical comparison isomorphism `pullbackTensorIso` sends `g^*(s ⊗ t)` to
`g^*s ⊗ g^*t`.

Proof: `pullbackTensorIso.hom = g^*(sheafifyTensorTo M N) ≫ pullbackTensorObjHom g M N ≫
tensorToSheafify (g^*M) (g^*N)` (all three pieces by definition). The first piece is handled by
naturality of the adjunction unit, after which the inner term is
`(sheafifyTensorTo M N).app ⊤ (sectionTensor s t) = tensorSections M N ⊤ s t`. The second piece
`δ := pullbackTensorObjHom g M N` is an adjoint transpose, and its value on a pairing of sections is
`homEquiv_pullbackTensorObjHom_tensorSections`: `tensorSections (g^*M) (g^*N) (g⁻¹U) (η m) (η n)`.
Finally `tensorToSheafify_tensorSections` identifies the result with the image of the
sheafification unit on `g^*s ⊗ₜ g^*t`, which is by definition `sectionTensor (g^*s) (g^*t)`. -/

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) {M N : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso g M N).hom.app ⊤
        (sectionPullbackAlong g (sectionTensor s t)) =
      sectionTensor (sectionPullbackAlong g s) (sectionPullbackAlong g t) := by
  show (AlgebraicGeometry.Scheme.Modules.tensorToSheafify
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N)).app ⊤
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullback g).map
          (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo M N)).app ⊤
          (sectionPullbackAlong g (sectionTensor s t)))) = _
  rw [← sectionPullbackAlong_map' g (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo M N)
    (sectionTensor s t)]
  have hs : AlgebraicGeometry.Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo M N) ⊤
      (sectionTensor s t) = AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := by
    change (AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo M N).val.app
      (Opposite.op (⊤ : Y.Opens)) (sectionTensor s t) = _
    exact sheafifyTensorTo_sectionTensor s t
  refine Eq.trans (congrArg (fun z =>
    (AlgebraicGeometry.Scheme.Modules.tensorToSheafify
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N)).app ⊤
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N).app ⊤
        (sectionPullbackAlong g z))) hs) ?_
  have hδ := homEquiv_app_top g (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N)
    (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)
  refine Eq.trans (congrArg
    ((AlgebraicGeometry.Scheme.Modules.tensorToSheafify
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N)).app ⊤) hδ) ?_
  -- `pullbackTensorObjHom` is the oplax `δ`; its value on a pairing of sections is given by one lemma.
  have hkey := AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections
    g M N ⊤ s t
  refine Eq.trans (congrArg (fun z =>
    (AlgebraicGeometry.Scheme.Modules.tensorToSheafify
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N)).val.app
      (Opposite.op (⊤ : X.Opens)) z) hkey) ?_
  exact tensorToSheafify_tensorSections_eq_sectionTensor
    (sectionPullbackAlong g s) (sectionPullbackAlong g t)

end
