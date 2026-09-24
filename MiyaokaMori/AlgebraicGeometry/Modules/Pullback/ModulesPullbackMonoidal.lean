import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective

/-! # Pullback of sheaves of modules is a strong monoidal functor

The pullback of sheaves of modules is a (strong) monoidal functor: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`,
`f^*O_Y ≅ O_X`, compatibly with associators, unitors and the braiding.

References: Stacks 01AG / 01CE (pullback commutes with tensor products), Stacks 01CD.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The comparison morphism `f^*(M ⊗ N) → f^*M ⊗ f^*N` (`⊗` the monoidal structure of `X.Modules`):
the `δ` of the oplax monoidal structure `pullbackOplaxMonoidal` of the pullback
(`ModulesPushforwardLaxMonoidal`: pushforward is lax monoidal + doctrinal adjunction). Naturality,
associativity and unitality come directly from the oplax structure. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) :=
  CategoryTheory.Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback f)
    (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) M N

/-- `pullbackTensorObjHom` is the `δ` of the oplax structure (by definition, `rfl`). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_eq_δ {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N =
      CategoryTheory.Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback f)
        (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) M N := rfl

/-- The adjoint transpose of `δ`: `(η_M ⊗ η_N) ≫ μ_{f_*}` (definition of
`Adjunction.leftAdjointOplaxMonoidal`). -/
theorem AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N) =
      CategoryTheory.MonoidalCategoryStruct.tensorHom
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pushforward f)
          (self := AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal f) _ _ :=
  Equiv.apply_symm_apply _ _

/-- **Characterization of the comparison morphism on sections**: the adjoint transpose of `δ` sends
the pairing `m ⊗ n ∈ (M ⊗ N)(U)` to `η_M(m) ⊗ η_N(n) ∈ (f^*M ⊗ f^*N)(f⁻¹U)`, where `η` is the unit
of the pullback–pushforward adjunction. By `Modules.tensorObj_hom_ext` this property determines
`δ` uniquely. -/
theorem AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (Opposite.op U)) (n : N.val.obj (Opposite.op U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)).val.app (Opposite.op U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N U m n) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
          (Opposite.op U) m)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
          (Opposite.op U) n) := by
  rw [AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom]
  refine (congrArg
    ((CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pushforward f)
      (self := AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal f) _ _).val.app (Opposite.op U))
    (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) U m n)).trans ?_
  exact AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal_μ_tensorSections f _ _ U _ _

/-- `δ` is compatible with the braiding: `δ_{M,N} ≫ β = f^*(β) ≫ δ_{N,M}` (checked on pairings of
sections after taking adjoint transposes). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_braiding
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N ≫
        (β_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (β_ M N).hom ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f N M := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
  intro U s t
  refine (congrArg (((AlgebraicGeometry.Scheme.Modules.pushforward f).map (β_ _ _).hom).val.app
      (Opposite.op U))
    (AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections f M N U s t)).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections _ _ (f ⁻¹ᵁ U) _ _).trans ?_
  refine Eq.trans ?_ (congrArg
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f N M)).val.app (Opposite.op U))
    (AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections M N U s t).symm)
  exact (AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections
    f N M U t s).symm


/- ## `δ` is an isomorphism (Stacks 01CD): stalkwise verification
   1. A morphism of sheaves of modules is an isomorphism iff it is bijective on every stalk:
      `AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`;
   2. stalks of pullbacks: `(f^*P)_x ≅ O_{X,x} ⊗_{O_{Y,y}} P_y`;
   3. stalks of tensor products (Stacks 01CB): `(A ⊗ B)_x ≅ A_x ⊗_{O_{X,x}} B_x`
      (`tensorStalkEquiv`, from `TensorPresheafStalk` and the fact that sheafification does not
      change stalks);
   4. under these isomorphisms `δ_x` corresponds to the canonical isomorphism of commutative algebra
      `TensorProduct.AlgebraTensorModule.distribBaseChange`:
      `S ⊗_R (M_y ⊗_R N_y) ≅ (S ⊗_R M_y) ⊗_S (S ⊗_R N_y)`,
      checked on generators `s ⊗ (m ⊗ n)` with the section characterization
      `homEquiv_pullbackTensorObjHom_tensorSections`. -/

section PullbackTensorStalk

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

variable {X Y : AlgebraicGeometry.Scheme.{u}}

attribute [local instance] AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra

/-- The **untransposed** form of the section characterization
`homEquiv_pullbackTensorObjHom_tensorSections`: `δ` itself sends `η_{M⊗N}(m ⊗ n)` to
`η_M m ⊗ η_N n` on `f⁻¹U`. -/
theorem pullbackTensorObjHom_app_unit_tensorSections (f : X ⟶ Y) (M N : Y.Modules)
    (U : Y.Opens) (m : M.val.obj (Opposite.op U)) (n : N.val.obj (Opposite.op U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N).app (f ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (CategoryTheory.MonoidalCategoryStruct.tensorObj M N)).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections M N U m n)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n) := by
  have h := AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections f M N U m n
  rw [CategoryTheory.Adjunction.homEquiv_unit] at h
  exact h

/-- The target-side isomorphism `Θ` of the stalkwise comparison:
`S ⊗_R (M ⊗ N)_y ≅ (f^*M)_x ⊗_S (f^*N)_x`, assembled from Stacks 01CB, `distribBaseChange` and the
stalk formula for pullbacks. -/
def pullbackTensorStalkAux (f : X ⟶ Y) (M N : Y.Modules) (x : X) :
    (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f.base x)]
        (CategoryTheory.MonoidalCategoryStruct.tensorObj M N).presheaf.stalk (f.base x))
      ≃ₗ[X.presheaf.stalk x]
      (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.stalk x
        ⊗[X.presheaf.stalk x]
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).presheaf.stalk x) :=
  TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (X.presheaf.stalk x) (X.presheaf.stalk x))
      (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv M N (f.base x)) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.distribBaseChange (Y.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) (M.presheaf.stalk (f.base x)) (N.presheaf.stalk (f.base x)) ≪≫ₗ
    TensorProduct.congr (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f M x)
      (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f N x)

theorem pullbackTensorStalkAux_apply (f : X ⟶ Y) (M N : Y.Modules) (x : X)
    (u : X.presheaf.stalk x ⊗[Y.presheaf.stalk (f.base x)]
      (CategoryTheory.MonoidalCategoryStruct.tensorObj M N).presheaf.stalk (f.base x)) :
    pullbackTensorStalkAux f M N x u =
      TensorProduct.congr (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f M x)
        (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f N x)
        (TensorProduct.AlgebraTensorModule.distribBaseChange (Y.presheaf.stalk (f.base x))
          (X.presheaf.stalk x) (M.presheaf.stalk (f.base x)) (N.presheaf.stalk (f.base x))
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl (X.presheaf.stalk x) (X.presheaf.stalk x))
            (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv M N (f.base x)) u)) := rfl

/-- **The comparison square for `δ` on stalks**: through the stalk formula for pullbacks and
Stacks 01CB, `δ_x` is `distribBaseChange`. -/
theorem tensorStalkEquiv_stalkMap_pullbackTensorObjHom (f : X ⟶ Y) (M N : Y.Modules) (x : X)
    (u : X.presheaf.stalk x ⊗[Y.presheaf.stalk (f.base x)]
      (CategoryTheory.MonoidalCategoryStruct.tensorObj M N).presheaf.stalk (f.base x)) :
    AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)
          (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
            (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x u)) =
      pullbackTensorStalkAux f M N x u := by
  have hgerm : ∀ (P : Y.Modules) (U : Y.Opens) (hx : f.base x ∈ U) (p : P.val.obj (Opposite.op U)),
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f P x ((P.presheaf.germ U (f.base x) hx) p) =
        (((AlgebraicGeometry.Scheme.Modules.pullback f).obj P).presheaf.germ (f ⁻¹ᵁ U) x hx)
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).app U p) :=
    fun P U hx p => AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ f P x U hx p
  have hQ : ∀ (P : Y.Modules) (U : Y.Opens) (hx : f.base x ∈ U) (p : P.val.obj (Opposite.op U)),
      MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f P x
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
            ((P.presheaf.germ U (f.base x) hx) p)) =
        (((AlgebraicGeometry.Scheme.Modules.pullback f).obj P).presheaf.germ (f ⁻¹ᵁ U) x hx)
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).app U p) := by
    intro P U hx p
    have h1 : MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f P x
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
          ((P.presheaf.germ U (f.base x) hx) p)) =
        (1 : X.presheaf.stalk x) • AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f P x
          ((P.presheaf.germ U (f.base x) hx) p) := rfl
    rw [h1, one_smul, hgerm P U hx p]
  -- step 1: the case `s = 1`, by induction on elements of `M_y ⊗_R N_y`
  have main : ∀ v : M.presheaf.stalk (f.base x) ⊗[Y.presheaf.stalk (f.base x)]
        N.presheaf.stalk (f.base x),
      AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) x
          (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
            (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)
            (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f
              (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x
              ((AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv M N (f.base x)).symm v))) =
        TensorProduct.congr (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f M x)
          (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f N x)
          (TensorProduct.AlgebraTensorModule.distribBaseChange (Y.presheaf.stalk (f.base x))
            (X.presheaf.stalk x) (M.presheaf.stalk (f.base x)) (N.presheaf.stalk (f.base x))
            ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)] v)) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add v w hv hw =>
        rw [TensorProduct.tmul_add]
        simp only [map_add]
        rw [hv, hw]
    | tmul m n =>
        obtain ⟨U, hx, a, b, ha, hb⟩ :=
          AlgebraicGeometry.Scheme.Modules.exists_germ_pair M N (f.base x) m n
        subst ha
        subst hb
        have hsymm : (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv M N (f.base x)).symm
            ((M.presheaf.germ U (f.base x) hx) a ⊗ₜ[Y.presheaf.stalk (f.base x)]
              (N.presheaf.germ U (f.base x) hx) b) =
            ((CategoryTheory.MonoidalCategoryStruct.tensorObj M N).presheaf.germ U (f.base x) hx)
              (AlgebraicGeometry.Scheme.Modules.tensorSections M N U a b) :=
          (LinearEquiv.symm_apply_eq _).mpr
            (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv_germ_tensorSections
              M N (f.base x) U hx a b).symm
        rw [hsymm, hgerm, AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ,
          pullbackTensorObjHom_app_unit_tensorSections,
          AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv_germ_tensorSections,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
          hQ, hQ]
  -- step 2: induction on elements of `S ⊗_R (M ⊗ N)_y`
  rw [pullbackTensorStalkAux_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u w hu hw =>
      simp only [map_add]
      rw [hu, hw]
  | tmul s w =>
      have hs : s ⊗ₜ[Y.presheaf.stalk (f.base x)] w
          = s • ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)] w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hone : MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
          (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)] w) =
          AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f
            (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x w := by
        have h1 : MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
            (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x
            ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)] w) =
            (1 : X.presheaf.stalk x) • AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f
              (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x w := rfl
        rw [h1, one_smul]
      have hmain := main ((AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv M N (f.base x)) w)
      rw [LinearEquiv.symm_apply_apply] at hmain
      rw [hs]
      simp only [_root_.map_smul]
      rw [hone, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
      exact congrArg (fun t => s • t) hmain

/-- **`δ` is bijective on every stalk** (the stalkwise proof of Stacks 01CD). -/
theorem pullbackTensorObjHom_stalk_bijective (f : X ⟶ Y) (M N : Y.Modules) (x : X) :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)) := by
  have hcomp : ∀ z, AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) x
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N) z) =
      pullbackTensorStalkAux f M N x
        ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
          (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x).symm z) := by
    intro z
    have hu := tensorStalkEquiv_stalkMap_pullbackTensorObjHom f M N x
      ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
        (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x).symm z)
    rw [LinearEquiv.apply_symm_apply] at hu
    exact hu
  have hfun : ⇑(AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)) =
      ⇑(AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) x).symm ∘
        (⇑(pullbackTensorStalkAux f M N x) ∘
          ⇑(MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
            (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x).symm) := by
    funext z
    simp only [Function.comp_apply]
    rw [← hcomp z, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) x).symm.bijective.comp
    ((pullbackTensorStalkAux f M N x).bijective.comp
      (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv f
        (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) x).symm.bijective)

end AlgebraicGeometry.Scheme.Modules

end PullbackTensorStalk

/-- **The comparison morphism is an isomorphism (Stacks 01CD)**, for arbitrary `O_Y`-modules `M`, `N`
(no quasi-coherence, finite presentation, flatness or local freeness is needed).

Proof (the stalkwise proof of Stacks 01CD):
1. A morphism of sheaves of modules is an isomorphism iff the linear map on every stalk is
   bijective (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`). Fix `x ∈ X`, `y := f x`, and write
   `R := O_{Y,y}`, `S := O_{X,x}` (`AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra`).
2. **Stalks of pullbacks**: `(f^*H)_x ≅ S ⊗_R H_y`, induced by the adjunction unit `η_H` on stalks
   (`modulePullbackStalkTensorEquiv`).
3. **Stalks of tensor products (Stacks 01CB)**: `(A ⊗ B)_x ≅ A_x ⊗_{O_x} B_x`, sending the germ of
   the pairing `tensorSections A B U a b` to `a_x ⊗ b_x` (`tensorStalkEquiv`: sheafification does
   not change stalks, and filtered colimits commute with tensor products,
   `AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv`).
4. By 2 and 3, the source of `δ_x` is `S ⊗_R (M_y ⊗_R N_y)` and the target is
   `(S ⊗_R M_y) ⊗_S (S ⊗_R N_y)`. The untransposed section characterization
   `pullbackTensorObjHom_app_unit_tensorSections` says that `δ` sends `η_{M⊗N}(m ⊗ n)` to
   `η_M m ⊗ η_N n`, so on generators `δ_x` is `s ⊗ (m ⊗ n) ↦ (s ⊗ m) ⊗ (1 ⊗ n)`, i.e.
   `TensorProduct.AlgebraTensorModule.distribBaseChange`; two tensor product inductions (first on
   `M_y ⊗_R N_y`, then on `S ⊗_R (M⊗N)_y`) reduce the check to pure tensors, with common
   neighbourhood representatives of generators supplied by
   `AlgebraicGeometry.Scheme.Modules.modulePresheafStalk_exists_pair`. Hence `δ_x` is a composite of three bijections
   (`pullbackTensorObjHom_stalk_bijective`).

Special cases with shorter proofs: open immersions (`ModulesRestrictMonoidal.pullbackTensorObjIsoOpen`);
the unit case `IsIso (pullbackTensorObjHom f (𝟙_ _) P)` also follows from the oplax left unitality
and `pullback_η_isIso`. -/
instance AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_isIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N) :=
  (AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)).mpr
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_stalk_bijective f M N)

noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) :=
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N)

/-- `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` (Stacks 01CD), written with `Modules.tensor`: both ends are converted
to the monoidal structure via the canonical isomorphism `Modules.tensor ≅ ⊗`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.tensor M N) ≅
      AlgebraicGeometry.Scheme.Modules.tensor ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) :=
  (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

/- The instance `Scheme.Modules.opensMap_final` (`Opens.map f.base` is final) and the isomorphism
   `Scheme.Modules.pullbackUnitIso : f^*O_Y ≅ O_X` (`= asIso (SheafOfModules.pullbackObjUnitToUnit)`)
   come from `PullbackUnit.lean`. -/

/- The monoidal functor structure (tensor and unit isomorphisms compatible with associators and
   unitors), compatible with the symmetric structure (the "canonical, natural" of Stacks 01CD):
   the strong monoidal structure is obtained from the oplax structure `pullbackOplaxMonoidal` and
   the invertibility of `η`, `δ` via Mathlib's `Functor.Monoidal.ofOplaxMonoidal` (so its
   `toOplaxMonoidal` is definitionally `pullbackOplaxMonoidal`; no instance diamond); `η` is an
   isomorphism by `pullback_η` + `pullbackUnitIso`, and `δ` by `pullbackTensorObjHom_isIso`. The
   statements below keep their names; each proof is a one-line reference. -/

section Coherence

open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- The `η` of the oplax structure is Mathlib's `pullbackObjUnitToUnit` (`= pullbackUnitIso.hom`):
take adjoint transposes and use `pushforwardLaxMonoidal_ε`. -/
theorem pullback_η (f : X ⟶ Y) :
    CategoryTheory.Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f)
        (self := pullbackOplaxMonoidal f) =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom :=
  congrArg ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (pushforwardLaxMonoidal_ε f)

theorem pullback_η_isIso (f : X ⟶ Y) :
    CategoryTheory.IsIso (CategoryTheory.Functor.OplaxMonoidal.η
      (AlgebraicGeometry.Scheme.Modules.pullback f) (self := pullbackOplaxMonoidal f)) := by
  rw [pullback_η]
  exact CategoryTheory.Iso.isIso_hom _

/-- The pullback of sheaves of modules is a strong monoidal functor. -/
noncomputable instance pullbackMonoidal (f : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).Monoidal :=
  haveI := pullback_η_isIso f
  haveI : ∀ M N : Y.Modules, CategoryTheory.IsIso (CategoryTheory.Functor.OplaxMonoidal.δ
      (AlgebraicGeometry.Scheme.Modules.pullback f) (self := pullbackOplaxMonoidal f) M N) :=
    fun M N => pullbackTensorObjHom_isIso f M N
  CategoryTheory.Functor.Monoidal.ofOplaxMonoidal _

/-- The `μ` of the strong monoidal structure is the inverse of `pullbackTensorObjIso`. -/
theorem pullback_μ_eq (f : X ⟶ Y) (M N : Y.Modules) :
    CategoryTheory.Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback f) M N =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N).inv := rfl

/-- The `ε` of the strong monoidal structure is the inverse of `pullbackUnitIso`. -/
theorem pullback_ε_eq (f : X ⟶ Y) :
    CategoryTheory.Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback f) =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).inv := by
  exact (Iso.hom_comp_eq_id _).mp
    ((congrArg (· ≫ CategoryTheory.Functor.LaxMonoidal.ε
        (AlgebraicGeometry.Scheme.Modules.pullback f)) (pullback_η f).symm).trans
      (CategoryTheory.Functor.Monoidal.η_ε _))

/-- `μ = δ⁻¹` is natural in the left variable (directly from `μ_natural_left` of the strong monoidal
structure). -/
theorem pullback_μ_natural_left (f : X ⟶ Y) {M M' : Y.Modules} (φ : M ⟶ M') (N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map φ ▷
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj N ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M' N).inv =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (φ ▷ N) :=
  CategoryTheory.Functor.LaxMonoidal.μ_natural_left (AlgebraicGeometry.Scheme.Modules.pullback f) φ N

/-- `μ = δ⁻¹` is natural in the right variable (`μ_natural_right`). -/
theorem pullback_μ_natural_right (f : X ⟶ Y) (M : Y.Modules) {N N' : Y.Modules} (ψ : N ⟶ N') :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ◁
        (AlgebraicGeometry.Scheme.Modules.pullback f).map ψ ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N').inv =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (M ◁ ψ) :=
  CategoryTheory.Functor.LaxMonoidal.μ_natural_right (AlgebraicGeometry.Scheme.Modules.pullback f) M ψ

/-- `μ` is compatible with the associators (`LaxMonoidal.associativity`). -/
theorem pullback_μ_associativity (f : X ⟶ Y) (M N P : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N).inv ▷
          (AlgebraicGeometry.Scheme.Modules.pullback f).obj P ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f (M ⊗ N) P).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (α_ M N P).hom =
      (α_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
            ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)
            ((AlgebraicGeometry.Scheme.Modules.pullback f).obj P)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ◁
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f N P).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M (N ⊗ P)).inv :=
  CategoryTheory.Functor.LaxMonoidal.associativity (AlgebraicGeometry.Scheme.Modules.pullback f) M N P

/-- `ε`, `μ` are compatible with the left unitors (`LaxMonoidal.left_unitality` + `pullback_ε_eq`). -/
theorem pullback_left_unitality (f : X ⟶ Y) (M : Y.Modules) :
    (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).inv ▷
          (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f
          (𝟙_ Y.Modules) M).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (λ_ M).hom := by
  rw [← pullback_ε_eq]
  exact CategoryTheory.Functor.LaxMonoidal.left_unitality (AlgebraicGeometry.Scheme.Modules.pullback f) M

/-- `ε`, `μ` are compatible with the right unitors (`LaxMonoidal.right_unitality` + `pullback_ε_eq`). -/
theorem pullback_right_unitality (f : X ⟶ Y) (M : Y.Modules) :
    (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ◁
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f
          M (𝟙_ Y.Modules)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (ρ_ M).hom := by
  rw [← pullback_ε_eq]
  exact CategoryTheory.Functor.LaxMonoidal.right_unitality (AlgebraicGeometry.Scheme.Modules.pullback f) M

/-- `μ` is compatible with the braiding (`Functor.LaxBraided.braided`): the inverse form of
`pullbackTensorObjHom_braiding`. -/
theorem pullback_braided (f : X ⟶ Y) (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f M N).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (β_ M N).hom =
      (β_ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso f N M).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (pullbackTensorObjHom_braiding f M N).symm

end AlgebraicGeometry.Scheme.Modules

noncomputable instance {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).Braided where
  braided := AlgebraicGeometry.Scheme.Modules.pullback_braided f

end Coherence

end
