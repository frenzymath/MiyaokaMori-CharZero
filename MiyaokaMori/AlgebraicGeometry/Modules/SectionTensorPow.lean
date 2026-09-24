import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne

/-! # Tensor powers of a section and the recursive maps on them

For `t ∈ Γ(W, M)` we define `t^{⊗m} ∈ Γ(W, M^{⊗m})` (`sectionPow`, right-recursive like `monoidalPow`:
`t^{⊗0} = 1`, `t^{⊗(m+1)} = t^{⊗m} ⊗ t`) and compute the four recursive morphisms of
`relativeProj.liftLocalHomAux` on it:
* restriction: `(t^{⊗m})|_{W'} = (t|_{W'})^{⊗m}` (`sectionPow_res`);
* `monoidalPowMap φ m (t^{⊗m}) = (φ t)^{⊗m}` (`monoidalPowMap_app_sectionPow`);
* `unitPowCollapse X m (1^{⊗m}) = 1` (`unitPowCollapse_app_sectionPow_one`);
* `pullbackMonoidalPow f N m (η(t^{⊗m})) = (η t)^{⊗m}`, `η` the unit of `f^* ⊣ f_*`
  (`pullbackMonoidalPow_app_unitSec_sectionPow`).
All proofs are inductions on `m` using the section formulas `tensorHom_tensorSections`,
`leftUnitor_app_tensorSections`, `pullbackTensorObjHom_app_unit_tensorSections`, `tensorSections_restrict`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `t^{⊗m} ∈ Γ(W, M^{⊗m})`: `t^{⊗0} = 1`, `t^{⊗(m+1)} = t^{⊗m} ⊗ t`. -/
noncomputable def sectionPow (M : X.Modules) (W : X.Opens) (t : Γ(M, W)) :
    ∀ m : ℕ, Γ(monoidalPow M m, W)
  | 0 => (1 : Γ(X, W))
  | m + 1 => tensorSections (monoidalPow M m) M W (sectionPow M W t m) t

theorem sectionPow_zero (M : X.Modules) (W : X.Opens) (t : Γ(M, W)) :
    sectionPow M W t 0 = (1 : Γ(X, W)) := rfl

theorem sectionPow_succ (M : X.Modules) (W : X.Opens) (t : Γ(M, W)) (m : ℕ) :
    sectionPow M W t (m + 1) = tensorSections (monoidalPow M m) M W (sectionPow M W t m) t := rfl

/-- Restriction of a tensor power. -/
theorem sectionPow_res (M : X.Modules) {W W' : X.Opens} (h : W' ≤ W) (t : Γ(M, W)) :
    ∀ m : ℕ, (monoidalPow M m).presheaf.map (homOfLE h).op (sectionPow M W t m) =
      sectionPow M W' (M.presheaf.map (homOfLE h).op t) m
  | 0 => by
    show X.presheaf.map (homOfLE h).op (1 : Γ(X, W)) = (1 : Γ(X, W'))
    exact map_one (X.presheaf.map (homOfLE h).op).hom
  | m + 1 => by
    show (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) (monoidalPow M m) M).presheaf.map
        (homOfLE h).op (tensorSections (monoidalPow M m) M W (sectionPow M W t m) t) =
      tensorSections (monoidalPow M m) M W' (sectionPow M W' (M.presheaf.map (homOfLE h).op t) m)
        (M.presheaf.map (homOfLE h).op t)
    refine (tensorSections_restrict (monoidalPow M m) M (homOfLE h) (sectionPow M W t m) t).trans ?_
    exact congrArg (fun z => tensorSections (monoidalPow M m) M W' z (M.presheaf.map (homOfLE h).op t))
      (sectionPow_res M h t m)

/-- `(φ ⊗ ψ)(a ⊗ b) = φ a ⊗ ψ b`, `Hom.app` spelling. -/
private theorem tensorHom_app_tensorSections_sp {A B A' B' : X.Modules} (φ : A ⟶ A') (ψ : B ⟶ B')
    (W : X.Opens) (a : Γ(A, W)) (b : Γ(B, W)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) φ ψ).app W
        (tensorSections A B W a b) =
      tensorSections A' B' W (φ.app W a) (ψ.app W b) :=
  tensorHom_tensorSections φ ψ W a b

private theorem whiskerRight_app_tensorSections_sp {A A' : X.Modules} (φ : A ⟶ A') (B : X.Modules)
    (W : X.Opens) (a : Γ(A, W)) (b : Γ(B, W)) :
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) φ B).app W
        (tensorSections A B W a b) =
      tensorSections A' B W (φ.app W a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact tensorHom_app_tensorSections_sp φ (𝟙 B) W a b

/-- `monoidalPowMap φ m` on tensor powers: `(φ t)^{⊗m}`. -/
theorem monoidalPowMap_app_sectionPow {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (t : Γ(M, W)) :
    ∀ m : ℕ, (monoidalPowMap φ m).app W (sectionPow M W t m) = sectionPow N W (φ.app W t) m
  | 0 => rfl
  | m + 1 => by
    show (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) (monoidalPowMap φ m) φ).app W
        (tensorSections (monoidalPow M m) M W (sectionPow M W t m) t) =
      tensorSections (monoidalPow N m) N W (sectionPow N W (φ.app W t) m) (φ.app W t)
    rw [tensorHom_app_tensorSections_sp, monoidalPowMap_app_sectionPow φ W t m]

/-- `unitPowCollapse X m` sends `1^{⊗m}` to `1`. -/
theorem unitPowCollapse_app_sectionPow_one (W : X.Opens) :
    ∀ m : ℕ, (unitPowCollapse X m).app W
      (sectionPow (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) W (1 : Γ(X, W)) m) =
      (1 : Γ(X, W))
  | 0 => rfl
  | m + 1 => by
    show (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) (unitPowCollapse X m)
          (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) ≫
        (CategoryTheory.MonoidalCategoryStruct.leftUnitor
          (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules)).hom).app W
        (tensorSections (monoidalPow (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) m)
          (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) W
          (sectionPow (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) W (1 : Γ(X, W)) m)
          (1 : Γ(X, W))) = (1 : Γ(X, W))
    rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tensorSections_sp,
      unitPowCollapse_app_sectionPow_one W m]
    exact (leftUnitor_app_tensorSections (𝟙_ X.Modules) W (1 : Γ(X, W)) (1 : Γ(X, W))).trans (one_smul _ _)

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- `f^*O_X ≅ O_Y` sends `η(1)` to `1` over `f⁻¹W` (adjoint transpose is `f^♯`, which is a ring map). -/
theorem pullbackUnitIso_hom_app_unitSec_one (f : Y ⟶ X) (W : X.Opens) :
    (pullbackUnitIso f).hom.app (f ⁻¹ᵁ W)
        (MiyaokaMori.DualPullback.unitSec f (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, W))) =
      (1 : Γ(Y, f ⁻¹ᵁ W)) := by
  have h1 : ((pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom).app W
      (1 : Γ(X, W)) = (1 : Γ(Y, f ⁻¹ᵁ W)) := by
    rw [homEquiv_pullbackUnitIso_hom_pbup]
    exact map_one (f.app W).hom
  have h2 : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      (pullbackPushforwardAdjunction f).unit.app _ ≫ (pushforward f).map (pullbackUnitIso f).hom :=
    Adjunction.homEquiv_unit (pullbackPushforwardAdjunction f) _ _ (pullbackUnitIso f).hom
  have h3 := congrArg (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) => Hom.app k W (1 : Γ(X, W))) h2
  exact h3.symm.trans h1

/-- The comparison `f^*(N^{⊗m}) → (f^*N)^{⊗m}` on the pullback of a tensor power of sections. -/
theorem pullbackMonoidalPow_app_unitSec_sectionPow (f : Y ⟶ X) (N : X.Modules) (W : X.Opens)
    (t : Γ(N, W)) :
    ∀ m : ℕ, (pullbackMonoidalPow f N m).app (f ⁻¹ᵁ W)
        (MiyaokaMori.DualPullback.unitSec f (monoidalPow N m) (sectionPow N W t m)) =
      sectionPow ((pullback f).obj N) (f ⁻¹ᵁ W) (MiyaokaMori.DualPullback.unitSec f N t) m
  | 0 => pullbackUnitIso_hom_app_unitSec_one f W
  | m + 1 => by
    show (pullbackTensorObjHom f (monoidalPow N m) N ≫
        CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := Y.Modules)
          (pullbackMonoidalPow f N m) ((pullback f).obj N)).app (f ⁻¹ᵁ W)
        (((pullbackPushforwardAdjunction f).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (monoidalPow N m) N)).app W
          (tensorSections (monoidalPow N m) N W (sectionPow N W t m) t)) =
      tensorSections (monoidalPow ((pullback f).obj N) m) ((pullback f).obj N) (f ⁻¹ᵁ W)
        (sectionPow ((pullback f).obj N) (f ⁻¹ᵁ W) (MiyaokaMori.DualPullback.unitSec f N t) m)
        (MiyaokaMori.DualPullback.unitSec f N t)
    rw [Hom.comp_app, ConcreteCategory.comp_apply, pullbackTensorObjHom_app_unit_tensorSections,
      whiskerRight_app_tensorSections_sp]
    exact congrArg (fun z => tensorSections (monoidalPow ((pullback f).obj N) m) ((pullback f).obj N)
      (f ⁻¹ᵁ W) z (MiyaokaMori.DualPullback.unitSec f N t))
      (pullbackMonoidalPow_app_unitSec_sectionPow f N W t m)

end AlgebraicGeometry.Scheme.Modules

end
