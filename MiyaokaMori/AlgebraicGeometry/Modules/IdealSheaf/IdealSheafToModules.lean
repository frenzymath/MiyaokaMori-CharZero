import MiyaokaMori.Prelude

/-! # A quasi-coherent ideal sheaf as a sheaf of modules

A quasi-coherent ideal sheaf `I` viewed as an `O_X`-module: the kernel of `O_X → ι_*O_{V(I)}`
(where `ι : V(I) ↪ X`); its sections on an affine open `U` are the ideal `I(U)`.

Reference: Stacks 01WR (the ideal sheaf `I_D ⊂ O_S`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.toModules {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) : X.Modules :=
  CategoryTheory.Limits.kernel
    (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

/-- In `ModuleCat`, the range of `kernel.ι` is the kernel of the linear map. -/
private theorem range_kernel_ι_moduleCat {R : Type u} [Ring R] {A B : ModuleCat.{v} R}
    (f : A ⟶ B) : Set.range (kernel.ι f) = (LinearMap.ker f.hom : Set A) := by
  rw [← ModuleCat.kernelIsoKer_hom_ker_subtype f]
  ext x
  simp only [Set.mem_range, SetLike.mem_coe, ConcreteCategory.comp_apply,
    ModuleCat.hom_ofHom, Submodule.coe_subtype]
  constructor
  · rintro ⟨y, rfl⟩
    exact ((ModuleCat.kernelIsoKer f).hom y).2
  · intro hx
    obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
      (ModuleCat.kernelIsoKer f).hom).2 ⟨x, hx⟩
    exact ⟨y, by rw [hy]⟩

/-- `SheafOfModules.evaluation` is an additive functor (both `forget` and
`PresheafOfModules.evaluation` are). Not registered as a global instance; used only in this file. -/
private theorem evaluationAdditive {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} (R : CategoryTheory.Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    (SheafOfModules.evaluation R U).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Kernels of sheaves of modules are computed sectionwise (`SheafOfModules.evaluation` preserves
finite limits), so the range of `kernel.ι` on `U` is the kernel of the map on `U`. -/
private theorem range_kernel_ι_val_app {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (U : Cᵒᵖ) :
    Set.range ((CategoryTheory.Limits.kernel.ι φ).val.app U)
      = (LinearMap.ker ((SheafOfModules.evaluation R U).map φ).hom :
          Set ((SheafOfModules.evaluation R U).obj M)) := by
  have := evaluationAdditive R U
  have key : ∀ y, kernel.ι ((SheafOfModules.evaluation R U).map φ) y
      = (SheafOfModules.evaluation R U).map (kernel.ι φ)
          ((PreservesKernel.iso (SheafOfModules.evaluation R U) φ).inv y) := by
    intro y
    rw [← PreservesKernel.iso_inv_ι (SheafOfModules.evaluation R U) φ]
    rfl
  have h1 : Set.range (((SheafOfModules.evaluation R U)).map (kernel.ι φ))
      = Set.range (kernel.ι (((SheafOfModules.evaluation R U)).map φ)) := by
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(PreservesKernel.iso (SheafOfModules.evaluation R U) φ).hom y, ?_⟩
      rw [key]
      congr 1
      exact congrArg (fun (m : _ ⟶ _) => (ConcreteCategory.hom m) y)
        (Iso.hom_inv_id (PreservesKernel.iso (SheafOfModules.evaluation R U) φ))
    · rintro ⟨y, rfl⟩
      exact ⟨(PreservesKernel.iso (SheafOfModules.evaluation R U) φ).inv y, (key y).symm⟩
  exact h1.trans (range_kernel_ι_moduleCat _)

/- Sections on an affine open: the range of `kernel.ι` on `U` is the ideal `I(U)`. -/

theorem AlgebraicGeometry.Scheme.IdealSheafData.range_toModules_ι_app {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range ((CategoryTheory.Limits.kernel.ι
        (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).val.app
          (Opposite.op (U : X.Opens))) = (I.ideal U : Set Γ(X, U)) := by
  rw [range_kernel_ι_val_app]
  ext x
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app I U]
  exact Iff.rfl

end
