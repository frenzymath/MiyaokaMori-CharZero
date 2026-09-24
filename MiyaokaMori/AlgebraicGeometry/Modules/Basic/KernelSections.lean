import MiyaokaMori.Prelude

/-! # Sections of the kernel of a morphism of sheaves of modules

The kernel `kernel f` of a morphism of sheaves of modules `f : M ⟶ N`, on sections over each open, is the
kernel of the map on sections:
* `kernel_ι_app_injective`: `(kernel.ι f).val.app (op U)` is injective;
* `kernel_ι_app_apply_eq_zero`: sections of the kernel are sent to `0` by `f` (`kernel.condition` on sections);
* `exists_kernel_ι_app_eq`: `f(y) = 0 ⇒ y` comes from `(ker f)(U)` (the sections functor preserves kernels).

Reference: Stacks 01AH (kernels in the abelian category of sheaves are computed on sections;
`SheafOfModules.forget` is a right adjoint hence preserves limits, and `PresheafOfModules.evaluation`
preserves limits).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}} {M N : Y.Modules} (f : M ⟶ N) (U : Y.Opens)

/-- `kernel.ι f` is injective on every open: `kernel.ι` is a monomorphism of sheaves (`equalizer.ι_mono`),
the forgetful functor to presheaves preserves limits hence monomorphisms, and monomorphisms of presheaves
are objectwise injective (`PresheafOfModules.injective_of_mono`). -/
theorem kernel_ι_app_injective :
    Function.Injective ((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom := by
  have hmono : CategoryTheory.Mono (CategoryTheory.Limits.kernel.ι f) :=
    CategoryTheory.Limits.equalizer.ι_mono
  have : CategoryTheory.Mono (CategoryTheory.Limits.kernel.ι f).val :=
    @CategoryTheory.Functor.map_mono _ _ _ _ (SheafOfModules.forget _) inferInstance _ _
      (CategoryTheory.Limits.kernel.ι f) hmono
  intro a b hab
  exact PresheafOfModules.injective_of_mono (CategoryTheory.Limits.kernel.ι f).val (Opposite.op U) hab

/-- Sections of the kernel are sent to `0` by `f` (`kernel.condition` on sections). -/
theorem kernel_ι_app_apply_eq_zero
    (x : ((CategoryTheory.Limits.kernel f).val.obj (Opposite.op U) : Type u)) :
    (f.val.app (Opposite.op U)).hom (((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom x) = 0 := by
  have h : CategoryTheory.Limits.kernel.ι f ≫ f = 0 := CategoryTheory.Limits.kernel.condition f
  exact congrArg (fun g : CategoryTheory.Limits.kernel f ⟶ N => (g.val.app (Opposite.op U)).hom x) h

/-- `f(y) = 0 ⇒ y` comes from `(ker f)(U)`: the sections functor `SheafOfModules.evaluation` preserves
kernels (`PreservesKernel.iso`), and kernels in `ModuleCat` are `LinearMap.ker` (`ModuleCat.kernelIsoKer`). -/
theorem exists_kernel_ι_app_eq (y : (M.val.obj (Opposite.op U) : Type u))
    (hy : (f.val.app (Opposite.op U)).hom y = 0) :
    ∃ x : ((CategoryTheory.Limits.kernel f).val.obj (Opposite.op U) : Type u),
      ((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom x = y := by
  have hGa : (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).Additive :=
    inferInstanceAs (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (Opposite.op U)).Additive
  have hGf : ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f).hom y = 0 := hy
  let z : ((CategoryTheory.Limits.kernel
      ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) : ModuleCat.{u} Γ(Y, U)) : Type u) :=
    (ModuleCat.kernelIsoKer ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f)).inv.hom ⟨y, hGf⟩
  refine ⟨(CategoryTheory.Limits.PreservesKernel.iso
    (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)) f).inv.hom z, ?_⟩
  have h1 := congrArg (fun φ : CategoryTheory.Limits.kernel
      ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) ⟶
      (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).obj M => φ.hom z)
    (CategoryTheory.Limits.PreservesKernel.iso_inv_ι (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)) f)
  have h3 := ModuleCat.kernelIsoKer_inv_kernel_ι_apply
    ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) ⟨y, hGf⟩
  simp only [ModuleCat.hom_comp] at h1
  exact h1.trans h3

/-- The image of the sections of the kernel is exactly the kernel of the map on sections (the two
previous statements combined). -/
theorem range_kernel_ι_app :
    Set.range ((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom =
      {y | (f.val.app (Opposite.op U)).hom y = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact kernel_ι_app_apply_eq_zero f U x
  · intro hy
    exact exists_kernel_ι_app_eq f U y hy

end AlgebraicGeometry.Scheme.Modules

end
