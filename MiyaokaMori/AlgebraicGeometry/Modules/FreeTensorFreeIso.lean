import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The tensor product of two free modules is free

The tensor product of free sheaves of modules is free: `O^{(I)} ⊗ O^{(J)} ≅ O^{(I×J)}`, sending
`ιFree i ⊗ ιFree j` to `ιFree (i, j)`, compatibly with the associator, unitors and braiding (the
multiplication of the weighted polynomial algebra is given by this together with the index map
`(e, e′) ↦ e + e′`; locally the basis consists of monomials and the multiplication is monomial
multiplication).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The tensor product, tensor morphisms and left unitor are taken in the monoidal structure of
   `X.Modules`; we write `C := X.Modules` explicitly (`Scheme.Modules` is not an `abbrev`, so the
   instance is not found on `SheafOfModules X.ringCatSheaf`); the free sheaf is Mathlib's
   `SheafOfModules.free`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso {X : AlgebraicGeometry.Scheme.{u}}
    (I J : Type u) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        (SheafOfModules.free (R := X.ringCatSheaf) I) (SheafOfModules.free (R := X.ringCatSheaf) J) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (I × J) :=
  -- the inverse morphism written out: free (I × J) = ∐_{I×J} O, whose (i, j)-th component is
  -- O ≅ 𝟙_ ⊗ O --(ιFree i ⊗ ιFree j)--> free I ⊗ free J
  let φ : (SheafOfModules.free (R := X.ringCatSheaf) (I × J) : X.Modules) ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        (SheafOfModules.free (R := X.ringCatSheaf) I) (SheafOfModules.free (R := X.ringCatSheaf) J) :=
    CategoryTheory.Limits.Sigma.desc fun p : I × J =>
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules)
          (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
          (SheafOfModules.ιFree (R := X.ringCatSheaf) p.1) (SheafOfModules.ιFree (R := X.ringCatSheaf) p.2)
  -- φ is an isomorphism: − ⊗ free J and O ⊗ − preserve coproducts,
  -- so free I ⊗ free J is the coproduct of (I × J) copies of O ⊗ O ≅ O, whose injections are the components of φ
  haveI : CategoryTheory.IsIso φ := by
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let FI : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
    let FJ : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) J
    let ii : ∀ _ : I, O ⟶ FI := fun i => SheafOfModules.ιFree (R := X.ringCatSheaf) i
    let jj : ∀ _ : J, O ⟶ FJ := fun j => SheafOfModules.ιFree (R := X.ringCatSheaf) j
    let lam : O ⟶ CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) O O :=
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) O).inv
    have hI : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk (f := fun _ : I => O) FI ii) :=
      CategoryTheory.Limits.coproductIsCoproduct (fun _ : I => O)
    have hJ : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk (f := fun _ : J => O) FJ jj) :=
      CategoryTheory.Limits.coproductIsCoproduct (fun _ : J => O)
    have h1 : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk
          (f := fun _ : I => CategoryTheory.MonoidalCategory.tensorObj O FJ)
          (CategoryTheory.MonoidalCategory.tensorObj FI FJ)
          (fun i => CategoryTheory.MonoidalCategory.whiskerRight (ii i) FJ)) :=
      CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv
        (CategoryTheory.MonoidalCategory.tensorRight FJ) _ _
        (CategoryTheory.Limits.isColimitOfPreserves
          (CategoryTheory.MonoidalCategory.tensorRight FJ) hI)
    have h2' : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk
          (f := fun _ : J => CategoryTheory.MonoidalCategory.tensorObj O O)
          (CategoryTheory.MonoidalCategory.tensorObj O FJ)
          (fun j => CategoryTheory.MonoidalCategory.whiskerLeft O (jj j))) :=
      CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv
        (CategoryTheory.MonoidalCategory.tensorLeft O) _ _
        (CategoryTheory.Limits.isColimitOfPreserves
          (CategoryTheory.MonoidalCategory.tensorLeft O) hJ)
    have h2 : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk (f := fun _ : J => O)
          (CategoryTheory.MonoidalCategory.tensorObj O FJ)
          (fun j => lam ≫ CategoryTheory.MonoidalCategory.whiskerLeft O (jj j))) :=
      CategoryTheory.Limits.cofanIsColimitOfObjIso _ h2' (fun _ =>
        CategoryTheory.Iso.mk lam
          (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) O).hom
          (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) O).inv_hom_id
          (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) O).hom_inv_id)
    have h3 : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk (f := fun _ : Σ _ : I, J => O)
          (CategoryTheory.MonoidalCategory.tensorObj FI FJ)
          (fun ab => (lam ≫ CategoryTheory.MonoidalCategory.whiskerLeft O (jj ab.2)) ≫
            CategoryTheory.MonoidalCategory.whiskerRight (ii ab.1) FJ)) :=
      CategoryTheory.Limits.Cofan.isColimitTrans _ h1
        (fun _ b => lam ≫ CategoryTheory.MonoidalCategory.whiskerLeft O (jj b)) (fun _ => h2)
    have h4 := (CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv
      (Equiv.sigmaEquivProd I J).symm _) h3
    have h5 : CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.Cofan.mk (f := fun _ : I × J => O)
          (CategoryTheory.MonoidalCategory.tensorObj FI FJ)
          (fun p => lam ≫ CategoryTheory.MonoidalCategory.tensorHom (ii p.1) (jj p.2))) :=
      CategoryTheory.Limits.IsColimit.ofIsoColimit h4
        (CategoryTheory.Limits.Cofan.ext (CategoryTheory.Iso.refl _) (by
          intro p
          simp only [CategoryTheory.Limits.Cofan.inj, CategoryTheory.Limits.Cofan.mk,
            CategoryTheory.Discrete.natTrans_app, CategoryTheory.Iso.refl_hom,
            CategoryTheory.Category.comp_id]
          rw [CategoryTheory.Category.assoc, ← CategoryTheory.MonoidalCategory.tensorHom_def']
          rfl))
    exact (CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨h5⟩
  (CategoryTheory.asIso φ).symm

/-- The inverse morphism is the `φ` of the definition (unfolding, `rfl`). -/
theorem AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso_inv
    {X : AlgebraicGeometry.Scheme.{u}} (I J : Type u) :
    (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).inv =
      CategoryTheory.Limits.Sigma.desc (fun p : I × J =>
        (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules)
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
            (SheafOfModules.ιFree (R := X.ringCatSheaf) p.1)
            (SheafOfModules.ιFree (R := X.ringCatSheaf) p.2)) :=
  rfl

theorem AlgebraicGeometry.Scheme.Modules.ιFree_tensor_ιFree_freeTensorFreeIso
    {X : AlgebraicGeometry.Scheme.{u}} {I J : Type u} (i : I) (j : J) :
    CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
        (SheafOfModules.ιFree (R := X.ringCatSheaf) i) (SheafOfModules.ιFree (R := X.ringCatSheaf) j) ≫
        (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso (X := X) I J).hom =
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules)
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.ιFree (R := X.ringCatSheaf) (i, j) := by
  refine (CategoryTheory.Iso.eq_comp_inv _).mp ?_
  rw [AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso_inv]
  have h := CategoryTheory.Limits.Sigma.ι_desc
    (f := fun _ : I × J => (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (fun p : I × J =>
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
          (SheafOfModules.ιFree (R := X.ringCatSheaf) p.1)
          (SheafOfModules.ιFree (R := X.ringCatSheaf) p.2)) (i, j)
  refine ((CategoryTheory.Category.assoc _ _ _).trans ?_).symm
  refine Eq.trans (congrArg (fun t =>
    (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules)
      (SheafOfModules.unit X.ringCatSheaf)).hom ≫ t) h) ?_
  exact CategoryTheory.Iso.hom_inv_id_assoc _ _

end
