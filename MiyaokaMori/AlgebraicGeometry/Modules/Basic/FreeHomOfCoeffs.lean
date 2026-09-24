import MiyaokaMori.Prelude

/-! # Morphisms of free sheaves given by coefficients

A morphism of free sheaves defined by coefficients: given `c : I → (J →₀ Γ(X, O_X))`, we get
`O_X^{(I)} → O_X^{(J)}` sending the `i`-th basis element to `Σ_j c_i(j)·e_j` (a finite sum). Used to
write transition morphisms between free sheaves from the coefficients of transition matrices /
substituted polynomials.

Standard construction (the linear map between free modules given by a coefficient matrix, evaluated
open by open).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The morphism between free sheaves given by coefficients: `ιFree i ↦ Σ_j c_i(j) · ιFree j` (`c_i` finitely
   supported, the coefficients being global functions). On each open `U` write the section
   `Σ_j c_i(j)|_U · (section of ιFree j)|_U`; the morphism is obtained through `freeHomEquiv`;
   compatibility of the family of sections with restriction is a proof obligation. -/

/-- The section over the open `U` of the image of the `i`-th generator: `Σ_j c_i(j)|_U · (section of ιFree j)|_U`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type u} (c : J →₀ Γ(X, ⊤)) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf) J).val.obj U :=
  @Finsupp.sum J Γ(X, ⊤) ((SheafOfModules.free (R := X.ringCatSheaf) J).val.obj U) _ _ c
    fun j a =>
      @HSMul.hSMul (X.ringCatSheaf.val.obj U) ((SheafOfModules.free (R := X.ringCatSheaf) J).val.obj U)
        ((SheafOfModules.free (R := X.ringCatSheaf) J).val.obj U) _
        (X.presheaf.map (CategoryTheory.homOfLE le_top : U.unop ⟶ ⊤).op a)
        ((SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree (R := X.ringCatSheaf) j)).val U)

/-- The family of sections is compatible with restriction: restriction maps are semilinear
(`map_finsuppSum` + `PresheafOfModules.map_smul`), the two restrictions of the coefficients (first to `U`,
then to `V`) merge into one by functoriality of `X.presheaf` (morphisms in `Opens` form a subsingleton,
`Subsingleton.elim`), and the family of sections of `ιFree j` is itself compatible with restriction (it is
an element of `sections`: `(unitHomEquiv _ (ιFree j)).property f`). -/
theorem AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily_compat {X : AlgebraicGeometry.Scheme.{u}}
    {J : Type u} (c : J →₀ Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily c ∈ ((SheafOfModules.free (R := X.ringCatSheaf) J).val.presheaf ⋙
      CategoryTheory.forget _).sections := by
  intro U V f
  unfold AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily
  change (SheafOfModules.free (R := X.ringCatSheaf) J).val.map f _ = _
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun j _ => ?_
  erw [PresheafOfModules.map_smul]
  congr 1
  · change X.presheaf.map f (X.presheaf.map (homOfLE le_top).op (c j)) =
      X.presheaf.map (homOfLE le_top).op (c j)
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    have e : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e]
  · exact (SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree j)).property f

noncomputable def AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs {X : AlgebraicGeometry.Scheme.{u}}
    {I J : Type u} (c : I → J →₀ Γ(X, ⊤)) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free (R := X.ringCatSheaf) J :=
  (SheafOfModules.freeHomEquiv _).symm fun i =>
    ⟨AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily (c i), AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs.sectionFamily_compat (c i)⟩

end
