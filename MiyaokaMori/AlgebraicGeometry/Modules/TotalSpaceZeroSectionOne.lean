import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSectionData

/-! # The augmentation sends the unit to the unit

Statement: `symAugmentation` sends the unit section of the total symmetric algebra to the unit section
of the structure sheaf.
Proof:
1. Unfold `total.one`; its only nonzero component is in degree zero;
2. use the identity property of `symAugmentationZero` on the degree-zero component;
3. simplify to `1` with the section formula for the unit of `pushforwardId`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory
noncomputable section

/-- On the graded piece `0`, the augmentation composed with the unit is the identity: in the
quasi-coherent branch by `symPowπ_desc` (quotient map ≫ descent = the original morphism, here `𝟙`),
in the trivial branch by definition `𝟙 ≫ 𝟙 = 𝟙`. -/
theorem AlgebraicGeometry.Scheme.Modules.one_comp_symAugmentationZero
    {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).one ≫
      AlgebraicGeometry.Scheme.Modules.symAugmentationZero W = 𝟙 _ := by
  unfold AlgebraicGeometry.Scheme.Modules.symAugmentationZero
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
  -- `Decidable.casesOn` with a constant motive is `dite` by definition
  show (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
      (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
      (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)).one ≫
    id (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _) _ _) = 𝟙 _
  by_cases h : SheafOfModules.IsQuasicoherent W
  · have hS : (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)) =
        AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h := dif_pos h
    simp only [dif_pos h]
    -- proof irrelevance: replace `_proof_2` by the explicit `congrArg _ hS`
    show (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)).one ≫
      id ((congrArg (fun T : X.GradedQCAlgebra => (T.part 0 ⟶ 𝟙_ X.Modules)) hS).mpr
        (AlgebraicGeometry.Scheme.Modules.symPowDesc W 0 (𝟙 _) (fun i => i.elim0))) = 𝟙 _
    revert hS
    generalize (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)) = S
    intro hS
    subst hS
    exact AlgebraicGeometry.Scheme.Modules.symPowπ_desc W 0 (𝟙 _) (fun i => i.elim0)
  · have hS : (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)) =
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X := dif_neg h
    simp only [dif_neg h]
    show (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)).one ≫
      id ((congrArg (fun T : X.GradedQCAlgebra => (T.part 0 ⟶ 𝟙_ X.Modules)) hS).mpr
        (𝟙 ((AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X).part 0))) = 𝟙 _
    revert hS
    generalize (@dite _ (SheafOfModules.IsQuasicoherent W) (Classical.propDecidable _)
        (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC W h)
        (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)) = S
    intro hS
    subst hS
    exact Category.id_comp _

/-- The unit of the total algebra composed with the augmentation is the identity of `𝟙_`:
`total.one = S.one ≫ Sigma.ι 0`, `Sigma.ι 0 ≫ Sigma.desc = symAugmentationZero`, then
`one_comp_symAugmentationZero`. -/
theorem AlgebraicGeometry.Scheme.Modules.total_one_comp_symAugmentation
    {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.one ≫
      AlgebraicGeometry.Scheme.Modules.symAugmentation W = 𝟙 _ := by
  show ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).one ≫
      CategoryTheory.Limits.Sigma.ι _ 0) ≫ CategoryTheory.Limits.Sigma.desc _ = 𝟙 _
  rw [Category.assoc, CategoryTheory.Limits.Sigma.ι_desc]
  exact AlgebraicGeometry.Scheme.Modules.one_comp_symAugmentationZero W

theorem AlgebraicGeometry.Scheme.Modules.symAugmentation_one {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) (U : X.Opens) :
    (show Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ U) from
      (AlgebraicGeometry.Scheme.Modules.symAugmentation W ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app
          (SheafOfModules.unit X.ringCatSheaf)).app U
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.one.app U
          (show Γ(X, U) from 1))) = 1 := by
  have h := congrArg (fun f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules =>
      (AlgebraicGeometry.Scheme.Modules.Hom.app f U) (show Γ(X, U) from 1))
    (AlgebraicGeometry.Scheme.Modules.total_one_comp_symAugmentation W)
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h ⊢
  exact h

end
