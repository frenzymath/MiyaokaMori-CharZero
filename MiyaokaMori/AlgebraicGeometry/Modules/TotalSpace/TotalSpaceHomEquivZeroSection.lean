import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `0 ▷ M = 0` (the `X.Modules` version of `MonoidalPreadditive.zero_whiskerRight`). The same fact is
`Modules.zero_whiskerRight` (`ModulesMonoidalZero`), which cannot be imported together with `TotalSpaceZeroSectionMul`
(a global name clash); hence a **private** copy, proved via the section criterion `tensorObj_hom_ext`
(`(0 ⊗ 𝟙)(s ⊗ t) = 0 s ⊗ t = 0`). -/
private theorem AlgebraicGeometry.Scheme.Modules.zero_whiskerRight_viaSections {X : AlgebraicGeometry.Scheme.{u}}
    {A B : X.Modules} (M : X.Modules) :
    ((0 : A ⟶ B) ▷ M) = 0 := by
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
  intro U s t
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  erw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
  have h0 : (0 : A ⟶ B).val.app (Opposite.op U) s = 0 := rfl
  rw [h0, AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left]
  rfl

/-- The zero morphism is the zero map on sections (by definition). -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.zero_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (U : X.Opens) (x : Γ(M, U)) :
    (0 : M ⟶ N).app U x = 0 := rfl

/-- Composition is computed pointwise on sections (by definition; the elementwise form of `Hom.comp_app`). -/
theorem AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_totalSpaceHomEquiv {X : AlgebraicGeometry.Scheme.{u}}
    {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := rfl

/-- `toAlgebraMap` on an open `U` is `pullbackSections` (by definition; the direction "morphism ↦ algebra map" of Stacks 01LQ). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A)
    (U : X.Opens) (y : Γ(A.carrier, U)) :
    (AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A T h).app U y =
      AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U y := rfl

/-- `Sigma.ι n ≫ toAlgebraMap` on sections: first `Sigma.ι`, then `pullbackSections` (by definition). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.ι_comp_toAlgebraMap_app_apply {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.GradedQCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A.total) (n : ℕ)
    (U : X.Opens) (x : Γ(A.part n, U)) :
    (CategoryTheory.Limits.Sigma.ι A.part n ≫
        AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A.total T h).app U x =
      AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A.total T h U
        ((CategoryTheory.Limits.Sigma.ι A.part n).app U x) := rfl

/-- The augmentation `symAugmentation` vanishes on the degree-1 component: `symAugmentation` is a `Sigma.desc` taking `0`
on the positive-degree components (`Sigma.ι_desc`). -/
theorem AlgebraicGeometry.Scheme.Modules.Sigma_ι_symAugmentation {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) :
    CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part 1 ≫
      AlgebraicGeometry.Scheme.Modules.symAugmentation W = 0 := by
  unfold AlgebraicGeometry.Scheme.Modules.symAugmentation
  rw [CategoryTheory.Limits.Sigma.ι_desc]

/-- The augmentation vanishes on sections of the degree-1 component. -/
theorem AlgebraicGeometry.Scheme.Modules.symAugmentation_app_ι_app {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) (U : X.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part 1, U)) :
    (AlgebraicGeometry.Scheme.Modules.symAugmentation W).app U
      ((CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part 1).app U x) = 0 :=
  congrArg (fun f => f.app U x) (AlgebraicGeometry.Scheme.Modules.Sigma_ι_symAugmentation W)

/-- An `X`-morphism `m = g ≫ σ_0` factoring through the zero section corresponds under `totalSpaceHomEquiv` to
`0 ∈ Γ(T, g^*V)` (the zero section is the augmentation).
Proof: step 1 uses `pullbackSections_ofAlgebraMap` (the `right_inv` of 01LQ, open by open); step 2 splits `m` into
components and `subst`s, with `(g ≫ σ_0)^♯ = σ_0^♯ ≫ g^♯` by `Scheme.comp_app` (rfl); step 3 is
`Sigma_ι_symAugmentation` + `Adjunction.homAddEquiv_symm_zero` (`pullback g` is additive); step 4 is
`zero_whiskerRight_viaSections`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_eq_zero_of_factors_zeroSection
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V)
    (hm : m.left = T.hom ≫ AlgebraicGeometry.Scheme.zeroSection V) :
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m = 0 := by
  have hB : AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
      CategoryTheory.Limits.Sigma.ι
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫
      AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total T m
      = 0 := by
    obtain ⟨mleft, mright, mw⟩ := m
    -- the zero section is by definition the `left` of `ofAlgebraMap` (augmentation ε')
    have hz : AlgebraicGeometry.Scheme.zeroSection V =
        (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total
          (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))
          (AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
            (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf))
          (AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
            (AlgebraicGeometry.Scheme.Modules.dual V))).left := rfl
    rw [hz] at hm
    subst hm
    apply AlgebraicGeometry.Scheme.Modules.hom_ext
    intro U
    ext a
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply_totalSpaceHomEquiv,
      AlgebraicGeometry.Scheme.Modules.Hom.zero_app_apply]
    refine (AlgebraicGeometry.Scheme.relativeSpec.ι_comp_toAlgebraMap_app_apply _ _ _ _ _ _).trans ?_
    -- the degree-1 part is killed by the augmentation
    have h3 := AlgebraicGeometry.Scheme.Modules.symAugmentation_app_ι_app
      (AlgebraicGeometry.Scheme.Modules.dual V) U
      ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a)
    -- the `right_inv` of 01LQ, open by open: `pullbackSections` of `ofAlgebraMap ε'` is the section map of ε'
    have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total
        (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X)) _
        (AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
          (AlgebraicGeometry.Scheme.Modules.dual V)) U))
      ((CategoryTheory.Limits.Sigma.ι
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
          ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a))
    simp only [CommRingCat.hom_ofHom] at h1
    have h1' : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).total.algebraMapSections
        (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X)).hom
        (AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf))
        (AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
          (AlgebraicGeometry.Scheme.Modules.dual V)) U
        ((CategoryTheory.Limits.Sigma.ι
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
          ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a)) = 0 := by
      have e : (AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app U
          ((CategoryTheory.Limits.Sigma.ι
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
            ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a)) =
          ((AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app U
          ((AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V)).app U
          ((CategoryTheory.Limits.Sigma.ι
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
            ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a))) := rfl
      show (AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app U _ = 0
      rw [e, h3, map_zero]
    have H := h1.trans h1'
    unfold AlgebraicGeometry.Scheme.relativeSpec.pullbackSections at H ⊢
    -- σ0.app W (structureRingMap y) = 0: X.presheaf.map (eqToHom _) is an isomorphism, hence injective
    have h2 := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X)).left.presheaf.map
        (CategoryTheory.eqToHom _).op)).1 (H.trans (map_zero _).symm)
    -- (g ≫ σ0)^♯ = σ0^♯ followed by g^♯ (`Scheme.comp_app` is rfl), then h2 and two `map_zero`s
    show (T.left.presheaf.map (CategoryTheory.eqToHom _).op).hom
        ((T.hom.app _).hom
          (((AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
              (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total
              (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))
              (AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
                (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf))
              (AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
                (AlgebraicGeometry.Scheme.Modules.dual V))).left.app _).hom
            (((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap
              (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total).app
                (Opposite.op U)).hom
              ((CategoryTheory.Limits.Sigma.ι
                (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
                ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U a))))) = 0
    erw [h2, map_zero, map_zero]
  show AlgebraicGeometry.Scheme.totalSpace.toSection V T m = 0
  simp only [AlgebraicGeometry.Scheme.totalSpace.toSection]
  rw [hB, CategoryTheory.Adjunction.homAddEquiv_symm_zero,
    AlgebraicGeometry.Scheme.Modules.zero_whiskerRight_viaSections, CategoryTheory.Limits.zero_comp,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.comp_zero]
  exact AlgebraicGeometry.Scheme.Modules.Hom.zero_app_apply _ _

end
