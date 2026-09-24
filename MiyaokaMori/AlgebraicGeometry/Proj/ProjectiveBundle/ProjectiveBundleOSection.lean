import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMapFunctorial
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The `O`-section of `P(O_X ⊕ L)`

The `O`-section `σ_O : X ⟶ P(O_X ⊕ L)` determined by the sub line bundle `O_X ⊆ O_X ⊕ L` (symmetric
to the `L`-section of `ProjectiveBundleLineSection`); its image is the curve `Σ_0` of the ruled
surface in the proof of the ruled-surface realization corollary of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section



/- `σ_O`: the sub line bundle `O ⊆ O ⊕ L` corresponds to the invertible quotient `(O ⊕ L)^∨ ↠ O^∨`
   (the dual `dualMap` of `inl : O → O ⊕ L`, i.e. restriction of linear functions to `O ⊕ 0`). It is
   obtained from the universal property of the projective bundle (`projBundle.lift` with `T = X`,
   `f = 𝟙`, `(𝟙)^*` removed by `pullbackId`); the quotient is `M = O^∨` (`≅ O_X`, not replaced by `O_X`
   here, which saves an isomorphism). The quotient map is an epimorphism: `quotientMap_epi` (split
   epimorphism with section `dualMap fst`). -/

/-- The quotient map `ψ : (𝟙)^*(O ⊕ L)^∨ ⟶ O^∨` of `σ_O` (`pullbackId` followed by `dualMap inl`). -/

noncomputable def AlgebraicGeometry.Scheme.oSection.quotientMap {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.CategoryStruct.id X)).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ⟶
      AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
      (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ≫
    AlgebraicGeometry.Scheme.Modules.dualMap
      (CategoryTheory.Limits.biprod.inl (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))

/-- The quotient map is an epimorphism: `pullbackId.hom.app _` is an isomorphism (hence epi), and
`dualMap inl` is a split epimorphism with section `dualMap fst`:
`dualMap fst ≫ dualMap inl = dualMap (inl ≫ fst) = dualMap (𝟙 O) = 𝟙` (`dualMap_comp`, `biprod.inl_fst`,
`dualMap_id`). -/
theorem AlgebraicGeometry.Scheme.oSection.quotientMap_epi {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    CategoryTheory.Epi (AlgebraicGeometry.Scheme.oSection.quotientMap L) := by
  unfold AlgebraicGeometry.Scheme.oSection.quotientMap
  have : CategoryTheory.IsSplitEpi (AlgebraicGeometry.Scheme.Modules.dualMap
      (CategoryTheory.Limits.biprod.inl (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) :=
    CategoryTheory.IsSplitEpi.mk'
      ⟨AlgebraicGeometry.Scheme.Modules.dualMap
        (CategoryTheory.Limits.biprod.fst (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)), by
        rw [← AlgebraicGeometry.Scheme.Modules.dualMap_comp, CategoryTheory.Limits.biprod.inl_fst,
          AlgebraicGeometry.Scheme.Modules.dualMap_id]⟩
  exact CategoryTheory.epi_comp _ _

/-- The `O`-section `σ_O : X ⟶ P(O_X ⊕ L)` determined by the sub line bundle `O_X ⊆ O_X ⊕ L`. -/
noncomputable def AlgebraicGeometry.Scheme.oSection {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    X ⟶ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).left :=
  -- the `[Epi ψ]` argument of `lift` is given explicitly (the type of `ψ` contains `show`, and instance
  -- search does not unify)
  @AlgebraicGeometry.Scheme.projBundle.lift X X
    (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) _ _
    (CategoryTheory.CategoryStruct.id X) (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) _
    (AlgebraicGeometry.Scheme.oSection.quotientMap L)
    (AlgebraicGeometry.Scheme.oSection.quotientMap_epi L)

/-- `σ_O` is a section of the structure morphism `π : P(O ⊕ L) → X`. -/
theorem AlgebraicGeometry.Scheme.oSection_comp {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.oSection L ≫
      (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom
      = CategoryTheory.CategoryStruct.id X :=
  -- `lift_hom` with `f = 𝟙`; the `Epi` argument is given explicitly, as in the definition
  @AlgebraicGeometry.Scheme.projBundle.lift_hom X X
    (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) _ _
    (CategoryTheory.CategoryStruct.id X)
    (AlgebraicGeometry.Scheme.Modules.dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) _
    (AlgebraicGeometry.Scheme.oSection.quotientMap L)
    (AlgebraicGeometry.Scheme.oSection.quotientMap_epi L)

end
