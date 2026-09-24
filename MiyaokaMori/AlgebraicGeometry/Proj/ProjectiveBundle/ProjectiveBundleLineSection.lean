import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMapFunctorial
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The `L`-section of `P(O_X ⊕ L)`

The "`L`-section" `σ_L : X ⟶ P(O_X ⊕ L)` determined by the sub line bundle `L ⊆ O_X ⊕ L`. In the
paper, `Tot(L)` is the complement of the `L`-section in `P(O ⊕ L)` (§1), and the `L`-section is the
curve `Σ_∞` of the ruled surface (proof of the ruled-surface realization corollary).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The biproduct `O_X ⊕ L`: the unit sheaf is written `show X.Modules from SheafOfModules.unit X.ringCatSheaf`
   so that its type is syntactically `X.Modules` (written directly, `SheafOfModules.unit …` has type
   `SheafOfModules X.ringCatSheaf`; `X.Modules` is an irreducible `def`, and the `HasBinaryBiproduct` /
   `IsLocallyFree` instances would not unify). -/

/- `σ_L`: the sub line bundle `L ⊆ O ⊕ L` corresponds to the invertible quotient `(O ⊕ L)^∨ ↠ L^∨`
   (the dual `dualMap` of `inr : L → O ⊕ L`). It is obtained from the universal property of the
   projective bundle (`projBundle.lift` with `T = X`, `f = 𝟙`, `(𝟙)^*` removed by `pullbackId`) with
   `M = L^∨` (the instance `IsLineBundle.dual`). The quotient map is an epimorphism: `quotientMap_epi`
   (split epimorphism with section `dualMap snd`). -/

/-- The quotient map `ψ : (𝟙)^*(O ⊕ L)^∨ ⟶ L^∨` of `σ_L` (`pullbackId` followed by `dualMap inr`). -/

noncomputable def AlgebraicGeometry.Scheme.lSection.quotientMap {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.CategoryStruct.id X)).obj
        (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ⟶
      AlgebraicGeometry.Scheme.Modules.dual L :=
  (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
      (AlgebraicGeometry.Scheme.Modules.dual (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) ≫
    AlgebraicGeometry.Scheme.Modules.dualMap
      (CategoryTheory.Limits.biprod.inr (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))

/-- The quotient map is an epimorphism: `pullbackId.hom.app _` is an isomorphism (hence epi), and
`dualMap inr` is a split epimorphism with section `dualMap snd`:
`dualMap snd ≫ dualMap inr = dualMap (inr ≫ snd) = dualMap (𝟙 L) = 𝟙` (`dualMap_comp`, `biprod.inr_snd`,
`dualMap_id`). Symmetric to `oSection.quotientMap_epi`. -/
theorem AlgebraicGeometry.Scheme.lSection.quotientMap_epi {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    CategoryTheory.Epi (AlgebraicGeometry.Scheme.lSection.quotientMap L) := by
  unfold AlgebraicGeometry.Scheme.lSection.quotientMap
  have : CategoryTheory.IsSplitEpi (AlgebraicGeometry.Scheme.Modules.dualMap
      (CategoryTheory.Limits.biprod.inr (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))) :=
    CategoryTheory.IsSplitEpi.mk'
      ⟨AlgebraicGeometry.Scheme.Modules.dualMap
        (CategoryTheory.Limits.biprod.snd (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)), by
        rw [← AlgebraicGeometry.Scheme.Modules.dualMap_comp, CategoryTheory.Limits.biprod.inr_snd,
          AlgebraicGeometry.Scheme.Modules.dualMap_id]⟩
  exact CategoryTheory.epi_comp _ _

/-- The `L`-section `σ_L : X ⟶ P(O_X ⊕ L)` determined by the sub line bundle `L ⊆ O_X ⊕ L`. -/
noncomputable def AlgebraicGeometry.Scheme.lSection {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    X ⟶ (AlgebraicGeometry.Scheme.projBundle
      (CategoryTheory.Limits.biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).left :=
  -- the `[Epi ψ]` argument of `lift` is given explicitly (the type of `ψ` contains `show`, and instance
  -- search does not unify)
  @AlgebraicGeometry.Scheme.projBundle.lift X X
    (CategoryTheory.Limits.biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) _ _
    (CategoryTheory.CategoryStruct.id X) (AlgebraicGeometry.Scheme.Modules.dual L) _
    (AlgebraicGeometry.Scheme.lSection.quotientMap L)
    (AlgebraicGeometry.Scheme.lSection.quotientMap_epi L)

/-- `σ_L` is a section of the structure morphism `π : P(O ⊕ L) → X` (`lift_hom` with `f = 𝟙`); this is
used to show that `σ_L` is a closed immersion. -/

theorem AlgebraicGeometry.Scheme.lSection_comp {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Scheme.lSection L ≫
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).hom
      = CategoryTheory.CategoryStruct.id X :=
  -- `lift_hom` with `f = 𝟙`; the `Epi` argument is given explicitly, as in the definition
  @AlgebraicGeometry.Scheme.projBundle.lift_hom X X
    (CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L) _ _
    (CategoryTheory.CategoryStruct.id X) (AlgebraicGeometry.Scheme.Modules.dual L) _
    (AlgebraicGeometry.Scheme.lSection.quotientMap L)
    (AlgebraicGeometry.Scheme.lSection.quotientMap_epi L)

end
