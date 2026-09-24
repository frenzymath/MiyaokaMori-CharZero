import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal

/-! # Compatibility of the projection-formula comparison map with the adjunction unit

Compatibility of the projection-formula comparison map with the unit of `i^* ⊣ i_*`, for an arbitrary
morphism of schemes `i : Z ⟶ X`. Two pure category-theory identities (Stacks 01E8 together with the
triangle identities of the adjunction and the strong monoidal structure of `i^*`):

* `whiskerLeft_unit_comp_projectionFormulaHom`:
  `(N ◁ η_M) ≫ θ_{N, i^*M} = η_{N ⊗ M} ≫ i_*(δ_{N,M})`, where `θ` is `projectionFormulaHom` and
  `δ = pullbackTensorObjHom` is the comparison `i^*(N ⊗ M) → i^*N ⊗ i^*M`.
  Proof: `θ_{N,P} = η_{N ⊗ i_*P} ≫ i_*(δ_{N, i_*P} ≫ (i^*N ◁ ε_P))` (definition, `homEquiv_apply`);
  move `N ◁ η_M` through `η` by naturality of `η`, through `δ` by naturality of `δ` in the right
  variable, and cancel `i^*(η_M) ≫ ε_{i^*M} = 𝟙` (left triangle identity).
* `whiskerLeft_unitToPushforwardObjUnit_comp_projectionFormulaHom`:
  `(M ◁ u) ≫ θ_{M, O_Z} ≫ i_*(ρ_{i^*M}) = ρ_M ≫ η_M`, where `u : O_X → i_*O_Z` is
  `SheafOfModules.unitToPushforwardObjUnit`.
  Proof: `u = η_{O_X} ≫ i_*(ε₀)` with `ε₀ : i^*O_X ≅ O_Z` (Mathlib
  `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`); naturality of `θ` in the right
  variable moves `i_*(ε₀)` inside; the first identity turns `(M ◁ η_{O_X}) ≫ θ` into
  `η_{M ⊗ O_X} ≫ i_*(δ)`; the right-unitality of the strong monoidal functor `i^*`
  (`pullback_right_unitality`) gives `δ ≫ (i^*M ◁ ε₀) ≫ ρ = i^*(ρ_M)`; finally naturality of `η`.

Used for the restriction sequence of a regular section: these
identities identify the right-hand map `L → i_*i^*L` of that sequence with `L ⊗ O_X → L ⊗ i_*O_Z`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

variable {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)

/-- `(N ◁ η_M) ≫ θ_{N, i^*M} = η_{N ⊗ M} ≫ i_*(δ_{N,M})`. -/
theorem whiskerLeft_unit_comp_projectionFormulaHom (N M : X.Modules) :
    (N ◁ (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) ≫
        AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i N
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M) =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (N ⊗ M) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom i N M) := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_eq_projFormulaHom]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Adjunction.homEquiv_symm_projFormulaHom, Adjunction.homEquiv_counit,
    Adjunction.left_triangle_components, Category.id_comp,
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_eq_δ, ← Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural_right, Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    Adjunction.left_triangle_components, MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- For `v : O_X → i_*O_Z` whose adjoint transpose is `i^*O_X ≅ O_Z` (`pullbackUnitIso`):
`(M ◁ v) ≫ θ_{M, O_Z} ≫ i_*(ρ_{i^*M}) = ρ_M ≫ η_M`. -/
theorem whiskerLeft_comp_projectionFormulaHom_rightUnitor (M : X.Modules)
    (v : 𝟙_ X.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules))
    (hv : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm v =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso i).hom) :
    (M ◁ v) ≫ AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i M (𝟙_ Z.Modules) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M)).hom =
      (ρ_ M).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm.injective
  have hR : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm
      ((ρ_ M).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) =
      (AlgebraicGeometry.Scheme.Modules.pullback i).map (ρ_ M).hom := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
      Adjunction.left_triangle_components, Category.comp_id]
  have hL : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).symm
      ((M ◁ v) ≫ AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i M (𝟙_ Z.Modules) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M)).hom) =
      (AlgebraicGeometry.Scheme.Modules.pullback i).map (M ◁ v) ≫
        (Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback i)
            (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal i) M
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules)) ≫
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M ◁
            (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).counit.app
              (𝟙_ Z.Modules))) ≫
        (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M)).hom := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
      AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_eq_projFormulaHom]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [Adjunction.homEquiv_symm_projFormulaHom]
  have hv' : (AlgebraicGeometry.Scheme.Modules.pullback i).map v ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso i).hom := by
    rw [← hv, Adjunction.homEquiv_counit]
  rw [hL, hR, ← Category.assoc, ← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_right]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hv',
    AlgebraicGeometry.Scheme.Modules.pullback_right_unitality,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]
  have hδ : Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback i)
      (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal i) M (𝟙_ X.Modules) =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso i M (𝟙_ X.Modules)).hom := rfl
  rw [hδ, Iso.hom_inv_id_assoc]

/-- `(M ◁ u) ≫ θ_{M, O_Z} ≫ i_*(ρ_{i^*M}) = ρ_M ≫ η_M` for `u = unitToPushforwardObjUnit`. -/
theorem whiskerLeft_unitToPushforwardObjUnit_comp_projectionFormulaHom (M : X.Modules) :
    (M ◁ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≫
        AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i M (𝟙_ Z.Modules) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M)).hom =
      (ρ_ M).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M :=
  whiskerLeft_comp_projectionFormulaHom_rightUnitor i M
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) rfl

end AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

end
