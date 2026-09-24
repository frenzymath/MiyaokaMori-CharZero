import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackIdMonoidal

/-! # Pullback of graded quasi-coherent algebras along the identity

Statement. Three generic facts about the category of graded quasi-coherent algebras `X.GradedQCAlgebra`
(`GradedQcAlgebraCategory.lean`) and the pullback `S.pullback g` (`GradedQcAlgebraPullback.lean`):
1. `GradedQCAlgebra.pullbackMap φ g : S.pullback g ⟶ T.pullback g` — pullback of a morphism `φ : S ⟶ T` of graded
   algebras (componentwise `g^*(φ.app m)`; compatibility with `mul`/`one` is naturality of `μ`, exactly as in the
   existing `pullbackMapIso` for isomorphisms);
2. `GradedQCAlgebra.isIso_of_isIso_app`: a morphism of graded algebras whose components are all isomorphisms is an
   isomorphism (the inverse components are compatible with `mul`/`one` by cancelling the isomorphisms);
3. `GradedQCAlgebra.pullbackId S : S.pullback (𝟙 X) ≅ S` — pullback along the identity, with components
   `(Modules.pullbackId X).hom.app (S.part m)`; compatibility with `mul`/`one` is the monoidality of `pullbackId`
   (`ModulesPullbackIdMonoidal.lean`: `μ_pullbackId`, `ε_pullbackId`) plus naturality of `pullbackId`.

Source: pseudofunctoriality of `Modules.pullback` (Mathlib `Scheme.Modules.pullbackId`); Stacks 01CD.
Used by `reesDeformation_restrictToLambda_one` (`DeformedJetAlgebra.lean`): the fibre at `λ = 1` of the Rees
deformation is identified with `S` through `R.pullback s ≅ (S.pullback π).pullback s ≅ S.pullback (s ≫ π) =
S.pullback (𝟙 X) ≅ S`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section


namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- Two morphisms of graded QC algebras with the same components are equal. -/
theorem Hom.ext_app {S T : X.GradedQCAlgebra} {φ ψ : S ⟶ T} (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  obtain ⟨φ, hφm, hφ1⟩ := φ
  obtain ⟨ψ, hψm, hψ1⟩ := ψ
  simp only at h
  cases funext h
  rfl

/-- Pullback of a morphism of graded QC algebras along `g : X ⟶ Y` (componentwise `g^*`). -/
def pullbackMap {S T : Y.GradedQCAlgebra} (φ : S ⟶ T) (g : X ⟶ Y) : S.pullback g ⟶ T.pullback g where
  app m := (AlgebraicGeometry.Scheme.Modules.pullback g).map (φ.app m)
  map_mul := by
    intro m n
    dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
    simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
    rw [φ.map_mul]
    simp only [Functor.map_comp]
    have hμ := CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc
      (AlgebraicGeometry.Scheme.Modules.pullback g) (φ.app m) (φ.app n)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map (T.mul m n))
    rw [← hμ]
  map_one := by
    dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
    simp only [Category.assoc, ← (AlgebraicGeometry.Scheme.Modules.pullback g).map_comp]
    rw [φ.map_one]

@[simp] theorem pullbackMap_app {S T : Y.GradedQCAlgebra} (φ : S ⟶ T) (g : X ⟶ Y) (m : ℕ) :
    (pullbackMap φ g).app m = (AlgebraicGeometry.Scheme.Modules.pullback g).map (φ.app m) := rfl

/-- A morphism of graded QC algebras whose components are all isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_app {S T : X.GradedQCAlgebra} (φ : S ⟶ T) [hφ : ∀ m, IsIso (φ.app m)] : IsIso φ := by
  refine ⟨⟨⟨fun m => inv (φ.app m), ?_, ?_⟩, ?_, ?_⟩⟩
  · intro m n
    rw [← cancel_epi (φ.app m ⊗ₘ φ.app n), ← Category.assoc, ← φ.map_mul, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, ← Category.assoc,
      CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, IsIso.hom_inv_id, IsIso.hom_inv_id,
      CategoryTheory.MonoidalCategory.id_tensorHom_id, Category.id_comp]
  · rw [← φ.map_one, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · exact Hom.ext_app fun m => IsIso.hom_inv_id (φ.app m)
  · exact Hom.ext_app fun m => IsIso.inv_hom_id (φ.app m)

/-- The comparison morphism `S.pullback (𝟙 X) ⟶ S` (components `(Modules.pullbackId X).hom.app (S.part m)`). -/
def pullbackIdHom (S : X.GradedQCAlgebra) : S.pullback (𝟙 X) ⟶ S where
  app m := (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (S.part m)
  map_mul := by
    intro m n
    dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
    rw [Category.assoc, (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.naturality (S.mul m n),
      ← Category.assoc, AlgebraicGeometry.Scheme.Modules.μ_pullbackId]
    rfl
  map_one := by
    dsimp [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
    rw [Category.assoc, (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.naturality S.one,
      ← Category.assoc, AlgebraicGeometry.Scheme.Modules.ε_pullbackId, Category.id_comp]
    rfl

instance pullbackIdHom_app_isIso (S : X.GradedQCAlgebra) (m : ℕ) : IsIso ((pullbackIdHom S).app m) :=
  inferInstanceAs (IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (S.part m)))

instance pullbackIdHom_isIso (S : X.GradedQCAlgebra) : IsIso (pullbackIdHom S) :=
  isIso_of_isIso_app (pullbackIdHom S)

/-- Pullback along the identity is the identity, as graded QC algebras. -/
def pullbackId (S : X.GradedQCAlgebra) : S.pullback (𝟙 X) ≅ S := asIso (pullbackIdHom S)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
