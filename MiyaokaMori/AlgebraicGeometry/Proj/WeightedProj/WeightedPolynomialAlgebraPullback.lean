import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlasPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialPullbackCompatibility

/-! # Pullback of the weighted polynomial algebra

The pullback of the weighted polynomial algebra sheaf along any morphism is again the weighted
polynomial algebra (each graded piece is the free sheaf on the monomials of weight `j`, and pullback
preserves free sheaves); consequently "locally weighted polynomial" is preserved under pullback.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

private theorem gradedQCAlgebraHom_ext' {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ ψ : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom S T)
    (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  cases φ with
  | mk φ hmul hone =>
    cases ψ with
    | mk ψ hmul' hone' =>
      simp only at h
      cases funext h
      rfl

/-- `g^* (weightedPolynomialQCAlgebra X w hw) ≅ weightedPolynomialQCAlgebra V w hw` as graded
quasi-coherent algebras. -/
theorem AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback {X V : AlgebraicGeometry.Scheme.{u}}
    (g : V ⟶ X) {σ : Type u} [Finite σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Nonempty ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g ≅
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw) := by
  let e : ∀ m : ℕ,
      ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g).part m ≅
        (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw).part m :=
    fun m => AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g (weightedMonomials w m)
  let φ : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom
      ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g)
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw) :=
    ⟨fun m => (e m).hom,
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback_freeIso_map_mul g w hw,
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback_freeIso_map_one g w hw⟩
  let ψ : AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom
      (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw)
      ((AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X w hw).pullback g) :=
    ⟨fun m => (e m).inv, by
      intro i j
      rw [← cancel_epi (((e i).hom ⊗ₘ (e j).hom))]
      have h := φ.map_mul i j
      change _ = ((e i).hom ⊗ₘ (e j).hom) ≫
        (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw).mul i j at h
      dsimp [φ] at h
      rw [← Category.assoc, ← h]
      simp only [← Category.assoc,
        CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
        Iso.hom_inv_id, CategoryTheory.MonoidalCategory.id_tensorHom_id,
        Category.id_comp]
      simp, by
      have h := φ.map_one
      change _ = (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra V w hw).one at h
      rw [← h, Category.assoc, (e 0).hom_inv_id, Category.comp_id]⟩
  refine ⟨{ hom := φ, inv := ψ, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply gradedQCAlgebraHom_ext'
    intro m
    exact (e m).hom_inv_id
  · apply gradedQCAlgebraHom_ext'
    intro m
    exact (e m).inv_hom_id

/-- Being locally a weighted polynomial algebra is preserved under pullback. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.IsLocallyWeightedPolynomial.pullback
    {X V : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ X) (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (hS : S.IsLocallyWeightedPolynomial w hw) :
    (S.pullback g).IsLocallyWeightedPolynomial w hw := by
  rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.isLocallyWeightedPolynomial_iff] at hS ⊢
  obtain ⟨𝒜⟩ := hS
  exact AlgebraicGeometry.Scheme.GradedQCAlgebra.weightedPolynomialAtlas_pullback g S w 𝒜

end
