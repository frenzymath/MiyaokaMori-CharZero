import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6

/-! # Base change of projective morphisms

The base change of a projective morphism is projective (Stacks Project, Tag 02V6; for instance
`C × A¹ → A¹` is the base change of `C → Spec k`, as used in Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

theorem AlgebraicGeometry.IsProjectiveMorphism.baseChange {X Y Y' : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [AlgebraicGeometry.IsProjectiveMorphism f] :
    AlgebraicGeometry.IsProjectiveMorphism (CategoryTheory.Limits.pullback.snd f g) := by
  obtain ⟨S, i, hgen, hft, hi, hfac⟩ :=
    AlgebraicGeometry.IsProjectiveMorphism.exists_closed_immersion (f := f)
  let S' := S.pullback g
  let P := CategoryTheory.Limits.pullback f g
  obtain ⟨e, he, htw⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange g S
  let q0 : P ⟶ CategoryTheory.Limits.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom g :=
    CategoryTheory.Limits.pullback.map f g (AlgebraicGeometry.Scheme.relativeProj S).hom g
      i (𝟙 _) (𝟙 _) (by simpa [hfac, Category.assoc]) (by simp)
  let q : P ⟶ CategoryTheory.Limits.pullback g (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    q0 ≫ (CategoryTheory.Limits.pullbackSymmetry g
      (AlgebraicGeometry.Scheme.relativeProj S).hom).inv
  let j : P ⟶ (AlgebraicGeometry.Scheme.relativeProj S').left := q ≫ e.inv
  letI : CategoryTheory.MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsClosedImmersion.{u}) :=
    ⟨fun _ _ hf hg => ⟨hg.isClosedEmbedding.comp hf.isClosedEmbedding⟩⟩
  have hq0 : AlgebraicGeometry.IsClosedImmersion q0 := by
    dsimp [q0]
    apply CategoryTheory.MorphismProperty.pullbackMap
      (P := @AlgebraicGeometry.IsClosedImmersion)
      (inferInstance : AlgebraicGeometry.IsClosedImmersion i)
      (inferInstance : AlgebraicGeometry.IsClosedImmersion (𝟙 Y'))
    · exact hfac.symm
    · simp
  have hq : AlgebraicGeometry.IsClosedImmersion q := by
    dsimp [q]
    exact ⟨(inferInstance : AlgebraicGeometry.IsClosedImmersion
      ((CategoryTheory.Limits.pullbackSymmetry g
        (AlgebraicGeometry.Scheme.relativeProj S).hom).inv)).isClosedEmbedding.comp
          hq0.isClosedEmbedding⟩
  have hj : AlgebraicGeometry.IsClosedImmersion j := by
    dsimp [j]
    exact (CategoryTheory.MorphismProperty.cancel_right_of_respectsIso
      (P := @AlgebraicGeometry.IsClosedImmersion) q e.inv).mpr hq
  refine ⟨S', j, ?_, ?_, hj, ?_⟩
  · intro ℓ hℓ
    let α := S.mulPowOne ℓ
    let α' := S'.mulPowOne ℓ
    have hα : CategoryTheory.Epi α := hgen ℓ hℓ
    have mulPowOne_succ {Z : AlgebraicGeometry.Scheme.{u}}
        (T : Z.GradedQCAlgebra) (n : ℕ) :
        T.mulPowOne (n + 1) =
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
              (AlgebraicGeometry.Scheme.Modules.tensorPow (T.part 1) n) (T.part 1)).hom ≫
            (T.mulPowOne n ▷ T.part 1) ≫ T.mul n 1 := by
      rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.mulPowOne]
      rfl
    have hpow : ∀ n, S'.mulPowOne n =
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g (S.part 1) n).inv ≫
          (AlgebraicGeometry.Scheme.Modules.pullback g).map (S.mulPowOne n) := by
      intro n
      induction n with
      | zero =>
          -- `ε (pullback g)` and `pullbackUnitIso.inv` are not definitionally equal; use `pullback_ε_eq`
          exact congrArg (· ≫ (AlgebraicGeometry.Scheme.Modules.pullback g).map (S.mulPowOne 0))
            (AlgebraicGeometry.Scheme.Modules.pullback_ε_eq g)
      | succ n ih =>
          rw [mulPowOne_succ]
          rw [ih]
          dsimp [S', AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback]
          simp only [AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso,
            AlgebraicGeometry.Scheme.Modules.tensorPow]
          rw [mulPowOne_succ S n]
          simp [AlgebraicGeometry.Scheme.Modules.pullbackTensorIso, Category.assoc]
          rfl
    change CategoryTheory.Epi (S'.mulPowOne ℓ)
    rw [hpow ℓ]
    have hIso : CategoryTheory.Epi
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g (S.part 1) ℓ).inv :=
      @CategoryTheory.IsIso.epi_of_iso _ _ _ _ _
        (CategoryTheory.Iso.isIso_inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
          g (S.part 1) ℓ))
    letI : CategoryTheory.Epi α := hα
    exact CategoryTheory.epi_comp' hIso ((AlgebraicGeometry.Scheme.Modules.pullback g).map_epi α)
  · exact AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback g (S.part 1)
  · dsimp [j]
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]
    simp [q, q0, CategoryTheory.Limits.pullback.map, hfac, Category.assoc,
      CategoryTheory.Limits.pullback.lift_snd]

end
