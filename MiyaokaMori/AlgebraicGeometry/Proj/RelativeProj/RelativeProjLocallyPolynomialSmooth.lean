import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.PolynomialProjSmoothOfRelativeDimension

/-! # A locally polynomial relative Proj is smooth over the base

Statement: `S` a graded quasicoherent `O_X`-algebra which is locally the standard-graded polynomial algebra in
`n + 1` variables (`σ` with `|σ| = n + 1`, all weights 1). Then the structure morphism `Proj_X S → X` is smooth
of relative dimension `n` (`Proj_X S` is a `P^n`-bundle over `X`).

Proof:
1. Locality on the target. `SmoothOfRelativeDimension n` is a `HasRingHomProperty` (Mathlib
   `Morphisms/Smooth.lean`), hence Zariski-local on the target (`HasRingHomProperty.instIsZariskiLocalAtTarget`,
   given explicitly since instance search does not find it): by `IsZariskiLocalAtTarget.iff_of_openCover`
   applied to the atlas cover `𝒜.openCover` (the affine charts `U_i = 𝒜.chart i`, covering X) it suffices to
   show `SmoothOfRelativeDimension n (pullback.snd π U_i.ι)` for each i.
2. Identify the restriction with the chart. `projChart_isPullback U_i` (Stacks 01NQ, `RelativeProj.lean`)
   says the chart square `Proj S(U_i) → Proj_X S`, `Proj S(U_i) → U_i` is a pullback of the cospan
   `(U_i.ι, π)`, so `pullback.snd π U_i.ι = (isoPullback).inv ≫ projToOpen U_i`; `SmoothOfRelativeDimension n`
   respects isomorphisms (`HasRingHomProperty.eq_affineLocally` + `affineLocally_respectsIso`, as in
   `ProjectiveLineSmoothProof.lean`), so it suffices to treat `projToOpen U_i`.
3. Transport along the chart isomorphism. `projIso_hom_weightedProjToOpen`
   (`LocallyWeightedProjLocalProduct.lean`): the atlas isomorphism
   `S(U_i) ≃+* Γ(X,U_i)[x_σ]` induces `projIso : Proj S(U_i) ≅ Proj Γ(X,U_i)[x_σ]` with
   `projIso.hom ≫ weightedProjToOpen = projToOpen`, where
   `weightedProjToOpen = Proj.toSpecZero ≫ Spec.map (algebraMap Γ(X,U_i) (Γ(X,U_i)[x_σ])_0) ≫ isoSpec.inv`.
   Cancelling the isomorphisms `projIso.hom` (left) and `isoSpec.inv` (right), it suffices that
   `Proj R[x_σ] → Spec R` (with `R = Γ(X,U_i)`) is smooth of relative dimension n.
4. `P^n_R → Spec R` is smooth of relative dimension n: `projToSpecBase_smoothOfRelativeDimension`
   (`PolynomialProjSmoothOfRelativeDimension.lean`): Zariski-local on the source, the standard charts
   `D_+(x_j) ≅ Spec (R[x_σ]_{x_j})_0` cover, and `(R[x_σ]_{x_j})_0 ≅ R[y_k : k ≠ j]` by dehomogenisation
   (`PolynomialProjChartRingEquiv.lean`), a polynomial algebra in n variables, which is standard smooth of
   relative dimension n.

Source: Hartshorne II.2.5, II.7.11; Stacks 01NE. Used for the ruled surface `P(O ⊕ L)` of Corollary 4.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

set_option backward.isDefEq.respectTransparency.types false in
theorem AlgebraicGeometry.Scheme.relativeProj_smoothOfRelativeDimension_of_isLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] (n : ℕ) (hσ : Fintype.card σ = n + 1)
    (hS : S.IsLocallyWeightedPolynomial (fun _ : σ => 1) (fun _ => Nat.one_pos)) :
    AlgebraicGeometry.SmoothOfRelativeDimension n (AlgebraicGeometry.Scheme.relativeProj S).hom := by
  classical
  obtain ⟨𝒜⟩ := hS
  have := AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n)
  have hiso : MorphismProperty.RespectsIso (@AlgebraicGeometry.SmoothOfRelativeDimension.{u} n) := by
    rw [AlgebraicGeometry.HasRingHomProperty.eq_affineLocally
      (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n)]
    exact AlgebraicGeometry.affineLocally_respectsIso
      (P := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  -- Step 1: locality on the target over the atlas cover.
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n) 𝒜.openCover]
  intro i
  -- Step 2: the restriction to a chart is `projToOpen` up to the chart isomorphism (Stacks 01NQ).
  have hA := (S.toGradedAffineAlgebra.projChart_isPullback (𝒜.chart i)).flip
  change AlgebraicGeometry.SmoothOfRelativeDimension n
    (CategoryTheory.Limits.pullback.snd S.toGradedAffineAlgebra.relativeProj.hom
      (𝒜.chart i).toOpens.ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n) hA.isoPullback.hom,
    hA.isoPullback_hom_snd]
  -- Step 3: transport along the atlas isomorphism `Proj S(U_i) ≅ Proj Γ(X,U_i)[x_σ]`.
  rw [← AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.projIso_hom_weightedProjToOpen
      𝒜 i,
    MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n)
      (𝒜.projIso i).hom (𝒜.weightedProjToOpen i),
    AlgebraicGeometry.Scheme.GradedAffineAlgebra.WeightedPolynomialAtlas.weightedProjToOpen,
    ← Category.assoc,
    MorphismProperty.cancel_right_of_respectsIso (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n)
      _ (𝒜.chart i).2.isoSpec.inv]
  -- Step 4: projective space over `Γ(X, U_i)` is smooth of relative dimension `n`.
  exact MvPolynomial.StandardProjChart.projToSpecBase_smoothOfRelativeDimension
    Γ(X, (𝒜.chart i).toOpens) σ n hσ

end
