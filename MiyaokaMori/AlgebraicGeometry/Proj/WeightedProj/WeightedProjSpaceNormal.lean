import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalIsLocal
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SpecNormalOfIntegrallyClosed
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjChartProdNormal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Normality of products with weighted projective space

Weighted projective space is normal (Dolgachev, *Weighted projective varieties*, Proposition
1.3.3(i)), extended to the local products used in the paper: **if `U` is integral and normal over
`k`, then `U ×_k P(w)` is normal** (`U = Spec k` gives `P(w)` itself). This is used in the proof of
the Veronese polarization lemma.

The proof is purely commutative-algebraic (no group actions or roots of unity, no `[IsAlgClosed]` or
`[CharZero]`):
1. An affine open cover `{Spec A}` of `U` and the coordinate chart cover `{D₊(x_i)}` of `P(w)` give
   the open cover `{Spec A ×_k D₊(x_i)}` of `U ×_k P(w)` (`Scheme.Pullback.openCoverOfLeftRight`);
   normality is a local property.
2. `U` integral and normal implies that every `A` is an integrally closed domain
   (`affine_isIntegral_iff` and `isIntegrallyClosed_of_Spec_isNormal`).
3. `Spec A ×_k D₊(x_i)` is normal (`weightedProjChart_prod_isNormal`): `A ⊗_k k[x]_(x_i) ≅ A[x]_(x_i)`
   is an integrally closed domain.

The hypotheses are `[IsIntegral U] [U.IsNormal]`; the callers only use `U` an affine open of a smooth
curve or `U = Spec k`, where normality comes from `Smooth.isNormal_of_field_of_dim_le_one`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `U ×_k P(w)` is normal for an integral normal `k`-scheme `U`. -/
theorem weightedProjectiveSpace_prod_isNormal (k : Type u) [Field k]
    {σ : Type u} [Fintype σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : AlgebraicGeometry.Scheme.{u}) (pU : U ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsIntegral U] [U.IsNormal] :
    (CategoryTheory.Limits.pullback pU
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).IsNormal := by
  apply isNormal_of_openCover (AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
    U.affineOpenCover.openCover
    (AlgebraicGeometry.weightedProjAffineChartCover k w hw).openCover pU
    (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  rintro ⟨i, j⟩
  show (CategoryTheory.Limits.pullback (U.affineOpenCover.openCover.f i ≫ pU)
      ((AlgebraicGeometry.weightedProjAffineChartCover k w hw).openCover.f j ≫
        (weightedProjectiveSpace k w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)))).IsNormal
  apply AlgebraicGeometry.Scheme.isNormal_of_nonempty_imp
  intro hne
  obtain ⟨z⟩ := hne
  haveI hoi : AlgebraicGeometry.IsOpenImmersion (U.affineOpenCover.openCover.f i) :=
    U.affineOpenCover.openCover.map_prop i
  haveI : Nonempty (AlgebraicGeometry.Spec (U.affineOpenCover.X i)) :=
    ⟨(CategoryTheory.Limits.pullback.fst (U.affineOpenCover.openCover.f i ≫ pU)
      ((AlgebraicGeometry.weightedProjAffineChartCover k w hw).openCover.f j ≫
        (weightedProjectiveSpace k w hw ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)))).base z⟩
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec (U.affineOpenCover.X i)) :=
    @AlgebraicGeometry.isIntegral_of_isOpenImmersion _ _ (U.affineOpenCover.openCover.f i) hoi
      inferInstance inferInstance
  haveI : IsDomain (U.affineOpenCover.X i) :=
    (AlgebraicGeometry.affine_isIntegral_iff (U.affineOpenCover.X i)).mp inferInstance
  haveI : IsIntegrallyClosed (U.affineOpenCover.X i) :=
    AlgebraicGeometry.isIntegrallyClosed_of_Spec_isNormal (U.affineOpenCover.X i)
      (@AlgebraicGeometry.Scheme.IsNormal.of_isOpenImmersion _ _
        (U.affineOpenCover.openCover.f i) hoi inferInstance)
  obtain ⟨a, ha⟩ :=
    AlgebraicGeometry.Spec.map_surjective (U.affineOpenCover.openCover.f i ≫ pU)
  have hchart :=
    AlgebraicGeometry.weightedProjChart_prod_isNormal k w hw j (U.affineOpenCover.X i) a
  rwa [ha] at hchart

end
