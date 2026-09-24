import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlas
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Charts.GradedPieceLocallyFree
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Locally weighted polynomial graded algebras

A graded quasi-coherent algebra is *locally a weighted polynomial algebra* of weights `w` if it is
locally isomorphic to `MvPolynomial σ Γ(X, U)` with the weighted grading. The graded jet algebras
of the paper are of this form: their local bases are the monomials of weight `j`
(see the proof of the Veronese polarization lemma in the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `S` is locally the weighted polynomial algebra of weights `w`, in atlas form: there is a family
of affine opens covering `X` and on each of them a ring isomorphism
`S(U_i) ≃+* MvPolynomial σ Γ(X, U_i)` which identifies the `m`-th graded piece with the weighted
homogeneous component of weight `m` and the structure map with the constants `C`. Restricting to an
affine open is just evaluating the sheaf at it (`S.sections U`), so no pullback of graded algebras
is needed. The positivity hypothesis `hw` is not used by the atlas form; it is kept because every
consumer (`weightedProjectiveSpace`, …) requires it anyway. -/
def AlgebraicGeometry.Scheme.GradedQCAlgebra.IsLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i) : Prop :=
  S.toGradedAffineAlgebra.IsLocallyWeightedPolynomial w

/-- Unfolding of the atlas form of `IsLocallyWeightedPolynomial`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.isLocallyWeightedPolynomial_iff
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) {σ : Type u} [Finite σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    S.IsLocallyWeightedPolynomial w hw ↔
      Nonempty (S.toGradedAffineAlgebra.WeightedPolynomialAtlas w) := Iff.rfl

-- Jet case: `σ = Fin (n+1) × Fin k`, `w iq = (iq.2 : ℕ) + 1`.

end
