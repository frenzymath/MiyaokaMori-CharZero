import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Restriction of a family over `C × A¹` to a fibre `λ = t`

Restriction at `λ = t` of graded algebras / sheaves of modules on `C × A¹`: pullback along the section
`sectionAt t : C → C × A¹` (used at the two ends `λ = 1` and `λ = 0` of the deformation).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.restrictToLambda {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (S : (AlgebraicGeometry.Scheme.affineLineOver X).GradedQCAlgebra) (t : k) : X.GradedQCAlgebra :=
  S.pullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)

noncomputable def SheafOfModules.restrictToLambda {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (V : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) (t : k) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t)).obj V

end
