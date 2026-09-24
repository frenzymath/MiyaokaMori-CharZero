import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC

/-! # Relatively very ample invertible sheaves

A relatively very ample invertible sheaf: `X` is realized over `S` by a closed immersion into the
relative Proj of a graded algebra generated in degree one, and `L` is the pullback of `O(1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple
    {Y X : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X) (L : Y.Modules) : Prop :=
  ∃ (S : X.GradedQCAlgebra) (i : Y ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left),
    S.GeneratedInDegreeOne ∧ AlgebraicGeometry.IsClosedImmersion i ∧
      i ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom = π ∧
      Nonempty (L ≅ (AlgebraicGeometry.Scheme.Modules.pullback i).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S 1))

end
