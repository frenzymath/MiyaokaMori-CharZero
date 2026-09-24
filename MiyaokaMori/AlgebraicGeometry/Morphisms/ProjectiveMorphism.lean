import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # Projective morphisms

A morphism `X ⟶ S` is projective if `X` admits a closed immersion over `S` into the relative Proj
of a graded quasi-coherent `𝒪_S`-algebra generated in degree one.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

class AlgebraicGeometry.IsProjectiveMorphism {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) : Prop where
  exists_closed_immersion : ∃ (S : X.GradedQCAlgebra)
    (i : Y ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left),
    S.GeneratedInDegreeOne ∧ (S.part 1).IsFiniteType ∧
      AlgebraicGeometry.IsClosedImmersion i ∧
      i ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom = f

end
