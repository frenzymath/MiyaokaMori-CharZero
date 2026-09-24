import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory
noncomputable section

noncomputable def AlgebraicGeometry.Scheme.Modules.symAugmentationZero {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part 0 ⟶ 𝟙_ X.Modules := by
  unfold AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
  split
  · exact AlgebraicGeometry.Scheme.Modules.symPowDesc W 0 (𝟙 _) (fun i => i.elim0)
  · exact 𝟙 _

noncomputable def AlgebraicGeometry.Scheme.Modules.symAugmentation {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.carrier ⟶ 𝟙_ X.Modules :=
  CategoryTheory.Limits.Sigma.desc fun m =>
    match m with
    | 0 => AlgebraicGeometry.Scheme.Modules.symAugmentationZero W
    | _ + 1 => 0

end
