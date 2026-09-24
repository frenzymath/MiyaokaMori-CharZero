import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjSeparated

/-! # The projectivization of a vector bundle

The projectivization `P(V)` of a vector bundle, parametrizing the one-dimensional subspaces of its
fibers; with this convention `P(V) = Proj_X Sym(V^∨)` (the paper's `P_lines`, §1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The projective bundle `P(V) = Proj_X Sym(V^∨)` of lines in the fibers of `V`, as a scheme over `X`. -/
noncomputable def AlgebraicGeometry.Scheme.projBundle {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] : CategoryTheory.Over X :=
  AlgebraicGeometry.Scheme.relativeProj (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V))

end
