import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism

/-! # The projective line

The projective line `P^1_k`, i.e. the projective space `Proj k[x, y]` with `N = 1`, together with its
structure morphism to `Spec k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable abbrev ProjectiveLine (k : Type u) [Field k] : AlgebraicGeometry.Scheme.{u} :=
  ProjectiveSpace 1 k

end
