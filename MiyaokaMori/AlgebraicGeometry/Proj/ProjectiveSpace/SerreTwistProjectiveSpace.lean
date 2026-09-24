import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # The Serre twisting sheaf on projective space

The Serre twisting sheaf `O_{P^N}(m)` on `P^N` (the line bundle `O_X(1)` of §2 of the paper is its
restriction to `X ⊂ P^N`). The graded ring is written directly as
`MvPolynomial.homogeneousSubmodule (Fin (N+1)) k`; this is the only definition of `O_{P^N}(m)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `O_{P^N}(m)`: the twisting sheaf of homogeneous fractions `MiyaokaMori.WeightedJets.ProjTwisting.sheaf 𝒜 m`
on `Proj 𝒜`, for `𝒜 = k[x_0,…,x_N]` with the standard grading. -/
noncomputable def projectiveSpaceTwist (k : Type u) [Field k] (N : ℕ) (m : ℤ) :
    (ProjectiveSpace N k).Modules :=
  MiyaokaMori.WeightedJets.ProjTwisting.sheaf (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) m

end
