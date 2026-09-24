import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace

/-! # Homogeneous coordinates of projective space

The homogeneous coordinates `x_i ∈ Γ(P^N, O(1))` of `P^N_k`; for a morphism `f : X → P^N` the
homogeneous coordinate sections of `f` are `f_ℓ = f^* x_ℓ` (§1 of the paper).

`projectiveSpaceCoordinate` is the only definition of the homogeneous coordinates; the section over
an arbitrary open `U` is the restriction of the global section,
`(projectiveSpaceTwist k N 1).presheaf.map (homOfLE le_top).op (projectiveSpaceCoordinate k N i)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous coordinate `x_i ∈ Γ(P^N, O(1))`: the global section `X_i / 1` given by the
degree-one homogeneous element `X i`. -/
noncomputable def projectiveSpaceCoordinate (k : Type u) [Field k] (N : ℕ) (i : Fin (N + 1)) :
    ((projectiveSpaceTwist k N 1).val.obj (Opposite.op ⊤) : Type u) :=
  MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) 1
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) ⊤

end
