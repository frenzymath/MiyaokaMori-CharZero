import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver

/-! # Projective space over a field

The `N`-dimensional projective space `P^N_k := Proj k[x₀, …, x_N]` over a field `k`
(Stacks 01ND). It is an `abbrev` of the ring version `ProjectiveSpaceOver N k` at `R := k`, so
instance search and the keys of `rw`/`simp` see through it and consumers over a field can use the
lemmas of the ring version directly. The structure morphism and the `Over` instance are in
`ProjDegreeZeroIsoBase` and `ProjectiveSpaceStructureMorphism`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `P^N_k = Proj k[x₀,…,x_N]`, where `k[x₀,…,x_N]` carries the standard total-degree grading
`MvPolynomial.homogeneousSubmodule` (Stacks 01ND): the ring version `ProjectiveSpaceOver N k` at the
field `k`, as an `abbrev`. -/
noncomputable abbrev ProjectiveSpace (N : ℕ) (k : Type u) [Field k] : AlgebraicGeometry.Scheme.{u} :=
  ProjectiveSpaceOver N k

/-- `ProjectiveSpace N k` agrees with the ring version by definition. -/
theorem ProjectiveSpace_eq_projectiveSpaceOver (N : ℕ) (k : Type u) [Field k] :
    ProjectiveSpace N k = ProjectiveSpaceOver N k := rfl

end
