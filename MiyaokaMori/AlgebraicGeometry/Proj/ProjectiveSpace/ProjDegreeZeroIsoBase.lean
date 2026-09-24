import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-! # The structure morphism of `P^N_k` to `Spec k`

The degree-`0` part of the graded polynomial ring `k[X_0, …, X_N]` is `k`
(`MvPolynomial.homogeneousSubmoduleZeroRingEquiv`); this identifies the target `Spec 𝒜₀` of Mathlib's
`Proj.toSpecZero` with `Spec k`, giving the structure morphism `ProjectiveSpace.toSpecBase : P^N_k ⟶ Spec k`.
It is the field case of `ProjectiveSpaceOver.toSpecBase`, which is defined over any commutative ring.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure morphism `P^N_k → Spec k`: Mathlib's `Proj.toSpecZero` (with target `Spec 𝒜₀`) followed by
`Spec (k → 𝒜₀)` (an isomorphism, by `MvPolynomial.homogeneousSubmoduleZeroRingEquiv`); this is
`ProjectiveSpaceOver.toSpecBase N k` at `R := k`. -/
noncomputable abbrev ProjectiveSpace.toSpecBase (N : ℕ) (k : Type u) [Field k] :
    ProjectiveSpace N k ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
  ProjectiveSpaceOver.toSpecBase N k

/-- The structure morphism agrees with the definition over a general ring (by definition). -/
theorem ProjectiveSpace.toSpecBase_eq_over (N : ℕ) (k : Type u) [Field k] :
    ProjectiveSpace.toSpecBase N k = ProjectiveSpaceOver.toSpecBase N k := rfl

end
