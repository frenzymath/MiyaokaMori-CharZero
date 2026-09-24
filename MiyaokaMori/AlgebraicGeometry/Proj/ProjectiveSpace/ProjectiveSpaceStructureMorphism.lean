import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjDegreeZeroIsoBase
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-! # The structure morphism of projective space over a field

The structure morphism `P^N_k → Spec k` (Mathlib's `Proj.toSpecZero` lands in `Spec 𝒜₀`, which has to
be identified with `Spec k`) and its properness (Stacks 01NE / 01WC). All schemes and morphisms of
the paper live over the base field `k` (§1 of the paper).

`ProjectiveSpace N k ↘ Spec (CommRingCat.of k)` is the one spelling of the structure morphism; the
`Over` instance is the ring version `ProjectiveSpaceOver.over N k` (instance search sees through the
`abbrev` `ProjectiveSpace N k = ProjectiveSpaceOver N k`), and the properness instance is the value of
the ring-version theorem `ProjectiveSpaceOver.isProper_toSpecBase` at `R := k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/- The structure morphism `ProjectiveSpace.toSpecBase N k : ProjectiveSpace N k ⟶ Spec k` is defined in
   `ProjDegreeZeroIsoBase` (an `abbrev` of the ring version `ProjectiveSpaceOver.toSpecBase N k`); the
   `Over` instance is the ring version `ProjectiveSpaceOver.over N k`. -/

/-- The instance of `(ProjectiveSpace N k).Over (Spec k)` is the ring-version instance (by definition). -/
theorem ProjectiveSpace.over_eq_over (N : ℕ) (k : Type u) [Field k] :
    (inferInstance : (ProjectiveSpace N k).Over (AlgebraicGeometry.Spec (CommRingCat.of k))) =
      ProjectiveSpaceOver.over N k := rfl

/-- `k → (k[x₀..x_N])₀` is bijective (the constants are exactly the degree-zero homogeneous part):
the ring version `ProjectiveSpaceOver.algebraMap_zero_bijective` at `R := k`. -/
theorem ProjectiveSpace.algebraMap_zero_bijective (N : ℕ) (k : Type u) [Field k] :
    Function.Bijective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) :=
  ProjectiveSpaceOver.algebraMap_zero_bijective N k

/-- The structure morphism is proper (Stacks 01NE): `Proj.toSpecZero 𝒜` is proper for a graded
`𝒜₀`-algebra `𝒜` of finite type (Mathlib instance), and composing with the isomorphism
`Spec (k → 𝒜₀)` preserves properness. This is the ring-version theorem
`ProjectiveSpaceOver.isProper_toSpecBase` at `R := k`, registered as a global instance over a field. -/
instance ProjectiveSpace.isProper_toSpecBase (N : ℕ) (k : Type u) [Field k] :
    AlgebraicGeometry.IsProper (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ProjectiveSpaceOver.isProper_toSpecBase N k

end
