import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # An internal grading as an `AddSubgroup`-valued grading

Any `SetLike`-valued internal grading `𝒜 : ι → σ` (for example a `GradedAlgebra` with values in
`Submodule R A`) gives the `AddSubgroup`-valued version `GradedRing.addSubgroupGrading 𝒜` of the same
grading, which is again a `GradedRing` (the decomposition data are reused as they are; the
construction is constructive).

This is needed because the `grading` field of `Scheme.GradedAffineAlgebra` uniformly takes values in
`AddSubgroup` (the coefficient rings on the affine opens differ, so `Submodule Γ(X,U) _` cannot be
written as one type independent of `U`), whereas gradings at the ring level
(`BasedJetAlgebra.grading`, `MvPolynomial.weightedHomogeneousSubmodule`) are `Submodule`-valued. The
conversion here avoids writing it out by hand everywhere. The technique is the one used inside the
proof of Mathlib's `DirectSum.Decomposition.inductionOn` (the carriers are definitionally equal).
-/

set_option autoImplicit false

namespace GradedRing

variable {ι A σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)

/-- The same grading, with each piece regarded as an additive subgroup. -/
def addSubgroupGrading (i : ι) : AddSubgroup A where
  carrier := {x | x ∈ 𝒜 i}
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

@[simp] theorem mem_addSubgroupGrading {i : ι} {x : A} :
    x ∈ addSubgroupGrading 𝒜 i ↔ x ∈ 𝒜 i := Iff.rfl

/-- The `AddSubgroup`-valued version is still a graded ring. -/
@[reducible] def addSubgroup [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] : GradedRing (addSubgroupGrading 𝒜) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem := fun _ _ _ _ ha hb => SetLike.GradedMul.mul_mem (A := 𝒜) ha hb
  decompose' := DirectSum.decompose 𝒜
  left_inv := fun _ => (DirectSum.decompose 𝒜).left_inv _
  right_inv := fun _ => (DirectSum.decompose 𝒜).right_inv _

end GradedRing
