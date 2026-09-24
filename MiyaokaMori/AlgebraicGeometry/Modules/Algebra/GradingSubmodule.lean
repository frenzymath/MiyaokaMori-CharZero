import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedAffineAlgebra
import MiyaokaMori.RingTheory.GradedRing.GradedRingAddSubgroup

/-! # Algebra structures and graded submodules of the sections of affine algebras

Two small connecting pieces used by every module doing algebra on affine opens:

* `AffineAlgebra.sectionsAlgebra A U : Algebra Γ(X,U) (A.sections U)` (structure map `unitHom`, a
  **global instance**): without it the types `A(U) ⊗_{Γ(X,U)} B(U)`, `Submodule Γ(X,U) (A(U))` cannot be
  written.
* `GradedAffineAlgebra.gradingSubmodule S U m : Submodule Γ(X,U) (S(U))`: the `Submodule` version of
  `S.grading U m` (`unit` lands in degree `0`, so each piece is automatically a `Γ(X,U)`-submodule),
  with the `GradedRing` instance `instGradedRingSubmodule` (same carrier, decomposition data reused,
  constructive). The field `GradedAffineAlgebra.grading` is `AddSubgroup`-valued (the coefficient
  rings differ between affine opens, so `Submodule Γ(X,U) _` is not a type independent of `U`), while
  Mathlib's results on tensor products, base change and `DirectSum.decomposeTensor` need
  `Submodule`-valued gradings; hence this conversion.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- `A(U)` as a `Γ(X,U)`-algebra (the structure map is `A.unitHom U`). -/
@[instance_reducible] def AffineAlgebra.sectionsAlgebra (A : X.AffineAlgebra)
    (U : X.AffineZariskiSite) : Algebra Γ(X, U.toOpens) (A.sections U) :=
  (A.unitHom U).toAlgebra

attribute [instance] AffineAlgebra.sectionsAlgebra

@[simp] theorem AffineAlgebra.algebraMap_sections (A : X.AffineAlgebra) (U : X.AffineZariskiSite)
    (r : Γ(X, U.toOpens)) : algebraMap Γ(X, U.toOpens) (A.sections U) r = A.unitHom U r := rfl

namespace GradedAffineAlgebra

variable (S : X.GradedAffineAlgebra) (U : X.AffineZariskiSite)

/-- The graded pieces of `S` on `U` as `Γ(X,U)`-submodules (the structure map lands in degree `0`, so
each piece is a submodule). -/
def gradingSubmodule (m : ℕ) : Submodule Γ(X, U.toOpens) (S.toAffineAlgebra.sections U) where
  carrier := S.grading U m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c _ ha := by
    have h := SetLike.mul_mem_graded (A := S.grading U) (S.unit_mem U c) ha
    rw [zero_add] at h
    exact h

@[simp] theorem mem_gradingSubmodule {m : ℕ} {a : S.toAffineAlgebra.sections U} :
    a ∈ S.gradingSubmodule U m ↔ a ∈ S.grading U m := Iff.rfl

/-- The same grading, now `Submodule`-valued, is still a graded ring (decomposition data reused,
constructive). -/
instance instGradedRingSubmodule : GradedRing (S.gradingSubmodule U) where
  one_mem := SetLike.one_mem_graded (S.grading U)
  mul_mem _ _ _ _ ha hb := SetLike.mul_mem_graded (A := S.grading U) ha hb
  decompose' := DirectSum.decompose (S.grading U)
  left_inv _ := (DirectSum.decompose (S.grading U)).left_inv _
  right_inv _ := (DirectSum.decompose (S.grading U)).right_inv _

end GradedAffineAlgebra

end AlgebraicGeometry.Scheme

end
