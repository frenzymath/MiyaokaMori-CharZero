import MiyaokaMori.Prelude

/-! # Rational extension of additive homomorphisms

An additive homomorphism `φ : M →+ N` (for instance between Chow groups) extends to a `ℚ`-linear
map `ℚ ⊗_ℤ M → ℚ ⊗_ℤ N`. This is how operators on Chow groups are extended to the rational Chow
groups `ChowGroupRat = ℚ ⊗_ℤ ChowGroup`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `ℚ`-linear extension `ℚ ⊗_ℤ M → ℚ ⊗_ℤ N` of an additive homomorphism `φ : M →+ N`. -/
noncomputable def AddMonoidHom.ratExtend {M N : Type u} [AddCommGroup M] [AddCommGroup N] (φ : M →+ N) :
    TensorProduct ℤ ℚ M →ₗ[ℚ] TensorProduct ℤ ℚ N :=
  LinearMap.baseChange ℚ φ.toIntLinearMap

end
