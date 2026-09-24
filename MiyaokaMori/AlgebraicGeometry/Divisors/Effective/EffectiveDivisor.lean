import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs

/-! # Effective Cartier divisors on a variety and their supports

Effectivity of a Cartier divisor (all Weil coefficients nonnegative) and its support; used for the
generators of the pseudo-effective cone and the fact that a general member of a covering family is
not contained in the support (proof of Theorem 1.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A Cartier divisor is effective if all coefficients of its Weil cycle are nonnegative. -/
def CartierDivisor.Effective {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : Prop :=
  ∀ p : X.toScheme, 0 ≤ (CartierDivisor.weilCycle X D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) p

/-- The support of a Cartier divisor: the points where its Weil cycle is nonzero. -/
def CartierDivisor.support {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : Set X.toScheme :=
  {p | (CartierDivisor.weilCycle X D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) p ≠ 0}

/-- The support of a Cartier divisor on a variety is finite. -/
theorem CartierDivisor.support_finite {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : (CartierDivisor.support D).Finite := by
  change (Function.support
    ((CartierDivisor.weilCycle X D : CycleGroup X (X.toScheme.dimension - 1)) :
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)).Finite
  have hlocal : LocallyFiniteSupport
      (((CartierDivisor.weilCycle X D : CycleGroup X (X.toScheme.dimension - 1)) :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) : X.toScheme → ℤ) :=
    Function.locallyFinsupp.locallyFiniteSupport _
  simpa only [Set.univ_inter] using
    (LocallyFiniteSupport.finite_inter_support_of_isCompact hlocal
      (W := Set.univ) isCompact_univ)

/-- The sum of effective divisors is effective. -/
theorem CartierDivisor.Effective.add {k : Type u} [Field k] {X : Variety k}
    {D E : CartierDivisor X} (hD : CartierDivisor.Effective D) (hE : CartierDivisor.Effective E) :
    CartierDivisor.Effective (D + E) := by
  intro p
  rw [CartierDivisor.weilCycle_add]
  exact add_nonneg (hD p) (hE p)

end
