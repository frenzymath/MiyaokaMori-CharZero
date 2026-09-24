import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Rational points

A name for the `k`-rational points of a `k`-scheme, which Mathlib only has as an inline subtype,
expressed with the `↘` notation of `Scheme.Over`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `k`-rational points of `X`: sections `p : Spec k ⟶ X` of the structure morphism
`X ↘ Spec k` (`p ≫ (X ↘ Spec k) = 𝟙`). -/
def AlgebraicGeometry.Scheme.rationalPoint (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : Type u :=
  {p : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X //
    p ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) = 𝟙 _}

end
