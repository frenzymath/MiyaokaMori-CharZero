import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree

/-! # Intersection number of a divisor with a one-cycle

The intersection number `D · Z ∈ ℤ` of a divisor with a one-cycle: take `D ∩ Z ∈ A_0(X)` and then
its degree (the number `-K_X · f_*[C]` of Theorem 1.1 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The intersection number `D · Z := deg(D ∩ Z)` of a Cartier divisor with a one-cycle. -/
noncomputable def intersectionNumber {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (D : CartierDivisor X.toVariety)
    (Z : OneCycle X.toVariety) : ℤ :=
  ChowGroup.degree X (capDivisor D 0 Z)

/- Notation `D ⬝ Z` for the intersection number (`⬝` is U+2B1D). We do not use `·`: it is Lean's cdot
   notation, so `(D · Z)` would also parse as `fun x => D x Z` and report "Ambiguous notation in cdot
   function" inside parentheses. Left associative, precedence 70 (like `*`), right argument at 71. -/

notation:70 D:70 " ⬝ " Z:71 => intersectionNumber _ D Z

end
