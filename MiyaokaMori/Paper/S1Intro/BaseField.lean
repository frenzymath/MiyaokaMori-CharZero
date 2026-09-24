import MiyaokaMori.Prelude

/-! # The base field

The base field `k` of the paper: an algebraically closed field of characteristic zero. All schemes,
varieties and morphisms in the main theorem live over `k` (§1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An algebraically closed field of characteristic zero, packaged as a class. -/
class BaseField (k : Type u) extends Field k where
  [isAlgClosed : IsAlgClosed k]
  [charZero : CharZero k]

end
