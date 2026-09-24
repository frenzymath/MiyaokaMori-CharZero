import MiyaokaMori.Prelude

/-! # Connected schemes

The predicate "the underlying topological space of the scheme `X` is connected".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme is connected if its underlying topological space is connected. -/
def SchemeIsConnected (X : AlgebraicGeometry.Scheme.{u}) : Prop := ConnectedSpace X

end
