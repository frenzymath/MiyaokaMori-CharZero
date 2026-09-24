import MiyaokaMori.Prelude

/-! # Schemes over a base field

A `k`-scheme is a scheme `X` together with a structure morphism `X ⟶ Spec k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

abbrev SchemeOver (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u}) : Type u :=
  X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))

end
