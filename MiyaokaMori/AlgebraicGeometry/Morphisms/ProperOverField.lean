import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Schemes proper over a field

A `k`-scheme `X` is proper over `k` if its structure morphism `X ⟶ Spec k` is proper (separated,
universally closed and of finite type). This is just a name for Mathlib's `IsProper` applied to the
structure morphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

abbrev IsProperOver (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : Prop :=
  AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

end
