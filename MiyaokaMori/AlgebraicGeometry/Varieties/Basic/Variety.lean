import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Varieties over a field

A variety over `k` is an integral, separated `k`-scheme of finite type, packaged as a structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A variety over `k`: an integral, separated scheme of finite type over `Spec k`. -/
structure Variety (k : Type u) [Field k] where
  carrier : AlgebraicGeometry.Scheme.{u}
  [«over» : carrier.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  [integral : AlgebraicGeometry.IsIntegral carrier]
  [separated : AlgebraicGeometry.IsSeparated (carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
  [finiteType : AlgebraicGeometry.IsOfFiniteType (carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- The underlying scheme of a variety. -/

abbrev Variety.toScheme {k : Type u} [Field k] (X : Variety k) : AlgebraicGeometry.Scheme.{u} :=
  X.carrier

attribute [instance] Variety.over Variety.integral Variety.separated Variety.finiteType

/-- The structure morphism `X ⟶ Spec k` of a variety (also available for `SmoothProjectiveVariety`
through `extends`). -/

abbrev Variety.structureMorphism {k : Type u} [Field k] (X : Variety k) :
    X.carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
  X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)

end
