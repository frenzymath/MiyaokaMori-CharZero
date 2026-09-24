import MiyaokaMori.Prelude

/-! # Morphisms of finite type

A morphism of schemes is of finite type if it is locally of finite type and quasi-compact.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

class AlgebraicGeometry.IsOfFiniteType {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) : Prop
  extends AlgebraicGeometry.LocallyOfFiniteType f, AlgebraicGeometry.QuasiCompact f

end
