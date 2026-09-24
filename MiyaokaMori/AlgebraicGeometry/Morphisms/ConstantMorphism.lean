import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismImageAsRange

/-! # Constant morphisms

A morphism of schemes is constant if the image of its underlying map is a single point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def IsConstantMorphism {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ y : Y, ∀ x : X, f.base x = y

end
