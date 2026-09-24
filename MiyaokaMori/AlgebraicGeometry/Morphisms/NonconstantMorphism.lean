import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismImageAsRange

/-! # Nonconstant morphisms

A morphism `f : C ⟶ X` is nonconstant if the image of its underlying map is not a single point
(Theorem 1.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def IsNonconstantMorphism {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ¬ IsConstantMorphism f

end
