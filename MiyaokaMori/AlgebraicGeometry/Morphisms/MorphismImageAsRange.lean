import MiyaokaMori.Prelude

/-! # The image of a morphism as a set

The image `f(C)` of a morphism of schemes is defined as the range of the underlying continuous
map, together with the characterization of its members.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

def AlgebraicGeometry.Scheme.Hom.setImage {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    Set Y := Set.range f.base

lemma AlgebraicGeometry.Scheme.Hom.mem_setImage {X Y : AlgebraicGeometry.Scheme.{u}}
    {f : X ⟶ Y} {y : Y} : y ∈ f.setImage ↔ ∃ x : X, f.base x = y := Iff.rfl

end
