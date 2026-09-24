import MiyaokaMori.Prelude

/-! # Open complement of a closed immersion

The image of a closed immersion is closed; its complement is an open subscheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The open subscheme of `Y` complementary to the image of a closed immersion `i : Z ⟶ Y`. -/
noncomputable def AlgebraicGeometry.Scheme.complementOfClosedImmersion
    {Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) [AlgebraicGeometry.IsClosedImmersion i] :
    Y.Opens :=
  ⟨(Set.range i.base)ᶜ, (AlgebraicGeometry.IsClosedImmersion.base_closed (f := i)).isClosed_range.isOpen_compl⟩

end
