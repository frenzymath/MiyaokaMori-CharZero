import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestrictComp

/-! # Restricting a morphism to a fiber

Restriction of a morphism `Φ : S ⟶ X` to one fiber of `π : S ⟶ C`:
`fiberRestrict Φ π y : π⁻¹(y) ⟶ X`. Used for the general fiber of the resolved ruled surface
(Corollary 4.3 and Lemma 5.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem fiberRestrict_eq {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (Φ : X ⟶ Z) (π : X ⟶ Y) (y : Y) :
    fiberRestrict Φ π y = π.fiberι y ≫ Φ :=
  rfl

end
