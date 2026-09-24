import MiyaokaMori.Prelude

/-! # Restriction of a morphism to a fiber via `fiberι`

Composing Mathlib's fiber inclusion `f.fiberι` with a morphism out of the total space gives the
restriction of that morphism to the fiber (used for the rulings of the resolved surface in
Corollary 4.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def fiberRestrict {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (Φ : X ⟶ Z) (π : X ⟶ Y) (y : Y) : (π.fiber y) ⟶ Z :=
  π.fiberι y ≫ Φ

end