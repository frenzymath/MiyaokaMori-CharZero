import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # Regular schemes

A scheme is regular if all its local rings are regular local rings. Over an algebraically closed
field of characteristic zero, smooth is equivalent to regular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme is regular if every stalk is a regular local ring. -/
class AlgebraicGeometry.Scheme.IsRegular (X : AlgebraicGeometry.Scheme.{u}) : Prop where
  [locallyNoetherian : AlgebraicGeometry.IsLocallyNoetherian X]
  isRegularLocalRing_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

end
