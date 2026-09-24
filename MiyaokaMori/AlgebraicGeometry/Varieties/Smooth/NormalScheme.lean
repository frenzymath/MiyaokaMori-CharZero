import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np

/-! # Normal schemes

A scheme is normal if all its local rings are integrally closed domains.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme is normal if every stalk is an integrally closed domain. -/
class AlgebraicGeometry.Scheme.IsNormal (X : AlgebraicGeometry.Scheme.{u}) : Prop where
  isDomain : ∀ x : X, IsDomain (X.presheaf.stalk x)
  integrallyClosed : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

end
