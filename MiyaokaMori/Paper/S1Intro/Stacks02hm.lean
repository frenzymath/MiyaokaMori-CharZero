import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.FormallyEtaleMorphism

/-! # Étale morphisms are formally étale

The direction (1) ⇒ (2) of Stacks 02HM: an étale morphism of schemes is formally étale.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An étale morphism is formally étale (Stacks 02HM, (1) ⇒ (2)). -/
theorem AlgebraicGeometry.formallyEtale_of_etale {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] : AlgebraicGeometry.FormallyEtale f := by
  constructor
  intro U hU V hV e
  exact (f.etale_appLE hU hV e).formallyEtale

end
