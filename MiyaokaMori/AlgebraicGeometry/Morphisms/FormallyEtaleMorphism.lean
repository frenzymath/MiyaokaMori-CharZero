import MiyaokaMori.Prelude

/-! # Formally étale morphisms

A morphism is formally étale if, for every square-zero extension, lifts exist and are unique
(used for the jet transition, §2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

class AlgebraicGeometry.FormallyEtale {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) : Prop where
  formallyEtale_appLE (f) :
    ∀ {U : Y.Opens} (_ : AlgebraicGeometry.IsAffineOpen U) {V : X.Opens}
      (_ : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FormallyEtale

end
