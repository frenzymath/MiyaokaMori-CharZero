import MiyaokaMori.Prelude

/-! # Finite morphisms over a locally Noetherian base

Stacks Project, Tag 02OG: over a locally Noetherian base, a morphism is finite if and only if it is
proper with finite fibers (cf. the proof of Debarre, *Higher-Dimensional Algebraic Geometry*,
Prop. 7.3: "the corresponding map `F : P¹ × T → X × T` is finite").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.isFinite_of_isProper_of_finite_fibers
    {X S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (f : X ⟶ S) [AlgebraicGeometry.IsProper f]
    (hfib : ∀ s : S, (f.base ⁻¹' {s}).Finite) :
    AlgebraicGeometry.IsFinite f := by
  letI : AlgebraicGeometry.LocallyQuasiFinite f :=
    AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton f hfib
  exact AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite f

end
