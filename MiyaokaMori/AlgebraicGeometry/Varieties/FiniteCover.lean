import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # Finite covers of curves

The paper's convention for finite covers: a finite surjective morphism between smooth connected
projective curves, ramification allowed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A finite cover of the smooth projective curve `C`: a smooth projective curve together with a
finite surjective `k`-morphism to `C`. -/
structure FiniteCover (k : Type u) [Field k] (C : SmoothProjectiveCurve k) where
  source : SmoothProjectiveCurve k
  hom : source.carrier ⟶ C.carrier
  isOver : hom ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    = source.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  [finite : AlgebraicGeometry.IsFinite hom]
  [surjective : AlgebraicGeometry.Surjective hom]

attribute [instance] FiniteCover.finite FiniteCover.surjective

/-- A finite cover sends the generic point to the generic point (finite surjective implies
dominant); hence `functionFieldDegree ρ.hom = [K(C̃) : K(C)]`. -/

theorem FiniteCover.hom_genericPoint {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (ρ : FiniteCover k C) :
    haveI := ρ.source.isIntegral; haveI := C.isIntegral
    ρ.hom.base (genericPoint ρ.source.carrier) = genericPoint C.carrier := by
  letI := ρ.source.isIntegral
  letI := C.isIntegral
  letI : AlgebraicGeometry.IsDominant ρ.hom := inferInstance
  exact AlgebraicGeometry.Scheme.dominantMap_genericPoint ρ.hom

end
