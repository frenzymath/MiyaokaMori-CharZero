import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Smooth rational curves

A smooth rational curve is an integral curve which is isomorphic to `P¹` as a `k`-scheme (the
ambient `X` is an arbitrary `k`-scheme).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An integral curve is smooth rational if it is isomorphic to `P¹_k` as a `k`-scheme. -/
def IntegralCurve.IsSmoothRational {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) : Prop :=
  ∃ e : Γ.carrier ≅ ProjectiveLine k,
    e.hom ≫ (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)

end
