import MiyaokaMori.AlgebraicGeometry.Morphisms.RegularSchemeSmoothOverPerfectField
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s

/-! # Regular implies smooth over a perfect field

A scheme of finite type over a perfect field (e.g. of characteristic zero) is smooth if and only if
it is regular. This is used to see that the normalization of a curve is a smooth projective curve.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem isSmoothOver_iff_regular {k : Type u} [Field k] [PerfectField k]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] :
    IsSmoothOver k Y ↔ AlgebraicGeometry.Scheme.IsRegular Y := by
  constructor
  · exact AlgebraicGeometry.isRegular_of_smoothOver Y
  · exact isSmoothOver_of_regular_over_perfectField Y

end
