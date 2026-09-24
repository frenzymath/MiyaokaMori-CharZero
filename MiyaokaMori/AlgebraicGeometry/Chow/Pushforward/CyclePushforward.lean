import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.SeedCycleGeometry
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Pushforward of the fundamental class of a curve

The pushforward `f_*[C] ∈ Z_1(X)` of the fundamental class of a curve `C` along `f : C → X`
(the one-cycle of Theorem 1.1 of the paper; Fulton, Intersection Theory, §1.4). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A `k`-morphism `C → X` is proper: `C` is proper over `k` (projective) and `X` is separated over `k`. -/
theorem SmoothProjectiveCurve.isProper_of_isOver {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.IsProper f := by
  have hX : AlgebraicGeometry.IsProper
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper X.projective
  have hC : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    IsProjectiveOver.isProper C.projective
  have hf : f ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    (inferInstance : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1
  have hcomp : AlgebraicGeometry.IsProper
      (f ≫ X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [hf]
    exact hC
  exact AlgebraicGeometry.IsProper.of_comp f (X.toScheme ↘
    AlgebraicGeometry.Spec (CommRingCat.of k))

/-- The one-cycle `f_*[C] = dimensionProperPushforward f 1 (dimensionFundamentalCycle C 1)`
(`AlgebraicGeometry.AlgebraicCycle.properPushforward` restricted to `Z_1`). `C` is Noetherian by its
variety structure, and a `DimensionCycle` is an element of `CycleGroup X 1`
(`DimensionCycle = ↥cycleSubgroup`). -/
noncomputable def curveCycleClassPushforward {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    OneCycle X.toVariety :=
  haveI : AlgebraicGeometry.IsProper f := SmoothProjectiveCurve.isProper_of_isOver f
  haveI : AlgebraicGeometry.IsNoetherian C.toScheme := C.toVariety.isNoetherian
  let α := AlgebraicGeometry.Intersection.dimensionProperPushforward f 1
      (AlgebraicGeometry.Intersection.dimensionFundamentalCycle C.toScheme 1)
  α

end
