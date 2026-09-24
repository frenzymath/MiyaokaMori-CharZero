import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # The fundamental class of a closed subvariety

The fundamental class `[V] ∈ Z_{dim V}(X)` of a closed subvariety `V`: the cycle with coefficient `1`
at the generic point of `V` and `0` elsewhere (the class `[C]` of Theorem 1.1 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A variety (of finite type over a field) is a Noetherian scheme: locally Noetherian (of finite type
over the Noetherian `Spec k`) and quasi-compact. -/
theorem Variety.isNoetherian {k : Type u} [Field k] (X : Variety k) :
    AlgebraicGeometry.IsNoetherian X.toScheme :=
  haveI : AlgebraicGeometry.IsLocallyNoetherian X.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  haveI : CompactSpace X.toScheme := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
    (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The fundamental class `[V]`: the `d`-dimensional fundamental cycle `dimensionFundamentalCycle V d`
(`d = dim V`) pushed forward along the closed immersion `V.ι` by `dimensionProperPushforward`
(`AlgebraicGeometry.AlgebraicCycle.properPushforward` restricted to `Z_d`); it lies in `Z_{dim V}(X)`
by the type of the pushforward. Since `V` is integral, the length at the generic point is `1` and the
residue degree of the pushforward is `1`, so this is the cycle with coefficient `1` at the image of
the generic point of `V` (`fundamentalClass_eq_single`). -/
noncomputable def ClosedSubvariety.fundamentalClass {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) : CycleGroup X V.dimension :=
  haveI : AlgebraicGeometry.IsNoetherian V.carrier := V.toVariety.isNoetherian
  (AlgebraicGeometry.Intersection.dimensionProperPushforward V.ι V.dimension
      (AlgebraicGeometry.Intersection.dimensionFundamentalCycle V.carrier V.dimension))

end
