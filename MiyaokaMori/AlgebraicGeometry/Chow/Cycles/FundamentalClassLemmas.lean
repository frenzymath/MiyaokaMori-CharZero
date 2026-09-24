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
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.SeedCyclePushforwardClosedImmersionComposition

/-! # Lemmas on the fundamental class of a closed subvariety

The fundamental class of a closed subvariety is the single point cycle at its generic point
(`ClosedSubvariety.fundamentalClass_eq_single`); separated from the definition of the
fundamental class. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

open Classical in

theorem ClosedSubvariety.fundamentalClass_eq_single {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) :
    (V.fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) =
      Function.locallyFinsuppWithin.single (V.ι.base (genericPoint V.carrier)) (1 : ℤ) := by
  letI : V.carrier.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨V.ι ≫ X.structureMorphism⟩
  letI : AlgebraicGeometry.IsLocallyNoetherian V.carrier := by
    change AlgebraicGeometry.IsLocallyNoetherian V.toVariety.toScheme
    exact V.toVariety.isLocallyNoetherian
  letI : AlgebraicGeometry.IsNoetherian V.carrier := by
    change AlgebraicGeometry.IsNoetherian V.toVariety.toScheme
    exact V.toVariety.isNoetherian
  letI : AlgebraicGeometry.IsSeparated
      (V.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsSeparated V.toVariety.structureMorphism
    exact V.toVariety.separated
  letI : AlgebraicGeometry.IsOfFiniteType
      (V.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsOfFiniteType V.toVariety.structureMorphism
    exact V.toVariety.finiteType
  unfold ClosedSubvariety.fundamentalClass
  have hfund := AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral_of_isOfFiniteType
    (k := k) V.carrier
  have hcycle :
      (AlgebraicGeometry.Intersection.dimensionFundamentalCycle V.carrier V.dimension).1 =
        Function.locallyFinsuppWithin.single (genericPoint V.carrier) (1 : ℤ) := by
    apply DFunLike.ext
    intro z
    rw [AlgebraicGeometry.Intersection.dimensionFundamentalCycle_apply]
    have hz := congrFun hfund z
    simpa [AlgebraicGeometry.Scheme.fundamentalCycle,
      Function.locallyFinsuppWithin.single_apply] using hz
  change AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
      (AlgebraicGeometry.Intersection.dimensionFundamentalCycle V.carrier V.dimension).1 = _
  rw [hcycle]
  apply DFunLike.ext
  intro y
  by_cases hy : y = V.ι.base (genericPoint V.carrier)
  · subst y
    rw [AlgebraicGeometry.Intersection.closedImmersion_properPushforward_apply_image]
    simp [Function.locallyFinsuppWithin.single_apply]
  · rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply]
    simp only [Function.locallyFinsuppWithin.single_apply, hy, if_false]
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    by_cases hzg : z = genericPoint V.carrier
    · subst z
      have hxy : V.ι.base (genericPoint V.carrier) ≠ y := fun h => hy h.symm
      simp [hxy]
    · simp [hzg]

end
