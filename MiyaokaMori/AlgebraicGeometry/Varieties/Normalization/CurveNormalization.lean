import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.CyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationFunctionField
import MiyaokaMori.AlgebraicGeometry.Morphisms.RegularImpliesSmoothOverPerfectField
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.FiniteNormalizationOfPerfectCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.NormalizationPushforwardFundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.Stacks035l
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0ecg
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks0bx2
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfClosedSubscheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfFiniteOverProjective
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.Stacks0bxs

/-! # Normalization of an integral curve

The normalization of an integral curve `Γ` in a smooth projective variety `X`: a smooth
projective curve `C̃` with a finite morphism `ν : C̃ → X` such that `ν_*[C̃] = [Γ]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The normalization of `Γ`: `AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ K(Γ)` (Mathlib's relative
normalization `(Spec K(Γ) → Γ).normalization`, the relative `Spec` of the integral closure of `O_Γ`
in `K(Γ)`). The `k`-structure is `ν₀ ≫ Γ.ι ≫ (X → Spec k)`; smoothness, projectivity and
one-dimensionality are proof obligations: normal of dimension one implies regular (Stacks 0BX2),
regular over a perfect field implies smooth, and finiteness of the normalization (Stacks 0BXS)
together with projectivity of `Γ` gives projectivity; connectedness holds since the scheme is
integral. -/

noncomputable def integralCurveNormalization {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) : SmoothProjectiveCurve k where
  carrier := AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField
  «over» := ⟨(AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι) ≫
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  smooth := by
    letI : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField).Over
        (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι) ≫
        (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField) :=
      integralCurveNormalizationMap_isFinite Γ
    letI : AlgebraicGeometry.IsOfFiniteType
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      change AlgebraicGeometry.IsOfFiniteType
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι ≫
          (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      exact { toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    letI : AlgebraicGeometry.IsLocallyNoetherian
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField) := by
      apply AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))
    letI : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField).IsNormal := by
      letI : (AlgebraicGeometry.Spec (CommRingCat.of Γ.carrier.functionField)).IsNormal :=
        AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed _
      change (AlgebraicGeometry.Scheme.Hom.normalization
        (AlgebraicGeometry.Scheme.Covers.curveExtensionGenericMap Γ.carrier Γ.carrier.functionField)).IsNormal
      apply AlgebraicGeometry.Scheme.Hom.normalization_isNormal
    apply (isSmoothOver_iff_regular
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField)).mpr
    apply AlgebraicGeometry.Scheme.isRegular_of_isNormal_of_dim_le_one
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField)]
    exact le_of_eq Γ.dim_eq_one
  projective := by
    letI : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField).Over
        (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι) ≫
        (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField) :=
      integralCurveNormalizationMap_isFinite Γ
    letI : AlgebraicGeometry.IsOfFiniteType
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      change AlgebraicGeometry.IsOfFiniteType
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι ≫
          (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      exact { toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    letI : AlgebraicGeometry.IsProper
        (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := Γ.isProperOver
    letI : AlgebraicGeometry.IsProper
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      change AlgebraicGeometry.IsProper
        (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫
          (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      infer_instance
    haveI : (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField).IsOver
        (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨(Category.assoc _ _ _).symm⟩
    haveI : Γ.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    exact IsProjectiveOver.of_isFinite
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField)
      (IsProjectiveOver.of_isClosedImmersion Γ.ι X.projective)
  connected := AlgebraicGeometry.Scheme.Covers.curveFieldNormalization_connected Γ.carrier Γ.carrier.functionField
  dim_one := by
    change topologicalKrullDim
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ.carrier Γ.carrier.functionField) = 1
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField)]
    exact Γ.dim_eq_one

/- ν : Γ^ν → Γ ↪ X -/

/-- The finite morphism `ν : Γ^ν → X` from the normalization of `Γ` to the ambient variety. -/
noncomputable def integralCurveNormalization.nu {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) :
    (integralCurveNormalization Γ).toScheme ⟶ X.toScheme :=
  AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField ≫ Γ.ι

/- `nu` is a `k`-morphism: the `k`-structure of `Γ^ν` is by definition `nu ≫ (X → Spec k)`. -/

instance integralCurveNormalization.nu_isOver {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) :
    (integralCurveNormalization.nu Γ).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨rfl⟩

theorem integralCurveNormalization_pushforward {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) :
    curveCycleClassPushforward (integralCurveNormalization.nu Γ) = Γ.fundamentalClass := by
  exact curveFieldNormalization_cyclePushforward_fundamentalClass Γ
    (integralCurveNormalization Γ) (integralCurveNormalization.nu Γ) rfl rfl

theorem integralCurveNormalization_nonconstant {k : Type u} [Field k] [PerfectField k]
    {X : SmoothProjectiveVariety k} (Γ : IntegralCurve k X.toScheme) :
    ¬ IsConstantMorphism (integralCurveNormalization.nu Γ) := by
  intro hconst
  obtain ⟨y, hy⟩ := hconst
  have hνsurj : Function.Surjective
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField).base :=
    (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ.carrier Γ.carrier.functionField).surjective
  have hΓinj : Function.Injective Γ.ι.base :=
    (Γ.ι.isClosedEmbedding.isEmbedding).injective
  have hsub : Subsingleton Γ.carrier := by
    constructor
    intro a b
    apply hΓinj
    obtain ⟨a', ha'⟩ := hνsurj a
    obtain ⟨b', hb'⟩ := hνsurj b
    rw [← ha', ← hb']
    exact (hy a').trans (hy b').symm
  letI : Subsingleton Γ.carrier := hsub
  have hle : topologicalKrullDim Γ.carrier ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology Γ.carrier
  have hdim := Γ.dim_eq_one
  rw [hdim] at hle
  norm_num at hle

end
