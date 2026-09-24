import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.DimensionLtOfProperClosedIntegral
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurveIntegral
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Integral curves on a smooth projective curve

An integral curve (a one-dimensional integral closed subscheme) on a smooth projective curve `C`
is `C` itself: the only irreducible closed subset of dimension `1` of an irreducible curve is the
whole space.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IntegralCurve.range_eq_univ_of_curve {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (Γ : IntegralCurve k C.toScheme) : Set.range Γ.ι.base = Set.univ := by
  by_contra hne
  have hdim :=
    AlgebraicGeometry.Scheme.dimension_lt_of_isClosedImmersion_of_range_ne_univ
      (K := k) C.isProper Γ.ι hne
  have hCdim : C.toScheme.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    norm_num
  rw [Γ.carrier_dimension, hCdim] at hdim
  omega

end
