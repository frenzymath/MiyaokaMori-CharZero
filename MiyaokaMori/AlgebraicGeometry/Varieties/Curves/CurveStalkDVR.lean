import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.RingTheory.OrderOfVanishing.RegularLocalRingDVR
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ClosedPointCoheightOne

/-! # Stalks of a smooth projective curve are discrete valuation rings

On a smooth projective curve, a closed point has coheight `1`, and the stalk at a point of
coheight `1` is a discrete valuation ring. These are the two prerequisites for connecting
`Scheme.ord` on a curve with `AlgebraicGeometry.Divisors.CurveStalkValuation.valuation`.

The DVR statement only needs coheight `1`, not closedness. The stalks of a one-dimensional
smooth scheme are computed directly to be domains and PIDs, and `ringKrullDim = coheight = 1`
shows they are not fields.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry Order

/-- A closed point of a smooth projective curve has coheight `1`. -/
theorem SmoothProjectiveCurve.coheight_eq_one_of_isClosed {k : Type u} [Field k]
    (Ct : SmoothProjectiveCurve k) (z : Ct.toScheme) (hz : IsClosed ({z} : Set Ct.toScheme)) :
    coheight z = 1 :=
  AlgebraicGeometry.Scheme.closedPoint_coheight_eq_one_of_dimension_one Ct.toScheme Ct.dim_one z hz

/-- The stalk of a smooth projective curve at a point of coheight `1` is a discrete valuation
ring: in dimension one the stalk is a domain and a PID
(`Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one`), and coheight `1` gives Krull
dimension `1`, so the stalk is not a field. -/
theorem SmoothProjectiveCurve.isDiscreteValuationRing_stalk {k : Type u} [Field k]
    (Ct : SmoothProjectiveCurve k) (z : Ct.toScheme) (hz : coheight z = 1) :
    IsDiscreteValuationRing (Ct.toScheme.presheaf.stalk z) := by
  have hsm : AlgebraicGeometry.Smooth (Ct.toScheme ↘ Spec (CommRingCat.of k)) := Ct.smooth
  obtain ⟨hdom, hpid⟩ :=
    AlgebraicGeometry.Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one
      (Ct.toScheme ↘ Spec (CommRingCat.of k)) (le_of_eq Ct.dim_one) z
  have hstalk : ringKrullDim (Ct.toScheme.presheaf.stalk z) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z, hz]
    norm_num
  refine { not_a_field' := fun hbot => ?_ }
  have hfield : IsField (Ct.toScheme.presheaf.stalk z) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
  rw [ringKrullDim_eq_zero_of_isField hfield] at hstalk
  exact zero_ne_one hstalk
