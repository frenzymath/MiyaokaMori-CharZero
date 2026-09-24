import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionClosedPointStalk
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyLocalDimensionEqDim
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s

/-! # Local rings of a smooth projective surface at closed points

The local ring of a smooth projective surface at a closed point is a two-dimensional regular local
ring (the hypothesis of Stacks 0AGQ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The stalk of a smooth projective surface at a closed point is a regular local ring of dimension
`2`. -/
theorem SmoothProjectiveSurface.stalk_regular_dim_two {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsRegularLocalRing (S.toScheme.presheaf.stalk p) ∧
      ringKrullDim (S.toScheme.presheaf.stalk p) = 2 := by
  have hreg : AlgebraicGeometry.Scheme.IsRegular S.toScheme :=
    AlgebraicGeometry.isRegular_of_smoothOver S.toScheme
      S.toSmoothProjectiveVariety.smooth
  constructor
  · exact hreg.isRegularLocalRing_stalk p
  · rw [← localDimension_eq_ringKrullDim_stalk (k := k) S.toScheme p hp,
      Variety.localDimension_eq_dim S.toVariety p, S.dim_eq_two]
    norm_num

end
