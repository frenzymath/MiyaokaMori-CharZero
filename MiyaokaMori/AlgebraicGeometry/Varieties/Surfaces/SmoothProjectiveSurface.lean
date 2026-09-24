import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # Smooth projective surfaces

A smooth projective surface is a smooth projective variety of dimension `2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A smooth projective surface over `k`: a smooth projective variety of dimension `2`. -/
structure SmoothProjectiveSurface (k : Type u) [Field k] where
  toSmoothProjectiveVariety : SmoothProjectiveVariety k
  dim_eq_two : toSmoothProjectiveVariety.toVariety.dim = 2

end
