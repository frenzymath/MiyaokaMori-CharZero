import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # One-dimensional schemes

The condition "the curve is one-dimensional": the topological Krull dimension of the underlying
space equals `1`. It is compatible with the dimension of a variety defined as the transcendence
degree of the function field (`schemeIsOneDimensional_iff_dim_eq_one`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A scheme is one-dimensional if its topological Krull dimension is `1`. -/
def SchemeIsOneDimensional (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  topologicalKrullDim X = 1

end