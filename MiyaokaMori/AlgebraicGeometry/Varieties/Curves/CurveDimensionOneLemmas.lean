import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne

/-! # One-dimensionality and the dimension of a variety

For a variety `X`, `SchemeIsOneDimensional X.carrier` is equivalent to `X.dim = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

theorem schemeIsOneDimensional_iff_dim_eq_one {k : Type u} [Field k] (X : Variety k) :
    SchemeIsOneDimensional X.carrier ↔ X.dim = 1 := by
  -- immediate from `Variety.dim_spec` (`topologicalKrullDim = dim`)
  rw [SchemeIsOneDimensional, Variety.dim_spec X]
  exact_mod_cast Iff.rfl

end
