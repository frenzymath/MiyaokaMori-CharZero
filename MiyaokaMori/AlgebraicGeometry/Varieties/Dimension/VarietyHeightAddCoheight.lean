import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21

/-! # Height plus coheight on a variety

The dimension formula for varieties: every point `x` of a variety `X` over `k` satisfies
`dim closure {x} + dim O_{X,x} = dim X`, i.e. `height x + coheight x = dim X` ("dimension =
dimension minus codimension"; used to match the pushforward of cycles graded by dimension with
principal divisors defined in codimension `1`).

Sources: Stacks 02R5, 02RM, 02RH, 02RT, 02S2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `height x + coheight x = dim X` for every point of a variety. -/
theorem Variety.height_add_coheight {k : Type u} [Field k] (X : Variety k) (x : X.toScheme) :
    Order.height x + Order.coheight x = (X.toScheme.dimension : ℕ∞) := by
  have hd : topologicalKrullDim X.toScheme = ((X.toScheme.dimension : ℕ) : WithBot ℕ∞) :=
    Variety.dim_spec X
  exact AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := k)
    X.toScheme X.toScheme.dimension hd x

end
