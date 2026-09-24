import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # Local dimension of a variety equals its dimension

Stacks 0A21 (3): an irreducible locally algebraic `k`-scheme has local dimension equal to its
global dimension at every point; for a variety `X`, `dim_x X = dim X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Untruncated form of Stacks 0A21 (3): for any point `x` of a variety `X`, the infimum of the Krull
dimensions of the open neighbourhoods of `x` (in `WithBot ℕ∞`, i.e. `localDimension` before
truncation) equals the Krull dimension of `X`. -/

theorem Variety.iInf_topologicalKrullDim_opens_eq {k : Type u} [Field k] (X : Variety k) (x : X.carrier) :
    (⨅ U ∈ {U : X.carrier.Opens | x ∈ U}, topologicalKrullDim U) = topologicalKrullDim X.carrier.carrier := by
  have : IrreducibleSpace X.carrier.carrier :=
    AlgebraicGeometry.irreducibleSpace_of_isIntegral X.carrier
  exact AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_of_irreducible (k := k) X.carrier x

/-- The `ℕ`-valued form, obtained by truncating both sides of the previous theorem. -/

theorem Variety.localDimension_eq_dim {k : Type u} [Field k] (X : Variety k) (x : X.carrier) :
    localDimension X.carrier x = X.dim := by
  unfold localDimension Variety.dim AlgebraicGeometry.Scheme.dimension
  rw [Variety.iInf_topologicalKrullDim_opens_eq]

end
