import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qt

/-! # The cycle of a closed subscheme (Stacks 02QU)

Stacks 02QU: the `k`-cycle `[Z]_k = Σ m_{Z',Z}[Z']` of a closed subscheme `Z ⊂ X`, the sum running over
the `k`-dimensional irreducible components `Z'` of `Z`, with multiplicities
`m_{Z',Z} = length_{O_{X,ξ}} O_{Z,ξ}` (`ξ` the generic point of `Z'`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `k`-cycle `[Z]_k := ι_*([Z]_k^Z)` of the closed subscheme `Z = I.subscheme`: the `k`-dimensional
fundamental cycle of `Z` pushed forward along the closed immersion (with
`AlgebraicGeometry.AlgebraicCycle.properPushforward`, weights `Order.height`; a closed immersion
pushes forward with coefficient `1`). Only `X` locally Noetherian is required; `Z` is then locally
Noetherian since a closed immersion is locally of finite type. -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.cycle {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData) (k : ℕ) :
    AlgebraicGeometry.AlgebraicCycle X ℤ :=
  haveI : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι (I.subscheme.fundamentalCycle k)

end
