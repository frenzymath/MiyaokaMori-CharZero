import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # Support of a sheaf of modules

The support `Supp F = {x ∈ X | F_x ≠ 0}` of a sheaf of modules `F`, as a set of points of `X`
(no extra topological structure; when a dimension is needed, apply `topologicalKrullDim` to the
subspace).

Source: Stacks 01BA (sheaves of modules, support).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The support of `F`: the set of points at which the stalk of `F` is nontrivial. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.support {X : AlgebraicGeometry.Scheme.{u}}
    (F : X.Modules) : Set X :=
  {x | Nontrivial (F.stalk x)}

end
