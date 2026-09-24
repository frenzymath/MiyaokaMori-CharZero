import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # The group of `i`-cycles of a variety

The group `Z_i(X)` of `i`-cycles: the additive subgroup of algebraic cycles supported on points of
dimension exactly `i`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Scheme version: the group of `i`-cycles `Z_i(X) = AlgebraicGeometry.cycleSubgroup X i` consists of the
   algebraic cycles supported on points of `height = i` (a point `x` ↔ the integral closed subscheme
   `closure{x}`, with `dim closure{x} = height x`). `cycleSubgroup` is the one definition of the
   `d`-cycles (declared in `AlgebraicCycles.lean`); `IsDimensionCycle X d α` is an abbrev for
   `α ∈ cycleSubgroup X d` and `DimensionCycle X d` for `↥(cycleSubgroup X d)`. The `pointClosureDimension`
   form of the membership condition is `AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension`. -/

/-- The group of `i`-cycles of a variety: the scheme-level `cycleSubgroup` of the underlying scheme
(an `abbrev`, not a second definition). -/
abbrev CycleGroup {k : Type u} [Field k] (X : Variety k) (i : ℕ) :
    AddSubgroup (AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) :=
  AlgebraicGeometry.cycleSubgroup X.toScheme i

end
