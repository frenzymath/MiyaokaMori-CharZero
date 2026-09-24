import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX

/-! # The Chow group of a scheme

The Chow group `A_p(X)`: `p`-dimensional cycles modulo rational equivalence. This module is the
**only** definition of the Chow group; the Chow group `ChowGroup (X : Variety k) i` of a variety is an
`abbrev` of `AlgebraicGeometry.ChowGroup X.toScheme i`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Chow group `A_p(X) = Z_p(X) / Rat_p(X)` of `p`-cycles modulo rational equivalence. -/
def AlgebraicGeometry.ChowGroup (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) : Type u :=
  ↥(AlgebraicGeometry.cycleSubgroup X p) ⧸
    (AlgebraicGeometry.ratEquivZero X p).addSubgroupOf (AlgebraicGeometry.cycleSubgroup X p)

noncomputable instance (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    AddCommGroup (AlgebraicGeometry.ChowGroup X p) := inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- The class of a `p`-cycle in the Chow group. -/
noncomputable def AlgebraicGeometry.ChowGroup.mk {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} :
    ↥(AlgebraicGeometry.cycleSubgroup X p) →+ AlgebraicGeometry.ChowGroup X p :=
  QuotientAddGroup.mk' _

end