import MiyaokaMori.Prelude

/-! # Colimits in the category of commutative groups

The category `CommGrpCat` of (multiplicatively written) commutative groups has all small colimits,
transported from the additive version along `CommGrpCat ≌ AddCommGrpCat`. This is what makes stalks
of `CommGrpCat`-valued sheaves (`TopCat.Presheaf.stalk` requires `HasColimits`) available, e.g. the
stalks of `𝒦^*/O^*` in the theory of Cartier divisors.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `CommGrpCat` has all small colimits (transported from `AddCommGrpCat`). -/
instance CommGrpCat.hasColimits : CategoryTheory.Limits.HasColimits CommGrpCat.{u} :=
  CategoryTheory.Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor

end
