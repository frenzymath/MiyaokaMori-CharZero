import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX

/-! # Lemmas on the scheme-level Chow group

The characterization of equality of classes in `AlgebraicGeometry.ChowGroup X p`
(`ChowGroup.mk_eq_mk_iff`), separated from the definition of the group. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

theorem AlgebraicGeometry.ChowGroup.mk_eq_mk_iff {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ}
    (α β : ↥(AlgebraicGeometry.cycleSubgroup X p)) :
    AlgebraicGeometry.ChowGroup.mk α = AlgebraicGeometry.ChowGroup.mk β ↔
      AlgebraicGeometry.RationallyEquivalent p (α : AlgebraicGeometry.AlgebraicCycle X ℤ) β := by
  change QuotientAddGroup.mk' _ α = QuotientAddGroup.mk' _ β ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  simp [AlgebraicGeometry.RationallyEquivalent, AddSubgroup.mem_addSubgroupOf]

end
