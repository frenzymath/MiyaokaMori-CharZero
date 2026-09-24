import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti

/-! # The first Chern class of an invertible sheaf

The first Chern class `c_1(L)` of an invertible sheaf, as an operator on Chow groups lowering the
dimension by one (the class of a Cartier divisor). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The first Chern class `c_1(L) ∩ − : CH_d(X) → CH_{d-1}(X)`, descended to the Chow group
(Stacks 02TI): if `X` is locally Noetherian and locally of finite type over some field (the setting
of Stacks 02SJ), `d > 0`, and the cycle-level `c_1(L) ∩ −` sends rationally equivalent `d`-cycles to
the same class, then it factors through the quotient `Z_d(X) → CH_d(X)`; otherwise it is `0` (the
signature is stated for an arbitrary scheme). The condition tests the truth of Stacks 02TI, so the
map is always the correct one; the lemmas evaluating it need the hypotheses. -/
noncomputable def AlgebraicGeometry.firstChernClass {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) :
    AlgebraicGeometry.ChowGroup X d →+ AlgebraicGeometry.ChowGroup X (d - 1) :=
  open Classical in
  if h : 0 < d ∧ ∃ (_ : AlgebraicGeometry.IsLocallyNoetherian X)
      (hX : X.IsLocallyOfFiniteTypeOverField),
      ∀ α β : AlgebraicGeometry.AlgebraicCycle X ℤ, AlgebraicGeometry.RationallyEquivalent d α β →
        AlgebraicGeometry.firstChernCapCycle hX L d α = AlgebraicGeometry.firstChernCapCycle hX L d β then
    haveI : AlgebraicGeometry.IsLocallyNoetherian X := h.2.1
    QuotientAddGroup.lift _
      ((AlgebraicGeometry.firstChernCapCycle h.2.2.1 L d).comp (AlgebraicGeometry.cycleSubgroup X d).subtype)
      (by
        intro x hx
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
          h.2.2.2 x 0 ⟨x.2, zero_mem _, by rw [sub_zero]; exact AddSubgroup.mem_addSubgroupOf.mp hx⟩,
          map_zero])
  else 0

end
