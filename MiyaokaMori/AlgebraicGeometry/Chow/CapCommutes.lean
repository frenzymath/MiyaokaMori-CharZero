import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02th
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCommCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf

/-! # Commutativity of caps with first Chern classes

Fulton, Intersection Theory, Cor. 2.4.2: the caps of two Cartier divisors (line bundles) on the Chow
group commute, `c_1(L) ∘ c_1(L') = c_1(L') ∘ c_1(L)`. This is why successive Cartier restrictions
make sense independently of their order (proof of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `c_1(L) ∩ (c_1(L') ∩ α) = c_1(L') ∩ (c_1(L) ∩ α)` (Stacks 02TJ). The proof descends to the cycle
level (`FirstChernClassNoIf.lean`) and uses the cycle-level commutativity
(`FirstChernCapCommCycle.lean`); it does not use the projection formula for general proper
morphisms. -/
theorem AlgebraicGeometry.firstChernClass_comm {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (d : ℕ) :
    (AlgebraicGeometry.firstChernClass L (d + 1)).comp
        (AlgebraicGeometry.firstChernClass L' (d + 2))
      = (AlgebraicGeometry.firstChernClass L' (d + 1)).comp
        (AlgebraicGeometry.firstChernClass L (d + 2)) := by
  have hLN : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  show AlgebraicGeometry.firstChernClass L (d + 1)
      (AlgebraicGeometry.firstChernClass L' (d + 2) (AlgebraicGeometry.ChowGroup.mk c)) =
    AlgebraicGeometry.firstChernClass L' (d + 1)
      (AlgebraicGeometry.firstChernClass L (d + 2) (AlgebraicGeometry.ChowGroup.mk c))
  rw [AlgebraicGeometry.firstChernClass_mk' hXk L' (d + 2) c,
    AlgebraicGeometry.firstChernClass_mk' hXk L (d + 2) c]
  show AlgebraicGeometry.firstChernClass L (d + 1) (AlgebraicGeometry.ChowGroup.mk
      (⟨AlgebraicGeometry.firstChernCapCycleAux L' (d + 2) c.1,
        AlgebraicGeometry.firstChernCapCycleAux_mem hXk L' (d + 2) c.1⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X (d + 1)))) =
    AlgebraicGeometry.firstChernClass L' (d + 1) (AlgebraicGeometry.ChowGroup.mk
      (⟨AlgebraicGeometry.firstChernCapCycleAux L (d + 2) c.1,
        AlgebraicGeometry.firstChernCapCycleAux_mem hXk L (d + 2) c.1⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X (d + 1))))
  rw [AlgebraicGeometry.firstChernClass_mk' hXk L (d + 1),
    AlgebraicGeometry.firstChernClass_mk' hXk L' (d + 1)]
  show AlgebraicGeometry.ChowGroup.mk
      (⟨AlgebraicGeometry.firstChernCapCycleAux L (d + 1)
          (AlgebraicGeometry.firstChernCapCycleAux L' (d + 2) c.1),
        AlgebraicGeometry.firstChernCapCycleAux_mem hXk L (d + 1) _⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X d)) =
    AlgebraicGeometry.ChowGroup.mk
      (⟨AlgebraicGeometry.firstChernCapCycleAux L' (d + 1)
          (AlgebraicGeometry.firstChernCapCycleAux L (d + 2) c.1),
        AlgebraicGeometry.firstChernCapCycleAux_mem hXk L' (d + 1) _⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X d))
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  exact AlgebraicGeometry.firstChernCapCycleAux_comm_mem (k := k) L L' d c.1

end
