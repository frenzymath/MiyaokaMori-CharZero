import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointwise

/-! # The cap with the trivial line bundle vanishes

The cap with the trivial line bundle is zero, `c_1(O_X) ∩ − = 0`, and the cap depends only on the
isomorphism class of the line bundle. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Both results are proved without Stacks 02TI/0AYC: they descend to the cycle-level `firstChernCapCycle`
   directly from the definition of `firstChernClass` (`FirstChernClassNoIf.lean`); the trivial bundle uses
   `firstChernCapCycle_unit_eq_zero`, and isomorphisms use the pointwise comparison
   (`FirstChernCapPointwise.lean`, Stacks 02SH: change of rational section). -/

/-- `c_1(O_X) ∩ − = 0`. -/
theorem AlgebraicGeometry.firstChernClass_one (X : AlgebraicGeometry.Scheme.{u}) (d : ℕ) :
    AlgebraicGeometry.firstChernClass (SheafOfModules.unit X.ringCatSheaf) (d + 1) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  rcases AlgebraicGeometry.firstChernClass_mk_eq_zero_or
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) (d + 1) c with h0 | ⟨hLN, hX, h1⟩
  · exact h0
  · exact h1.trans (AlgebraicGeometry.firstChernCapCycle_unit_eq_zero hX (d + 1) c.1)

/-- The cap `c_1(L) ∩ −` depends only on the isomorphism class of `L`. -/
theorem AlgebraicGeometry.firstChernClass_congr {X : AlgebraicGeometry.Scheme.{u}}
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') (d : ℕ) :
    AlgebraicGeometry.firstChernClass L (d + 1) = AlgebraicGeometry.firstChernClass L' (d + 1) :=
  AlgebraicGeometry.firstChernClass_eq_of_capCycle_eq L L' (d + 1) fun _ hX β =>
    AlgebraicGeometry.firstChernCapCycle_eq_of_pointwise hX L L' d
      (fun w hw => AlgebraicGeometry.isRatEquivGen_firstChernCapPoint_sub_of_iso L L' e d w hw) β

end
