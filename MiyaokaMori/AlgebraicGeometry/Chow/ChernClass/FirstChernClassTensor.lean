import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.RationalSectionDivisorTensor

/-! # Additivity of the first Chern class under tensor products

The first Chern class is additive under tensor products: `c_1(L ⊗ M) ∩ α = c_1(L) ∩ α + c_1(M) ∩ α`
(in particular `c_1(L^{⊗m}) = m·c_1(L)`). Source: Fulton, Intersection Theory, Prop. 2.5(e). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `c_1(L ⊗ M) = c_1(L) + c_1(M)` on the Chow group of a scheme locally of finite type over a field
(Stacks 02SL, 02SP: the divisor of a tensor product of rational sections is the sum of the divisors,
then descend to the Chow group). -/
theorem AlgebraicGeometry.firstChernClass_tensor {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.tensor L M).IsLineBundle] (d : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Scheme.Modules.tensor L M) d
      = AlgebraicGeometry.firstChernClass L d + AlgebraicGeometry.firstChernClass M d := by
  have hLN : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  show AlgebraicGeometry.firstChernClass _ d (AlgebraicGeometry.ChowGroup.mk c) =
    AlgebraicGeometry.firstChernClass L d (AlgebraicGeometry.ChowGroup.mk c) +
      AlgebraicGeometry.firstChernClass M d (AlgebraicGeometry.ChowGroup.mk c)
  rw [AlgebraicGeometry.firstChernClass_mk' hXk _ d c, AlgebraicGeometry.firstChernClass_mk' hXk L d c,
    AlgebraicGeometry.firstChernClass_mk' hXk M d c]
  cases d with
  | zero =>
    rw [AlgebraicGeometry.firstChernCapCycle_dim_zero, AlgebraicGeometry.firstChernCapCycle_dim_zero,
      AlgebraicGeometry.firstChernCapCycle_dim_zero, add_zero]
  | succ e =>
    exact AlgebraicGeometry.firstChernCapCycle_eq_add_of_pointwise hXk _ L M e
      (fun w hw => AlgebraicGeometry.isRatEquivGen_firstChernCapPoint_tensor L M e w hw) c.1

end
