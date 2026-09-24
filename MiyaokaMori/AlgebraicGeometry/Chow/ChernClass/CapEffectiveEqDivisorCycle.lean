import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamental
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightNeOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightEqOne

/-! # The cap with an effective section is the cycle of its zero scheme

Fulton, Intersection Theory, §2.3: if the local equations of a global section `σ` of a line bundle `L`
on an integral closed subscheme `V` are non-zero-divisors everywhere, then `c_1(L) ∩ [V] = [Z(σ) ∩ V]`
(the cycle of the zero scheme, with multiplicities given by the orders of the local equations). This
is the statement of the paper that successive intersections are the corresponding coordinate
subspaces with multiplicities given by the coordinate powers (proof of Proposition 2.4). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `c_1(L) ∩ [X] = [Z(σ)]` for a global section `σ` whose local equations are non-zero-divisors:
by Stacks 02SJ, `c_1(L) ∩ [X] = [div_L(s)]` for any nonzero rational section `s`; the germ of a
nonzero global section at the generic point is nonzero, and `div_L(σ)` agrees pointwise with the
cycle `[Z(σ)]_d` of the zero scheme. -/
theorem AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (Opposite.op ⊤) : Type u)) (hσ : σ ≠ 0)
    (d : ℕ) (hX : X.dimension = d + 1) :
    ∃ h : (AlgebraicGeometry.Scheme.idealSheafOfSection L σ).cycle d ∈ AlgebraicGeometry.cycleSubgroup X d,
      AlgebraicGeometry.firstChernClass L (d + 1) (X.fundamentalChowClass (d + 1))
        = AlgebraicGeometry.ChowGroup.mk ⟨(AlgebraicGeometry.Scheme.idealSheafOfSection L σ).cycle d, h⟩ := by
  have hgerm := AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero L σ hσ
  have hcyc : L.rationalSectionDivisor
      (L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ)) =
      (AlgebraicGeometry.Scheme.idealSheafOfSection L σ).cycle d := by
    ext z
    by_cases hz : Order.coheight z = 1
    · exact (AlgebraicGeometry.Scheme.idealSheafOfSection_cycle_apply_of_coheight_eq_one
        (k := k) L σ hσ d hX z hz).symm
    · rw [AlgebraicGeometry.Scheme.idealSheafOfSection_cycle_apply_of_coheight_ne_one L σ hσ d z hz]
      exact AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_zero_of_coheight_ne_one L _ hz
  obtain ⟨h, heq⟩ :=
    AlgebraicGeometry.firstChernClass_fundamentalChowClass_eq_mk_rationalSectionDivisor
      (k := k) L d hX _ hgerm
  refine ⟨hcyc ▸ h, ?_⟩
  rw [heq]
  congr 1
  exact Subtype.ext hcyc

end
