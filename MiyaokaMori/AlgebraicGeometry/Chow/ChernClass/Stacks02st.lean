import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionPullbackDominant
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisorAdditive
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02rt
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle

/-! # Pushforward of the cap with a pulled-back line bundle (Stacks 02ST, cycle level)

Stacks 02ST at the level of cycles: `X`, `Y` integral of the same dimension `n+1` and locally of finite
type over a field, `f : X → Y` a proper dominant `k`-morphism, `L` an invertible sheaf on `Y`; then
`f_*(c_1(f^*L) ∩ [X]) = [R(X):R(Y)]·(c_1(L) ∩ [Y])` in `CH_n(Y)`, where `∩` is the cycle-level
`firstChernCapCycle`. The proof reduces to `f_*(div_{f^*L}(f^*s)) = [R(X):R(Y)]·div_L(s)`.

Source: Stacks 02ST (lemma-equal-c1-as-cycles).

Assembly:
1. Cycle-level 02SJ (`firstChernCapCycle_fundamentalCycle_eq_mk_rationalSectionDivisor`, this file): on an
   integral scheme `c_1(M) ∩ [X] = [div_M(t)]` for any nonzero rational section `t` ((F1) +
   `firstChernCapPoint_genericPoint` + change of section differs by a principal cycle + (PC));
2. take a nonzero rational section `s` of `L` and use `t = f^*s` on `X` (`rationalSectionPullback_ne_zero`);
3. `chowPushforward_mk` (the descent condition is the statement of 02S2,
   `properPushforward_rationallyEquivalent`) reduces the pushforward to cycles;
4. the cycle identity is `properPushforward_rationalSectionDivisor_pullback` (02ST at the divisor level,
   proved through the scheme version of 02RT).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Cycle level (the `∩` of 02SO is `firstChernCapCycle`, acting on cycles with values in the Chow group):
   this does not go through the descent of `firstChernClass` (02TI), so it can be used by the proof of
   02SU without circularity. -/

/-- **Stacks 02SJ at the level of cycles**: `X` integral, locally Noetherian, locally of finite type over a
field, `dim X = m + 1`, `M` a line bundle, `t` any nonzero rational section of `M`; then
`c_1(M) ∩ [X]` (the cycle-level `firstChernCapCycle`) equals `[div_M(t)] ∈ CH_m(X)`.

Proof (as (F2) in `FirstChernCapFundamental.lean`, but stopping at `firstChernCapCycle` instead of
`firstChernClass`): (F1) the cycle representing `c_1(M) ∩ [X]` is `firstChernCapPoint M η`;
`firstChernCapPoint_genericPoint` shows it equals some `div_M(s′)`; change of section gives
`div_M(s′) = div_M(t) + div(g)` (02SH); `div(g)` is a generator of rational equivalence at `η` (PC), hence
`0` in `CH_m(X)`. Source: Stacks 02SJ, 02SH. -/
theorem AlgebraicGeometry.firstChernCapCycle_fundamentalCycle_eq_mk_rationalSectionDivisor
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X] (hXk : X.IsLocallyOfFiniteTypeOverField)
    (M : X.Modules) [M.IsLineBundle] {m : ℕ} (hX : X.dimension = m + 1)
    (t : M.stalk (genericPoint X)) (ht : t ≠ 0)
    (hmem : M.rationalSectionDivisor t ∈ AlgebraicGeometry.cycleSubgroup X m) :
    AlgebraicGeometry.firstChernCapCycle hXk M (m + 1) (X.fundamentalCycle (m + 1)) =
      AlgebraicGeometry.ChowGroup.mk ⟨M.rationalSectionDivisor t, hmem⟩ := by
  obtain ⟨s', hs', hcap⟩ := MiyaokaMori.FirstChernCapPointGeneric.firstChernCapPoint_genericPoint M
  obtain ⟨g, hg⟩ :=
    MiyaokaMori.FirstChernCapPointClosurePushforward.exists_rationalSectionDivisor_eq_add_principalCycle
      M s' t hs' ht
  have haux := (AlgebraicGeometry.firstChernCapCycleAux_fundamentalCycle_of_isIntegral M hX).trans hcap
  have hmem' : M.rationalSectionDivisor s' ∈ AlgebraicGeometry.cycleSubgroup X m := by
    have h0 := AlgebraicGeometry.firstChernCapCycleAux_mem hXk M (m + 1) (X.fundamentalCycle (m + 1))
    rw [haux] at h0
    exact h0
  have h1 : AlgebraicGeometry.firstChernCapCycle hXk M (m + 1) (X.fundamentalCycle (m + 1)) =
      AlgebraicGeometry.ChowGroup.mk ⟨M.rationalSectionDivisor s', hmem'⟩ := by
    show AlgebraicGeometry.ChowGroup.mk (⟨AlgebraicGeometry.firstChernCapCycleAux M (m + 1)
      (X.fundamentalCycle (m + 1)), _⟩ : ↥(AlgebraicGeometry.cycleSubgroup X m)) = _
    congr 1
    exact Subtype.ext haux
  rw [h1, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  show M.rationalSectionDivisor s' - M.rationalSectionDivisor t ∈ AlgebraicGeometry.ratEquivZero X m
  rw [hg, add_sub_cancel_left]
  exact AlgebraicGeometry.single_mem_ratEquivZero
    (AlgebraicGeometry.isRatEquivGen_principalCycle
      (AlgebraicGeometry.height_genericPoint_of_dimension_pos hX) g)

theorem AlgebraicGeometry.chowPushforward_firstChernCapCycle_fundamentalCycle_of_dominant
    {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (f : X ⟶ Y) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper f]
    (hf : f.base (genericPoint X) = genericPoint Y)
    (L : Y.Modules) [L.IsLineBundle]
    (n : ℕ) (hX : X.dimension = n + 1) (hY : Y.dimension = n + 1) :
    AlgebraicGeometry.chowPushforward f n
        (AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) (n + 1)
          (X.fundamentalCycle (n + 1)))
      = (functionFieldDegree f : ℤ) •
          AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) Y)
            L (n + 1) (Y.fundamentalCycle (n + 1)) := by
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  have hYk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) Y
  have hXd := AlgebraicGeometry.topologicalKrullDim_eq_of_dimension_pos hX
  have hYd := AlgebraicGeometry.topologicalKrullDim_eq_of_dimension_pos hY
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero L
  have ht := AlgebraicGeometry.Scheme.Modules.rationalSectionPullback_ne_zero f hf L s hs
  have hmemX : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).rationalSectionDivisor
      (AlgebraicGeometry.Scheme.Modules.rationalSectionPullback f hf L s) ∈
        AlgebraicGeometry.cycleSubgroup X n := fun z hz =>
    AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hXd
      (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support _ _ z hz)
  have hmemY : L.rationalSectionDivisor s ∈ AlgebraicGeometry.cycleSubgroup Y n := fun z hz =>
    AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hYd
      (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support _ _ z hz)
  rw [AlgebraicGeometry.firstChernCapCycle_fundamentalCycle_eq_mk_rationalSectionDivisor hXk _ hX _ ht hmemX,
    AlgebraicGeometry.firstChernCapCycle_fundamentalCycle_eq_mk_rationalSectionDivisor hYk L hY s hs hmemY,
    AlgebraicGeometry.chowPushforward_mk f n
      (AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) f n),
    ← map_zsmul]
  congr 1
  apply Subtype.ext
  show AlgebraicGeometry.AlgebraicCycle.properPushforward f _ = (functionFieldDegree f : ℤ) • _
  exact AlgebraicGeometry.Scheme.Modules.properPushforward_rationalSectionDivisor_pullback f hf
    (k := k) (n + 1) hXd hYd L s hs

end
