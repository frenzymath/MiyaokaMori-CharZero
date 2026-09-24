import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardPreservesDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalence
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suCycle

/-! # The cap of a Cartier divisor with cycles

The action `D ∩ − : Z_{i+1}(X) → A_i(X)` of a Cartier divisor on cycles: on each generator `[V]` take the
class of the Weil cycle of `D|_V` and push it to `X` (the route of Fulton, Intersection Theory, Chapter 2,
§2.3; used for `-K_X · f_*[C]` in Theorem 1.1 of the paper).

`capDivisor D i` is *defined* as `c₁(O_X(D)) ∩ −` composed with the class map,
`(firstChernClass O(D) (i+1)).comp ChowGroup.mk : Z_{i+1}(X) →+ A_i(X)` (Fulton §2.5 / Stacks 02SJ: the two
are the same construction), so that `capDivisor_eq_firstChernClass` is `rfl`. The generator formula
`capDivisor_single` reduces `c₁(O(D)) ∩ [V_v]` to `firstChernCapPoint` (`firstChernClass_mk'`,
`firstChernCapCycleAux_single`) and then uses the change-of-section argument of Stacks 02SH.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `D ∩ − : Z_{i+1}(X) →+ A_i(X)`, **defined** as `c₁(O_X(D)) ∩ −` on the class of the cycle
(Fulton §2.5 = Stacks 02SJ: `D ∩ [V] = c₁(O(D)) ∩ [V] = [ι_{V*} div_{O(D)|_V}(s)]` for any nonzero rational section
`s`). `i + 1 - 1` and `i` are definitionally equal, so the codomain is `ChowGroup X i`. -/
noncomputable def capDivisor {k : Type u} [Field k] {X : Variety k} (D : CartierDivisor X)
    (i : ℕ) : CycleGroup X (i + 1) →+ ChowGroup X i :=
  (AlgebraicGeometry.firstChernClass D.lineBundle.toModules (i + 1)).comp
    AlgebraicGeometry.ChowGroup.mk

/- Generator formula: `v` a point of dimension `i+1`, `V_v = ClosedSubvariety.ofPoint v`, `s` any nonzero
   rational section of `ι_v^*O_X(D)` at the generic point of `V_v`; then
   `D ∩ [V_v] = [ι_v* div_{ι_v^*O(D)}(s)]` (Stacks 02SJ / Fulton §2.3). -/

open Classical in

theorem capDivisor_single {k : Type u} [Field k] {X : Variety k} (D : CartierDivisor X) (i : ℕ)
    (v : X.toScheme) (hv : Order.height v = ((i + 1 : ℕ) : ℕ∞))
    (hvmem : Function.locallyFinsuppWithin.single v (1 : ℤ) ∈ CycleGroup X (i + 1))
    (s : ((AlgebraicGeometry.Scheme.Modules.pullback (ClosedSubvariety.ofPoint v).ι).obj
          D.lineBundle.toModules).stalk (genericPoint (ClosedSubvariety.ofPoint v).carrier))
    (hs : s ≠ 0)
    (hmem : AlgebraicGeometry.AlgebraicCycle.properPushforward (ClosedSubvariety.ofPoint v).ι
        (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor _ s) ∈ CycleGroup X i) :
      capDivisor D i ⟨Function.locallyFinsuppWithin.single v 1, hvmem⟩
      = QuotientAddGroup.mk ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward (ClosedSubvariety.ofPoint v).ι
          (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor _ s), hmem⟩ := by
  let V := ClosedSubvariety.ofPoint v
  let M := (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj D.lineBundle.toModules
  letI : CompactSpace X.toScheme := Variety.compactSpace X
  letI : CompactSpace V.carrier :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace V.ι
  let tM : M.stalk (genericPoint V.carrier) := Classical.epsilon fun q => q ≠ 0
  let t : M.presheaf.stalk (genericPoint V.carrier) := tM
  change M.presheaf.stalk (genericPoint V.carrier) at s
  have htM : tM ≠ 0 := by
    dsimp [tM]
    exact Classical.epsilon_spec
      (AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero M)
  have ht : t ≠ 0 := by
    intro h
    apply htM
    exact h
  have hdim : V.dimension = i + 1 := by
    change V.carrier.dimension = i + 1
    change (X.toScheme.pointClosure v).dimension = i + 1
    exact AlgebraicGeometry.Scheme.dimension_pointClosure v hv
  have htop : topologicalKrullDim V.carrier = ((i + 1 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (X.toScheme.pointClosure v) = _
    exact AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure v hv
  have hdivmem (q : M.stalk (genericPoint V.carrier)) (hq : q ≠ 0) :
      AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M q ∈
        CycleGroup V.toVariety i := by
    intro z hz
    have hco : Order.coheight z = 1 :=
      AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support M q z hz
    let π : V.carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
      V.ι ≫ X.structureMorphism
    have hLFT : AlgebraicGeometry.LocallyOfFiniteType π := inferInstance
    exact AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one π htop hco
  let ct : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ :=
    AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
      (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M tM)
  have hctmem : ct ∈ CycleGroup X i := by
    change AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
        (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M tM) ∈ CycleGroup X i
    intro y hy
    have happ : AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
        (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M tM) y =
        ∑ᶠ z ∈ V.ι.base ⁻¹' {y},
          (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M tM) z *
            ((AlgebraicGeometry.AlgebraicCycle.mapCoeff V.ι
              (Order.height (α := V.carrier)) (Order.height (α := X.toScheme)) z : ℕ) : ℤ) := rfl
    rw [happ] at hy
    obtain ⟨z, (hzy : V.ι.base z = y), hz⟩ :=
      exists_ne_zero_of_finsum_mem_ne_zero hy
    have hq : AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M tM z ≠ 0 := by
      intro hzero
      exact hz (by simp [hzero])
    have hdimz : Order.height z = Order.height (V.ι.base z) := by
      by_contra hne
      exact hz (by simp [AlgebraicGeometry.AlgebraicCycle.mapCoeff, hne])
    rw [← hzy, ← hdimz]
    exact hdivmem tM htM z hq
  obtain ⟨U, hU, ⟨eU⟩⟩ := AlgebraicGeometry.Scheme.Modules.exists_trivialization M
    (genericPoint V.carrier)
  let c := AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate V.carrier M U
    ⟨⟨genericPoint V.carrier, hU⟩⟩ eU
  have hcs : c s ≠ 0 := AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate_ne_zero
    V.carrier M U ⟨⟨genericPoint V.carrier, hU⟩⟩ eU s hs
  have hct0 : c t ≠ 0 := AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate_ne_zero
    V.carrier M U ⟨⟨genericPoint V.carrier, hU⟩⟩ eU t ht
  let g : V.carrier.functionFieldˣ := Units.mk0 (c t / c s) (div_ne_zero hct0 hcs)
  have hts : t = (g : V.carrier.functionField) • s := by
    apply c.injective
    change c t = c ((c t / c s) • s)
    rw [c.map_smul, smul_eq_mul, div_mul_cancel₀ _ hcs]
  have hsmul := AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_smul M s hs g
  have hdiv : AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M t =
      AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M s + V.carrier.principalCycle g := by
    rw [hts]
    exact hsmul
  have hpush : ct =
      AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
          (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M s) +
        AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι (V.carrier.principalCycle g) := by
    dsimp [ct]
    rw [hdiv]
    change AlgebraicGeometry.AlgebraicCycle.map V.ι _ _ (_ + _) = _
    exact AlgebraicGeometry.AlgebraicCycle.map_add V.ι _ _ _ _
  have hpmem : AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι (V.carrier.principalCycle g) ∈
      CycleGroup X i := by
    have hp : AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι (V.carrier.principalCycle g) =
        ct - AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
          (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M s) := by
      rw [hpush]
      abel
    rw [hp]
    exact sub_mem hctmem hmem
  -- the generator `ι_V* div(g)` lies in the rational equivalence of Stacks 02RW
  have hprincipal :
      (⟨AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι (V.carrier.principalCycle g), hpmem⟩ :
        CycleGroup X i) ∈ (AlgebraicGeometry.ratEquivZero X.toScheme i).addSubgroupOf
          (AlgebraicGeometry.cycleSubgroup X.toScheme i) :=
    ClosedSubvariety.properPushforward_principalDivisor_mem_addSubgroupOf V hdim g hpmem
  have hquot :
      (QuotientAddGroup.mk (⟨ct, hctmem⟩ : CycleGroup X i) : ChowGroup X i) =
        (QuotientAddGroup.mk
          ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
            (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M s), hmem⟩ :
          ChowGroup X i) := by
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    let cp : CycleGroup X i :=
      ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι (V.carrier.principalCycle g), hpmem⟩
    have hsub : (⟨ct, hctmem⟩ : CycleGroup X i) -
        ⟨AlgebraicGeometry.AlgebraicCycle.properPushforward V.ι
          (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor M s), hmem⟩ = cp := by
      apply Subtype.ext
      dsimp [cp]
      rw [hpush]
      abel
    rw [hsub]
    exact hprincipal
  -- `capDivisor` is `c₁(O(D)) ∩ −`; descend to the cycle level with `firstChernClass_mk'`; the
  -- `firstChernCapCycleAux` of a single-point cycle is `firstChernCapPoint O(D) v`
  -- (`firstChernCapCycleAux_single`), whose body is literally the same expression as `ct`
  -- (`ι_* div` of the chosen section `tM`), hence `rfl`; finish with `hquot` above.
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X.toScheme
  change AlgebraicGeometry.firstChernClass D.lineBundle.toModules (i + 1)
    (AlgebraicGeometry.ChowGroup.mk ⟨Function.locallyFinsuppWithin.single v 1, hvmem⟩) = _
  rw [AlgebraicGeometry.firstChernClass_mk' hXk D.lineBundle.toModules (i + 1)]
  show AlgebraicGeometry.ChowGroup.mk
    ⟨AlgebraicGeometry.firstChernCapCycleAux D.lineBundle.toModules (i + 1)
        (Function.locallyFinsuppWithin.single v 1),
      AlgebraicGeometry.firstChernCapCycleAux_mem hXk D.lineBundle.toModules (i + 1) _⟩ = _
  have haux : AlgebraicGeometry.firstChernCapCycleAux D.lineBundle.toModules (i + 1)
      (Function.locallyFinsuppWithin.single v (1 : ℤ)) = ct := by
    rw [MiyaokaMori.Stacks02suCycle.firstChernCapCycleAux_single, if_pos hv, one_smul]
    rfl
  refine Eq.trans ?_ hquot
  exact congrArg AlgebraicGeometry.ChowGroup.mk (Subtype.ext haux)

end
