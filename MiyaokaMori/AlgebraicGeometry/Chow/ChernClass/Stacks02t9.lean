import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonzeroSectionRegular
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleRestrictClosed
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassMk
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.SectionGermGeneratorOffZeroLocus
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointwise

/-! # Support refinement of the cap with a first Chern class (Stacks 02T9)

Stacks 02T9 (with the Gysin map of 02T8): for `L` invertible, `s ∈ Γ(X,L)` and `i : D = Z(s) → X`, one has
`c_1(L) ∩ α = i_*(i^*α)` for every `α`. Only its consequence is formalized here: `c_1(L) ∩ α` is the
pushforward of some class in `CH_*(Z(s))` (support refinement). This holds for any global section, not
necessarily regular.

Source: Stacks 02T9 (lemma-gysin-fundamental).

The restriction of cycles along a closed immersion is `CycleRestrictClosed.lean`; the cycle-level support
refinement is `firstChernCapCycle_mem_range_zeroScheme` (this file), and the main theorem
`firstChernClass_mem_range_zeroScheme` is assembled from it by taking a representative and
`firstChernClass_mk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The cycle-level assembly of 02T9

`B_w` (`zeroSchemeCapPoint`): for `w ∈ Z(s)` take the representative `firstChernCapPoint L w` of
`c_1(L) ∩ [w]`; for `w ∉ Z(s)` take `ι_{w*} div_{ι_w^*L}(ι_w^*s)` (the pulled-back section itself as a
rational section). Then
* `supp B_w ⊆ Z(s)` (for `w ∉ Z(s)`, since `ord = 0` outside `Z(s)`: the germ of a section generates off its
  zero locus, + 02OR);
* `capPoint L w − B_w` is a 02RW generator (for `w ∉ Z(s)` by the change of section 02SH);
* `b := Σ_w a_w B_w` is locally finite, lies in `Z_d` and is supported in `Z(s)`; `capAux a − b` is
  rationally trivial (`mem_ratEquivZero_of_pointwise`).
Finally `γ := [ι^♭ b]`, and `ι_*γ = [b] = [capAux a]`. -/

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

/-- The height in `X` of a point of coheight `1` on a point closure (Stacks 0A21(4); the second half of the
proof of `firstChernCapPoint_height`). -/
theorem AlgebraicGeometry.height_pointClosureι_of_coheight_eq_one {X : AlgebraicGeometry.Scheme.{u}}
    (hX : X.IsLocallyOfFiniteTypeOverField) {w : X} {d : ℕ} (hw : Order.height w = (d : ℕ∞))
    (z' : X.pointClosure w) (hco : Order.coheight z' = 1) :
    Order.height ((X.pointClosureι w).base z') = ((d - 1 : ℕ) : ℕ∞) := by
  obtain ⟨k, _, π, _⟩ := hX
  let _ : (X.pointClosure w).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨X.pointClosureι w ≫ π⟩
  have : AlgebraicGeometry.LocallyOfFiniteType
      ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (X.pointClosureι w ≫ π))
  have hdim := AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure w hw
  have hadd := AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := k)
    (X.pointClosure w) d hdim z'
  rw [hco] at hadd
  rw [AlgebraicGeometry.Scheme.Hom.height_of_isClosedImmersion]
  have hne : Order.height z' ≠ ⊤ := by
    intro ht; rw [ht] at hadd; simp at hadd
  lift Order.height z' to ℕ using hne with n
  have : n + 1 = d := by exact_mod_cast hadd
  have : n = d - 1 := by omega
  exact_mod_cast this

/-- The germ at the generic point of `W_w` of the pulled-back section `ι_w^*s` (as a rational section of
`ι_w^*L`). -/
noncomputable abbrev AlgebraicGeometry.pointClosureSectionGerm {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) (s : (L.val.obj (Opposite.op ⊤) : Type u)) (w : X) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).presheaf.stalk
      (genericPoint (X.pointClosure w)) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).presheaf.germ ⊤
    (genericPoint (X.pointClosure w)) trivial
    (show Γ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L, ⊤) from
      sectionPullbackAlong (X.pointClosureι w) s)

/-- `B_w`: a representative of `c_1(L) ∩ [closure{w}]` supported in `Z(s)`. -/
noncomputable def AlgebraicGeometry.zeroSchemeCapPoint {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle]
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) (w : X) : AlgebraicGeometry.AlgebraicCycle X ℤ :=
  open Classical in
  if w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support then
    AlgebraicGeometry.firstChernCapPoint L w
  else
    AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
      (((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor
        (AlgebraicGeometry.pointClosureSectionGerm L s w))

section ZeroSchemeCap

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
  (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u))

theorem AlgebraicGeometry.zeroSchemeCapPoint_of_mem {w : X}
    (hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support) :
    AlgebraicGeometry.zeroSchemeCapPoint L s w = AlgebraicGeometry.firstChernCapPoint L w := by
  classical
  unfold AlgebraicGeometry.zeroSchemeCapPoint
  exact if_pos hw

theorem AlgebraicGeometry.zeroSchemeCapPoint_of_notMem {w : X}
    (hw : w ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support) :
    AlgebraicGeometry.zeroSchemeCapPoint L s w =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
        (((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor
          (AlgebraicGeometry.pointClosureSectionGerm L s w)) := by
  classical
  unfold AlgebraicGeometry.zeroSchemeCapPoint
  exact if_neg hw

/-- 02OR: the support of the zero scheme of the pulled-back section on `W_w` is `ι_w^{-1}(Z(s))`. -/
theorem AlgebraicGeometry.notMem_support_pullback_pointClosure {w : X} {z' : X.pointClosure w}
    (h : (X.pointClosureι w).base z' ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support) :
    z' ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection
      ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L)
      (sectionPullbackAlong (X.pointClosureι w) s)).support := by
  rw [AlgebraicGeometry.Scheme.zeroScheme_pullback,
    AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
  exact h

theorem AlgebraicGeometry.zeroSchemeCapPoint_specializes {w z : X}
    (h : AlgebraicGeometry.zeroSchemeCapPoint L s w z ≠ 0) : w ⤳ z := by
  by_cases hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support
  · rw [AlgebraicGeometry.zeroSchemeCapPoint_of_mem L s hw] at h
    exact AlgebraicGeometry.firstChernCapPoint_specializes L h
  · rw [AlgebraicGeometry.zeroSchemeCapPoint_of_notMem L s hw] at h
    exact AlgebraicGeometry.properPushforward_pointClosure_specializes _ h

/-- The coefficient of `B_w` at an image point `ι_w z'` (for `w ∉ Z(s)`). -/
theorem AlgebraicGeometry.zeroSchemeCapPoint_apply_of_notMem {w : X}
    (hw : w ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support) {z : X}
    (h : AlgebraicGeometry.zeroSchemeCapPoint L s w z ≠ 0) :
    ∃ z' : X.pointClosure w, (X.pointClosureι w).base z' = z ∧
      ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionOrd
        (AlgebraicGeometry.pointClosureSectionGerm L s w) z' ≠ 0 := by
  rw [AlgebraicGeometry.zeroSchemeCapPoint_of_notMem L s hw] at h
  by_cases hr : z ∈ Set.range (X.pointClosureι w).base
  · obtain ⟨z', rfl⟩ := hr
    refine ⟨z', rfl, ?_⟩
    have e := MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply
      (X.pointClosureι w)
      (((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor
        (AlgebraicGeometry.pointClosureSectionGerm L s w)) z'
    rw [e] at h
    exact h
  · exact absurd (MiyaokaMori.ClosedImmersionPushforward.properPushforward_apply_of_notMem_range
      (X.pointClosureι w) _ hr) h

/-- supp B_w ⊆ Z(s). -/
theorem AlgebraicGeometry.zeroSchemeCapPoint_mem_support {w z : X}
    (h : AlgebraicGeometry.zeroSchemeCapPoint L s w z ≠ 0) :
    z ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support := by
  by_cases hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support
  · exact (AlgebraicGeometry.zeroSchemeCapPoint_specializes L s h).mem_closed
      (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support.isClosed hw
  · obtain ⟨z', rfl, hz'⟩ := AlgebraicGeometry.zeroSchemeCapPoint_apply_of_notMem L s hw h
    by_contra hzD
    exact hz' (AlgebraicGeometry.Scheme.rationalSectionOrd_germ_eq_zero_of_notMem_support _ _
      (AlgebraicGeometry.notMem_support_pullback_pointClosure L s hzD))

/-- The support points of `B_w` have height `d` (for `height w = d+1`). -/
theorem AlgebraicGeometry.zeroSchemeCapPoint_height (hX : X.IsLocallyOfFiniteTypeOverField)
    {d : ℕ} {w z : X} (hwd : Order.height w = ((d + 1 : ℕ) : ℕ∞))
    (h : AlgebraicGeometry.zeroSchemeCapPoint L s w z ≠ 0) :
    Order.height z = (d : ℕ∞) := by
  by_cases hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support
  · rw [AlgebraicGeometry.zeroSchemeCapPoint_of_mem L s hw] at h
    simpa using AlgebraicGeometry.firstChernCapPoint_height hX L hwd h
  · obtain ⟨z', rfl, hz'⟩ := AlgebraicGeometry.zeroSchemeCapPoint_apply_of_notMem L s hw h
    have hco := AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support _ _ z' hz'
    simpa using AlgebraicGeometry.height_pointClosureι_of_coheight_eq_one hX hwd z' hco

/-- `capPoint L w − B_w` is a 02RW generator. -/
theorem AlgebraicGeometry.isRatEquivGen_firstChernCapPoint_sub_zeroSchemeCapPoint {e : ℕ} {w : X}
    (hwd : Order.height w = ((e + 1 : ℕ) : ℕ∞)) :
    AlgebraicGeometry.IsRatEquivGen X e w
      (AlgebraicGeometry.firstChernCapPoint L w - AlgebraicGeometry.zeroSchemeCapPoint L s w) := by
  by_cases hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support
  · rw [AlgebraicGeometry.zeroSchemeCapPoint_of_mem L s hw, sub_self]
    have h0 : AlgebraicGeometry.IsRatEquivGen X e w _ :=
      ⟨hwd, inferInstance, inferInstance, inferInstance, 1, rfl⟩
    have h00 := h0.zsmul 0
    rwa [zero_smul] at h00
  · obtain ⟨s₁, hs₁, h1⟩ :=
      MiyaokaMori.FirstChernCapPointClosurePushforward.exists_firstChernCapPoint_eq L w
    have hη : genericPoint (X.pointClosure w) ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection
        ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L)
        (sectionPullbackAlong (X.pointClosureι w) s)).support := by
      refine AlgebraicGeometry.notMem_support_pullback_pointClosure L s ?_
      rwa [AlgebraicGeometry.Scheme.pointClosureι_genericPoint]
    have ht0 := AlgebraicGeometry.Scheme.germ_genericPoint_ne_zero_of_notMem_support _ _ hη
    obtain ⟨g, hg⟩ :=
      MiyaokaMori.FirstChernCapPointClosurePushforward.exists_rationalSectionDivisor_eq_add_principalCycle
        _ s₁ (AlgebraicGeometry.pointClosureSectionGerm L s w) hs₁ ht0
    refine ⟨hwd, inferInstance, inferInstance, inferInstance, g, ?_⟩
    rw [AlgebraicGeometry.zeroSchemeCapPoint_of_notMem L s hw, h1, hg]
    exact sub_eq_of_eq_add' (AlgebraicGeometry.properPushforward_add _ _ _)

/-- The summand of the linear extension. -/
noncomputable def AlgebraicGeometry.zeroSchemeCapTerm (d : ℕ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) (z : X) (w : X) : ℤ :=
  open Classical in
  if Order.height w = (d : ℕ∞) then a w * AlgebraicGeometry.zeroSchemeCapPoint L s w z else 0

theorem AlgebraicGeometry.zeroSchemeCapTerm_ne_zero {d : ℕ}
    {a : AlgebraicGeometry.AlgebraicCycle X ℤ} {z w : X}
    (h : AlgebraicGeometry.zeroSchemeCapTerm L s d a z w ≠ 0) :
    Order.height w = (d : ℕ∞) ∧ a w ≠ 0 ∧ AlgebraicGeometry.zeroSchemeCapPoint L s w z ≠ 0 := by
  unfold AlgebraicGeometry.zeroSchemeCapTerm at h
  split_ifs at h with hw
  · exact ⟨hw, left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  · exact absurd rfl h

theorem AlgebraicGeometry.zeroSchemeCapTerm_support_subset (d : ℕ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) {U : Set X} (hU : IsOpen U) {z : X} (hz : z ∈ U) :
    Function.support (AlgebraicGeometry.zeroSchemeCapTerm L s d a z) ⊆ U ∩ Function.support a := by
  intro w hw
  obtain ⟨-, ha, hc⟩ := AlgebraicGeometry.zeroSchemeCapTerm_ne_zero L s hw
  exact ⟨(AlgebraicGeometry.zeroSchemeCapPoint_specializes L s hc).mem_open hU hz, ha⟩

theorem AlgebraicGeometry.zeroSchemeCapTerm_support_finite (d : ℕ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) (z : X) :
    (Function.support (AlgebraicGeometry.zeroSchemeCapTerm L s d a z)).Finite := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  exact (a.locallyFiniteSupport.finite_inter_support_of_isCompact hU.isCompact).subset
    (AlgebraicGeometry.zeroSchemeCapTerm_support_subset L s d a U.isOpen hzU)

/-- `b = Σ_{height w = d} a(w)·B_w` (a pointwise finite sum; local finiteness as for `firstChernCapCycleAux`). -/
noncomputable def AlgebraicGeometry.zeroSchemeCapCycle (d : ℕ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ) : AlgebraicGeometry.AlgebraicCycle X ℤ where
  toFun := fun z => ∑ᶠ w : X, AlgebraicGeometry.zeroSchemeCapTerm L s d a z w
  supportWithinDomain' := fun _ _ => Set.mem_univ _
  supportLocallyFiniteWithinDomain' := by
    intro y _
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, U.isOpen.mem_nhds hyU, ?_⟩
    have hfin : ((U : Set X) ∩ Function.support a).Finite :=
      a.locallyFiniteSupport.finite_inter_support_of_isCompact hU.isCompact
    refine (hfin.biUnion (t := fun w => (U : Set X) ∩
      Function.support (AlgebraicGeometry.zeroSchemeCapPoint L s w)) fun w _ =>
        (AlgebraicGeometry.zeroSchemeCapPoint L s w).locallyFiniteSupport.finite_inter_support_of_isCompact
          hU.isCompact).subset ?_
    rintro z ⟨hzU, hz⟩
    have : ∃ w, AlgebraicGeometry.zeroSchemeCapTerm L s d a z w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz (by show (∑ᶠ w : X, _) = 0; simp [hall])
    obtain ⟨w, hw⟩ := this
    have hwU := AlgebraicGeometry.zeroSchemeCapTerm_support_subset L s d a U.isOpen hzU hw
    exact Set.mem_biUnion hwU ⟨hzU, (AlgebraicGeometry.zeroSchemeCapTerm_ne_zero L s hw).2.2⟩

theorem AlgebraicGeometry.exists_zeroSchemeCapTerm_ne_zero {d : ℕ}
    {a : AlgebraicGeometry.AlgebraicCycle X ℤ} {z : X}
    (hz : AlgebraicGeometry.zeroSchemeCapCycle L s d a z ≠ 0) :
    ∃ w, AlgebraicGeometry.zeroSchemeCapTerm L s d a z w ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hz (by show (∑ᶠ w : X, _) = 0; simp [hall])

end ZeroSchemeCap

/-- **Support refinement at the level of cycles**: for every `(d+1)`-cycle `a`, the cycle-level `c_1(L) ∩ a`
(`firstChernCapCycle`, with values in `CH_d(X)`) lies in the image of the pushforward from `D = Z(s)`.

Proof (the proof of Stacks 02T9): write `a = Σ_w n_w [closure{w}]` (`w` over the points with
`height w = d+1`, locally finite); `firstChernCapCycle` is by definition the class of
`firstChernCapCycleAux`, a locally finite sum of the terms `firstChernCapPoint L w`. Two cases at each point:
* **`w ∈ D`** (i.e. `s` lies in the ideal sheaf at `w`): the support of `capPoint L w` is already contained
  in `closure{w} ⊆ D`, so it is itself the pushforward along `ι` of a cycle on `D` — use
  `AlgebraicCycle.restrictClosed ι` to recover the cycle on `D`, then `properPushforward_restrictClosed`;
* **`w ∉ D`**: on `W_w = closure{w}` the section `s` restricts to a nonzero section, and
  `firstChernClass_fundamentalChowClass_eq_mk_rationalSectionDivisor` (the 02SJ family) with the comparison
  of the cap with the zero-scheme cycle give
  `capPoint L w − ι_{w*}[Z(ι_w^*s)] ∈ ratEquivZeroOn (closure{w})` (pushforward along `ι_w` by
  `properPushforward_pointClosure_mem_ratEquivZeroOn`), while the support of `[Z(ι_w^*s)]` lies in `D`
 (Stacks 02OR).
Finally sum the pointwise results as in `firstChernCapCycleAux_comm_mem`, using
`ratEquivZeroOn_le_ratEquivZero` and Stacks 02RZ.

Source: Stacks 02T9; 02RZ; 02OR. -/
theorem AlgebraicGeometry.firstChernCapCycle_mem_range_zeroScheme {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u)) (d : ℕ)
    (a : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (ha : a ∈ AlgebraicGeometry.cycleSubgroup X (d + 1)) :
    ∃ γ : AlgebraicGeometry.ChowGroup (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subscheme d,
      AlgebraicGeometry.chowPushforward
          (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι d γ
        = AlgebraicGeometry.firstChernCapCycle
            (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X)
            L (d + 1) a := by
  classical
  have hX := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  let I := AlgebraicGeometry.Scheme.idealSheafOfSection L s
  let b := AlgebraicGeometry.zeroSchemeCapCycle L s (d + 1) a
  -- `b ∈ Z_d(X)`, and `supp b ⊆ Z(s) = range ι`
  have hbZ : ∀ z, b z ≠ 0 → Order.height z = (d : ℕ∞) := by
    intro z hz
    obtain ⟨w, hw⟩ := AlgebraicGeometry.exists_zeroSchemeCapTerm_ne_zero L s hz
    obtain ⟨hwd, -, hc⟩ := AlgebraicGeometry.zeroSchemeCapTerm_ne_zero L s hw
    exact AlgebraicGeometry.zeroSchemeCapPoint_height L s hX hwd hc
  have hbD : Function.support (b : X → ℤ) ⊆ Set.range I.subschemeι.base := by
    intro z hz
    obtain ⟨w, hw⟩ := AlgebraicGeometry.exists_zeroSchemeCapTerm_ne_zero L s hz
    obtain ⟨-, -, hc⟩ := AlgebraicGeometry.zeroSchemeCapTerm_ne_zero L s hw
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    exact AlgebraicGeometry.zeroSchemeCapPoint_mem_support L s hc
  -- `capAux a − b` is rationally trivial (the pointwise differences are 02RW generators)
  have hdiff : AlgebraicGeometry.firstChernCapCycleAux L (d + 1) a - b ∈
      AlgebraicGeometry.ratEquivZero X d := by
    refine AlgebraicGeometry.mem_ratEquivZero_of_pointwise d a
      (fun w => AlgebraicGeometry.firstChernCapPoint L w - AlgebraicGeometry.zeroSchemeCapPoint L s w)
      (fun w hw => AlgebraicGeometry.isRatEquivGen_firstChernCapPoint_sub_zeroSchemeCapPoint L s hw)
      _ fun z => ?_
    show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L (d + 1) a z w) -
      (∑ᶠ w : X, AlgebraicGeometry.zeroSchemeCapTerm L s (d + 1) a z w) = _
    rw [← finsum_sub_distrib (AlgebraicGeometry.firstChernCapTerm_support_finite L _ a z)
      (AlgebraicGeometry.zeroSchemeCapTerm_support_finite L s _ a z)]
    refine finsum_congr fun w => ?_
    unfold AlgebraicGeometry.firstChernCapTerm AlgebraicGeometry.zeroSchemeCapTerm
    split_ifs
    · rw [← mul_sub]; rfl
    · simp
  have hmem : AlgebraicGeometry.AlgebraicCycle.restrictClosed I.subschemeι b ∈
      AlgebraicGeometry.cycleSubgroup I.subscheme d := by
    intro z' hz'
    rw [← AlgebraicGeometry.Scheme.Hom.height_of_isClosedImmersion I.subschemeι z']
    exact hbZ _ hz'
  refine ⟨AlgebraicGeometry.ChowGroup.mk ⟨_, hmem⟩, ?_⟩
  rw [AlgebraicGeometry.chowPushforward_mk _ d
    (AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion _ d)]
  show AlgebraicGeometry.ChowGroup.mk _ = AlgebraicGeometry.ChowGroup.mk
    ⟨AlgebraicGeometry.firstChernCapCycleAux L (d + 1) a,
      AlgebraicGeometry.firstChernCapCycleAux_mem hX L (d + 1) a⟩
  rw [← sub_eq_zero, ← map_sub, AlgebraicGeometry.ChowGroup.mk_eq_zero_iff]
  have hpush : AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι
      (AlgebraicGeometry.AlgebraicCycle.restrictClosed I.subschemeι b) = b :=
    AlgebraicGeometry.AlgebraicCycle.properPushforward_restrictClosed I.subschemeι b hbD
  have hneg := neg_mem hdiff
  rw [neg_sub] at hneg
  convert hneg using 1
  show AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι
      (AlgebraicGeometry.AlgebraicCycle.restrictClosed I.subschemeι b) -
    AlgebraicGeometry.firstChernCapCycleAux L (d + 1) a = _
  rw [hpush]
  all_goals rfl

/-- **Stacks 02T9 (support refinement)**: `c_1(L) ∩ α` is the pushforward of a class on `Z(s)`. Take a
representative of `α`, replace `c_1(L) ∩ −` on the Chow group by the cycle-level `firstChernCapCycle`
(`firstChernClass_mk`), and apply the previous lemma. -/
theorem AlgebraicGeometry.firstChernClass_mem_range_zeroScheme {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u)) (d : ℕ)
    (α : AlgebraicGeometry.ChowGroup X (d + 1)) :
    ∃ γ : AlgebraicGeometry.ChowGroup (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subscheme d,
      AlgebraicGeometry.chowPushforward (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι d γ
        = AlgebraicGeometry.firstChernClass L (d + 1) α := by
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((AlgebraicGeometry.ratEquivZero X (d + 1)).addSubgroupOf
      (AlgebraicGeometry.cycleSubgroup X (d + 1))) α
  show ∃ γ : AlgebraicGeometry.ChowGroup
      (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subscheme d,
      AlgebraicGeometry.chowPushforward
          (AlgebraicGeometry.Scheme.idealSheafOfSection L s).subschemeι d γ
        = AlgebraicGeometry.firstChernClass L (d + 1)
            (AlgebraicGeometry.ChowGroup.mk ⟨a, ha⟩)
  rw [AlgebraicGeometry.firstChernClass_mk (k := k) L (Nat.succ_pos d) a ha]
  exact AlgebraicGeometry.firstChernCapCycle_mem_range_zeroScheme (k := k) L s d a ha

end
