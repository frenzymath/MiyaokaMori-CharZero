import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedInducedSubschemeIntegral
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21

/-! # The cap with the first Chern class at the level of cycles

The cycle-level `c_1(L) ∩ −`: for a `d`-dimensional integral closed subscheme `W` (the closure of a point
`w` of height `d`, with reduced structure) take a nonzero meromorphic section `s` of `L|_W`, let
`c_1(L) ∩ [W]` be the class of `i_*div_{L|_W}(s)`, and extend linearly to `d`-cycles (Stacks 02SJ + 02SO).
This is the first layer of the construction of `firstChernClass`.

Source: Stacks 02SJ, 02SO (the definition of the cap on cycles). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `X` is locally of finite type over some field (the setting of Stacks 02SJ / 02SO with `S = Spec k`).
Stated as a proposition without the parameter `k`, so that users of `firstChernCapCycle` (including
`firstChernClass`, stated for arbitrary schemes with a `dite`) can pass it as an explicit hypothesis. -/
def AlgebraicGeometry.Scheme.IsLocallyOfFiniteTypeOverField (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∃ (k : Type u) (_ : Field k) (π : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)),
    AlgebraicGeometry.LocallyOfFiniteType π

theorem AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] :
    X.IsLocallyOfFiniteTypeOverField :=
  ⟨k, inferInstance, X ↘ AlgebraicGeometry.Spec (CommRingCat.of k), inferInstance⟩

/-- The reduced induced structure on `closure{w}` is locally Noetherian: a closed immersion is locally of
finite type. -/
theorem AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (w : X) :
    AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w) := by
  have : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι w) := by
    unfold AlgebraicGeometry.Scheme.pointClosureι; exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι _
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (X.pointClosureι w)

/- `c_1(L) ∩ −` at the level of cycles (Stacks 02SJ + 02SO): for a point `w` of height `d`, let
   `W_w := X.pointClosure w` (the reduced induced structure on `closure{w}`, integral) and `ι_w` the closed
   immersion; take a nonzero element `s_w` (a rational section) of the stalk of `ι_w^*L` at the generic
   point and set `c_1(L) ∩ [w] := ι_{w*} div_{ι_w^*L}(s_w)`; extend linearly over the points of `α`
   (pointwise finite sums), and finally take the class in `CH_{d−1}(X)`. -/

/-- The contribution of a single point `w` (at the level of cycles): a representative
`ι_{w*} div_{ι_w^*L}(s_w)` of `c_1(L) ∩ [closure{w}]`. -/
noncomputable def AlgebraicGeometry.firstChernCapPoint {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (w : X) :
    AlgebraicGeometry.AlgebraicCycle X ℤ :=
  -- the reduced induced structure on `closure{w}` is integral and locally Noetherian (`X` locally Noetherian)
  haveI : AlgebraicGeometry.IsIntegral (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isIntegral_pointClosure w
  haveI : AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure w
  -- `ι_w` is a closed immersion (Mathlib's `subschemeι` instance), hence proper
  haveI : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι w) := by
    unfold AlgebraicGeometry.Scheme.pointClosureι; exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι _
  haveI : AlgebraicGeometry.IsProper (X.pointClosureι w) := inferInstance
  let Lw := (AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L
  -- the rational section `s_w`: choose a nonzero element with Hilbert's ε (the stalk of a line bundle at
  -- the generic point of an integral scheme is nonzero, so the chosen element is indeed nonzero; the
  -- resulting class is independent of the choice by Stacks 02SH)
  let s : Lw.stalk (genericPoint (X.pointClosure w)) := Classical.epsilon fun t => t ≠ 0
  AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) (Lw.rationalSectionDivisor s)

/-- Every support point `z` of `capPoint` comes from a point of `W_w` of coheight `1` and of the same height
as `z` (the pushforward only keeps points of equal height). -/
theorem AlgebraicGeometry.firstChernCapPoint_ne_zero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {w z : X}
    (h : AlgebraicGeometry.firstChernCapPoint L w z ≠ 0) :
    ∃ z' : X.pointClosure w, (X.pointClosureι w).base z' = z ∧ Order.height z' = Order.height z ∧
      Order.coheight z' = 1 := by
  have : AlgebraicGeometry.IsIntegral (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isIntegral_pointClosure w
  have : AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure w
  unfold AlgebraicGeometry.firstChernCapPoint AlgebraicGeometry.AlgebraicCycle.properPushforward
    AlgebraicGeometry.AlgebraicCycle.map at h
  simp only [Function.locallyFinsupp.map_apply] at h
  obtain ⟨z', hz', hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  refine ⟨z', hz', ?_, ?_⟩
  · by_contra hht
    apply hne
    have : Order.height z' ≠ Order.height ((X.pointClosureι w).base z') := by rwa [hz']
    simp [AlgebraicGeometry.AlgebraicCycle.mapCoeff, this]
  · exact AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support _ _ z'
      (left_ne_zero_of_mul hne)

/-- A closed immersion preserves the height of points (= the dimension of the closure): the points below
`f y` all lie in the closed set `range f`. -/
private theorem height_eq_of_isClosedImmersion {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] (y : Y) :
    Order.height (f.base y) = Order.height y := by
  have hiff : ∀ a b : Y, f.base a ≤ f.base b ↔ a ≤ b := fun a b =>
    f.isClosedEmbedding.isInducing.specializes_iff
  have hlt : ∀ a b : Y, f.base a < f.base b ↔ a < b := fun a b => by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hiff, hiff]
  refine le_antisymm ?_ (Order.height_le_height_apply_of_strictMono _ (fun a b hab => (hlt a b).mpr hab) y)
  refine Order.height_le_iff.mpr fun p hp => ?_
  have hrange : ∀ i, p i ∈ Set.range f.base := fun i => by
    have h1 : p i ≤ f.base y := (p.monotone (Fin.le_last i)).trans hp
    have h2 : p i ∈ closure {f.base y} := (specializes_iff_mem_closure).mp h1
    exact (f.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨y, rfl⟩)) h2
  choose g hg using hrange
  let q : LTSeries Y := ⟨p.length, g, fun i => by
    have := p.step i
    rw [← hg, ← hg] at this
    exact (hlt _ _).mp this⟩
  have hq : q.last ≤ y := by
    rw [← hiff]
    show f.base (g _) ≤ _
    rw [hg]; exact hp
  exact Order.length_le_height (p := q) hq

/-- The Krull dimension of the underlying space of a scheme (specialization order) is its topological Krull
dimension. -/
private theorem krullDim_scheme_eq_topologicalKrullDim' (X : AlgebraicGeometry.Scheme.{u}) :
    Order.krullDim X = topologicalKrullDim X :=
  (Order.krullDim_eq_of_orderIso
    (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm

/-- Dimension formula: if `X` is locally of finite type over a field and `height w = d`, then the support
points of `capPoint w` all have height `d − 1` (in particular `d ≥ 1`). `W_w` is an integral scheme locally
of finite type over a field with `dim W_w = height w = d`, and Stacks 0A21(4)
(`height_add_coheight_eq_of_locallyOfFiniteType`) gives `height z' + 1 = d`. -/
theorem AlgebraicGeometry.firstChernCapPoint_height {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (hX : X.IsLocallyOfFiniteTypeOverField)
    (L : X.Modules) [L.IsLineBundle] {d : ℕ} {w z : X} (hw : Order.height w = (d : ℕ∞))
    (h : AlgebraicGeometry.firstChernCapPoint L w z ≠ 0) :
    Order.height z = ((d - 1 : ℕ) : ℕ∞) := by
  obtain ⟨k, _, π, _⟩ := hX
  obtain ⟨z', -, hht, hco⟩ := AlgebraicGeometry.firstChernCapPoint_ne_zero L h
  have : AlgebraicGeometry.IsIntegral (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isIntegral_pointClosure w
  have : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι w) := by
    unfold AlgebraicGeometry.Scheme.pointClosureι; exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι _
  let _ : (X.pointClosure w).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨X.pointClosureι w ≫ π⟩
  have : AlgebraicGeometry.LocallyOfFiniteType
      ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (X.pointClosureι w ≫ π))
  have hdim : topologicalKrullDim (X.pointClosure w) = ((d : ℕ) : WithBot ℕ∞) := by
    rw [← krullDim_scheme_eq_topologicalKrullDim', ← Order.height_top_eq_krullDim]
    have h1 : Order.height (⊤ : X.pointClosure w) = (d : ℕ∞) := by
      rw [← hw, ← height_eq_of_isClosedImmersion (X.pointClosureι w)]
      congr 1
      exact AlgebraicGeometry.Scheme.pointClosureι_genericPoint w
    rw [h1]; rfl
  have hadd := AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := k)
    (X.pointClosure w) d hdim z'
  rw [hht, hco] at hadd
  have hne : Order.height z ≠ ⊤ := by
    intro ht; rw [ht] at hadd; simp at hadd
  lift Order.height z to ℕ using hne with n
  have : n + 1 = d := by exact_mod_cast hadd
  have : n = d - 1 := by omega
  exact_mod_cast this

/-- The support of `capPoint w` lies in `closure{w}`. -/
theorem AlgebraicGeometry.firstChernCapPoint_specializes {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {w z : X}
    (h : AlgebraicGeometry.firstChernCapPoint L w z ≠ 0) : w ⤳ z := by
  obtain ⟨z', rfl, -, -⟩ := AlgebraicGeometry.firstChernCapPoint_ne_zero L h
  rw [specializes_iff_mem_closure]
  have hr := AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨closure {w}, isClosed_closure⟩)
  rw [AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal] at hr
  exact hr.subset ⟨z', rfl⟩

/-- The summand of the linear extension: `w ↦ [height w = d] · α(w) · (c_1(L) ∩ [w])(z)`. -/
noncomputable def AlgebraicGeometry.firstChernCapTerm {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (z : X) (w : X) : ℤ :=
  open Classical in
  if Order.height w = (d : ℕ∞) then α w * AlgebraicGeometry.firstChernCapPoint L w z else 0

theorem AlgebraicGeometry.firstChernCapTerm_ne_zero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {d : ℕ}
    {α : AlgebraicGeometry.AlgebraicCycle X ℤ} {z w : X}
    (h : AlgebraicGeometry.firstChernCapTerm L d α z w ≠ 0) :
    Order.height w = (d : ℕ∞) ∧ α w ≠ 0 ∧ AlgebraicGeometry.firstChernCapPoint L w z ≠ 0 := by
  unfold AlgebraicGeometry.firstChernCapTerm at h
  split_ifs at h with hw
  · exact ⟨hw, left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  · exact absurd rfl h

/-- Inside a compact open `U` containing `z`, only the `w ∈ U ∩ supp α` contribute at `z` (open sets are
closed under generization). -/
theorem AlgebraicGeometry.firstChernCapTerm_support_subset {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) {U : Set X} (hU : IsOpen U) {z : X} (hz : z ∈ U) :
    Function.support (AlgebraicGeometry.firstChernCapTerm L d α z) ⊆ U ∩ Function.support α := by
  intro w hw
  obtain ⟨-, hα, hc⟩ := AlgebraicGeometry.firstChernCapTerm_ne_zero L hw
  exact ⟨(AlgebraicGeometry.firstChernCapPoint_specializes L hc).mem_open hU hz, hα⟩

theorem AlgebraicGeometry.firstChernCapTerm_support_finite {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (z : X) :
    (Function.support (AlgebraicGeometry.firstChernCapTerm L d α z)).Finite := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  exact (α.locallyFiniteSupport.finite_inter_support_of_isCompact hU.isCompact).subset
    (AlgebraicGeometry.firstChernCapTerm_support_subset L d α U.isOpen hzU)

/-- The linear extension (at the level of cycles): `α ↦ Σ_{height w = d} α(w)·(c_1(L) ∩ [w])`, a finite sum
at each point; local finiteness is proved here. -/
noncomputable def AlgebraicGeometry.firstChernCapCycleAux {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) : AlgebraicGeometry.AlgebraicCycle X ℤ where
  toFun := fun z => ∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d α z w
  supportWithinDomain' := fun _ _ => Set.mem_univ _
  supportLocallyFiniteWithinDomain' := by
    intro y _
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine ⟨U, U.isOpen.mem_nhds hyU, ?_⟩
    have hfin : ((U : Set X) ∩ Function.support α).Finite :=
      α.locallyFiniteSupport.finite_inter_support_of_isCompact hU.isCompact
    refine (hfin.biUnion (t := fun w => (U : Set X) ∩
      Function.support (AlgebraicGeometry.firstChernCapPoint L w)) fun w _ =>
        (AlgebraicGeometry.firstChernCapPoint L w).locallyFiniteSupport.finite_inter_support_of_isCompact
          hU.isCompact).subset ?_
    rintro z ⟨hzU, hz⟩
    have : ∃ w, AlgebraicGeometry.firstChernCapTerm L d α z w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz (by show (∑ᶠ w : X, _) = 0; simp [hall])
    obtain ⟨w, hw⟩ := this
    have hwU := AlgebraicGeometry.firstChernCapTerm_support_subset L d α U.isOpen hzU hw
    exact Set.mem_biUnion hwU ⟨hzU, (AlgebraicGeometry.firstChernCapTerm_ne_zero L hw).2.2⟩

theorem AlgebraicGeometry.firstChernCapCycleAux_mem {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (hX : X.IsLocallyOfFiniteTypeOverField)
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L d α ∈ AlgebraicGeometry.cycleSubgroup X (d - 1) := by
  intro z hz
  have : ∃ w, AlgebraicGeometry.firstChernCapTerm L d α z w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz (by show (∑ᶠ w : X, _) = 0; simp [hall])
  obtain ⟨w, hw⟩ := this
  obtain ⟨hwd, -, hc⟩ := AlgebraicGeometry.firstChernCapTerm_ne_zero L hw
  exact AlgebraicGeometry.firstChernCapPoint_height hX L hwd hc

theorem AlgebraicGeometry.firstChernCapCycleAux_zero {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ) :
    AlgebraicGeometry.firstChernCapCycleAux L d 0 = 0 := by
  ext z
  show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d 0 z w) = 0
  simp [AlgebraicGeometry.firstChernCapTerm]

theorem AlgebraicGeometry.firstChernCapCycleAux_add {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α β : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L d (α + β) =
      AlgebraicGeometry.firstChernCapCycleAux L d α + AlgebraicGeometry.firstChernCapCycleAux L d β := by
  ext z
  show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d (α + β) z w) =
    (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d α z w) +
      ∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d β z w
  rw [← finsum_add_distrib (AlgebraicGeometry.firstChernCapTerm_support_finite L d α z)
    (AlgebraicGeometry.firstChernCapTerm_support_finite L d β z)]
  refine finsum_congr fun w => ?_
  unfold AlgebraicGeometry.firstChernCapTerm
  split_ifs
  · show (α w + β w) * _ = _
    rw [add_mul]
  · simp

/-- The cycle-level `c_1(L) ∩ −` (Stacks 02SJ + 02SO).

The hypothesis `hX : X.IsLocallyOfFiniteTypeOverField` (the setting of Stacks 02SJ) is needed: the support
points of `div_{L|_W}(s)` are only known to have coheight `1`, while `Z_{d−1}(X)` is graded by `Order.height`
(dimension of the closure), and `height + coheight = dim` needs a catenary, equidimensional situation. A
counterexample without it is a Nagata-type two-dimensional Noetherian domain with a maximal ideal `m₁` of
height `1` (`X = W = Spec A`, `d = 2`, `div(s)` nonzero at `m₁` while `height m₁ = 0 ≠ 1`). The membership
obligation is `firstChernCapCycleAux_mem` (the dimension formula of Stacks 0A21(4)).

For `d = 0`: the closure of a point of height `0` is zero-dimensional and has no point of coheight `1`, so
the map is identically `0` (writing the codomain as `CH_{0−1} = CH_0` is only the notation of `ℕ`
truncation); `firstChernClass` uses it only for `0 < d`. -/
noncomputable def AlgebraicGeometry.firstChernCapCycle {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (hX : X.IsLocallyOfFiniteTypeOverField)
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) :
    AlgebraicGeometry.AlgebraicCycle X ℤ →+ AlgebraicGeometry.ChowGroup X (d - 1) where
  toFun := fun α => AlgebraicGeometry.ChowGroup.mk
    ⟨AlgebraicGeometry.firstChernCapCycleAux L d α,
      AlgebraicGeometry.firstChernCapCycleAux_mem hX L d α⟩
  map_zero' := by
    rw [← map_zero AlgebraicGeometry.ChowGroup.mk]
    congr 1
    exact Subtype.ext (AlgebraicGeometry.firstChernCapCycleAux_zero L d)
  map_add' := fun α β => by
    rw [← map_add]
    congr 1
    exact Subtype.ext (AlgebraicGeometry.firstChernCapCycleAux_add L d α β)

end
