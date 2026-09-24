import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdCoordinate

/-! # The cap with the trivial line bundle vanishes at the level of cycles

Let `X` be locally Noetherian and locally of finite type over some field (**no quasi-compactness**). Then
the cycle-level `c_1(O_X) ∩ −` is identically zero: for every `d` and cycle `β`,
`firstChernCapCycle hX (SheafOfModules.unit _) d β = 0 ∈ CH_{d−1}(X)` (the case `c_1(O)` of Stacks 02SP).
Also: (i) for `d = 0` and any line bundle `L`, `firstChernCapCycleAux L 0 α = 0`;
(ii) `firstChernCapCycleAux L (d+1) β` is a **locally finite** ℤ-linear combination of the
`firstChernCapPoint L w` (`height w = d+1`), indexed by the support of `β`
(`firstChernCapCycleAux_mem_ratEquivZeroOn`).

Proof:
1. (i): for `height w = 0`, `W_w` has no point of coheight `1`, while the support points of `capPoint` all
   come from points of coheight `1` (`firstChernCapPoint_ne_zero`), so `capPoint L w = 0` and every term of
   the linear extension vanishes.
2. (ii): restrict the pointwise `finsum` to `S = {w | height w = d+1 ∧ β w ≠ 0}`
   (`finsum_mem_inter_support_eq` + `finsum_set_coe_eq_finsum_mem`); `S`, a subset of the support of `β`, is
   a locally finite family of points; each term `β w • capPoint L w` is still generating data of Stacks 02RW
   by `IsRatEquivGen.zsmul` (`div(f^n) = n·div(f)`).
3. Single point: `capPoint O_X w = ι_{w*} div_{ι_w^*O_X}(s_ε)`, with `s_ε` the chosen nonzero rational section
   (existence: `exists_stalk_genericPoint_ne_zero`). `ι_w^*O_X ≅ O_{W_w}` (`pullbackUnitIso`), and
   `div(s_ε) = div(g)` is a principal cycle (rational sections of the trivial bundle are functions); so for
   `height w = d + 1`, `capPoint O_X w` is exactly a generator of `ratEquivZero X d`.
4. Together: for `d = d' + 1`, `Aux ∈ ratEquivZero X d'` and `ChowGroup.mk` of it is zero
   (`QuotientAddGroup.eq_zero_iff`); for `d = 0` use (i).

No quasi-compactness is needed because `ratEquivZero` allows the locally finite sums of Stacks 02RW: for
`X = ∐_{i∈ℕ} P^1` and `β = Σ_i [P^1_i]`, `c_1(O) ∩ β` is a locally finite sum of infinitely many principal
cycles, which is indeed zero in `CH_0(X)` (the Example of Stacks 02RS).

Source: Stacks 02SP (`c_1(O_X) ∩ α = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]

/-- Points of height `0` do not contribute to `c_1(L) ∩ −`. -/
theorem firstChernCapPoint_eq_zero_of_height_eq_zero (L : X.Modules) [L.IsLineBundle] {w : X}
    (hw : Order.height w = 0) : AlgebraicGeometry.firstChernCapPoint L w = 0 := by
  ext z
  show AlgebraicGeometry.firstChernCapPoint L w z = 0
  by_contra h
  obtain ⟨z', -, -, hco⟩ := AlgebraicGeometry.firstChernCapPoint_ne_zero L h
  exact AlgebraicGeometry.Scheme.coheight_ne_one_of_height_eq_zero hw z' hco

/-- (i) For `d = 0` the linear extension vanishes identically. -/
theorem firstChernCapCycleAux_dim_zero (L : X.Modules) [L.IsLineBundle]
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L 0 α = 0 := by
  ext z
  show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L 0 α z w) = 0
  refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
  unfold AlgebraicGeometry.firstChernCapTerm
  split_ifs with hw
  · have hw0 : Order.height w = 0 := by exact_mod_cast hw
    rw [AlgebraicGeometry.firstChernCapPoint_eq_zero_of_height_eq_zero L hw0]
    exact mul_zero _
  · rfl

theorem firstChernCapCycle_dim_zero (hX : X.IsLocallyOfFiniteTypeOverField) (L : X.Modules)
    [L.IsLineBundle] (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycle hX L 0 α = 0 := by
  show AlgebraicGeometry.ChowGroup.mk
    ⟨AlgebraicGeometry.firstChernCapCycleAux L 0 α,
      AlgebraicGeometry.firstChernCapCycleAux_mem hX L 0 α⟩ = 0
  have h0 : (⟨AlgebraicGeometry.firstChernCapCycleAux L 0 α,
      AlgebraicGeometry.firstChernCapCycleAux_mem hX L 0 α⟩ :
        ↥(AlgebraicGeometry.cycleSubgroup X (0 - 1))) = 0 :=
    Subtype.ext (AlgebraicGeometry.firstChernCapCycleAux_dim_zero L α)
  rw [h0, map_zero]

/-- For `X` quasi-compact: the linear extension is a **finite** ℤ-linear combination of the single-point
contributions, and lies in any subgroup containing them. Superseded by `firstChernCapCycleAux_mem_ratEquivZero`
(which needs no quasi-compactness), but kept since it holds for an arbitrary subgroup `H`. -/
theorem firstChernCapCycleAux_mem_of_forall [CompactSpace X] (L : X.Modules) [L.IsLineBundle]
    (d : ℕ) (H : AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ))
    (hH : ∀ w : X, Order.height w = (d : ℕ∞) → AlgebraicGeometry.firstChernCapPoint L w ∈ H)
    (β : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L d β ∈ H := by
  classical
  have hfin : (Function.support β).Finite := by
    have := β.locallyFiniteSupport.finite_inter_support_of_isCompact (isCompact_univ (X := X))
    simpa using this
  have key : AlgebraicGeometry.firstChernCapCycleAux L d β =
      ∑ w ∈ hfin.toFinset, (if Order.height w = (d : ℕ∞) then
        β w • AlgebraicGeometry.firstChernCapPoint L w else 0) := by
    ext z
    let ev : AlgebraicGeometry.AlgebraicCycle X ℤ →+ ℤ :=
      { toFun := fun c => c z, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L d β z w) = ev _
    rw [map_sum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun w _ => ?_
      unfold AlgebraicGeometry.firstChernCapTerm
      split_ifs
      · rw [map_zsmul, smul_eq_mul]; rfl
      · exact (map_zero ev).symm
    · intro w hw
      have := (AlgebraicGeometry.firstChernCapTerm_ne_zero L hw).2.1
      simpa using this
  rw [key]
  refine H.sum_mem fun w _ => ?_
  split_ifs with h
  · exact H.zsmul_mem (hH w h) _
  · exact H.zero_mem

omit [AlgebraicGeometry.IsLocallyNoetherian X] in
/-- For `X` quasi-compact, point closures are quasi-compact. -/
theorem Scheme.compactSpace_pointClosure [CompactSpace X] (w : X) :
    CompactSpace (X.pointClosure w) :=
  (X.pointClosureι w).isClosedEmbedding.compactSpace

/-- Single point: the representative of `c_1(O_X) ∩ [closure{w}]` **is** generating data of Stacks 02RW (with
generic point `w`). The conclusion is the generator form `IsRatEquivGen` rather than mere membership in
`ratEquivZero`: a locally finite sum needs to know the `W_j` of each term in order to verify that `{W_j}` is
locally finite (the requirement of Stacks 02RW). -/
theorem firstChernCapPoint_unit_isRatEquivGen {d : ℕ} {w : X}
    (hw : Order.height w = ((d + 1 : ℕ) : ℕ∞)) :
    AlgebraicGeometry.IsRatEquivGen X d w
      (AlgebraicGeometry.firstChernCapPoint (X := X) (SheafOfModules.unit X.ringCatSheaf) w) := by
  have hint : AlgebraicGeometry.IsIntegral (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isIntegral_pointClosure w
  have hLN : AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w) :=
    AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure w
  let Lw : (X.pointClosure w).Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj
      (SheafOfModules.unit X.ringCatSheaf)
  have : Lw.IsLineBundle := SheafOfModules.IsLineBundle.pullback (X.pointClosureι w) _
  let s : Lw.stalk (genericPoint (X.pointClosure w)) := Classical.epsilon fun t => t ≠ 0
  have hs : s ≠ 0 :=
    Classical.epsilon_spec (AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero Lw)
  obtain ⟨g, hg⟩ :=
    AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_eq_principalCycle_of_iso_unit Lw
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (X.pointClosureι w)) s hs
  have hcap : AlgebraicGeometry.firstChernCapPoint (X := X) (SheafOfModules.unit X.ringCatSheaf) w =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) (Lw.rationalSectionDivisor s) := rfl
  exact ⟨hw, hint, inferInstance, hLN, g, by rw [hcap, hg]⟩

theorem firstChernCapPoint_unit_mem_ratEquivZero {d : ℕ} {w : X}
    (hw : Order.height w = ((d + 1 : ℕ) : ℕ∞)) :
    AlgebraicGeometry.firstChernCapPoint (X := X) (SheafOfModules.unit X.ringCatSheaf) w ∈
      AlgebraicGeometry.ratEquivZero X d :=
  AlgebraicGeometry.single_mem_ratEquivZero (firstChernCapPoint_unit_isRatEquivGen hw)

/-- **Without quasi-compactness**: `firstChernCapCycleAux L (d+1) β` is a **locally finite** ℤ-linear
combination of the `firstChernCapPoint L w` (`height w = d+1`), indexed by the (locally finite) support of
`β`. If every single-point contribution is generating data of Stacks 02RW with generic point `w`, the whole
sum lies in `ratEquivZero X d`.

This replaces `firstChernCapCycleAux_mem_of_forall` (which needs `[CompactSpace X]` to turn the pointwise
`finsum` into a finite `Finset` sum); the difference is exactly the point made at the start of Stacks 02RV. -/
theorem firstChernCapCycleAux_mem_ratEquivZero (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (hgen : ∀ w : X, Order.height w = ((d + 1 : ℕ) : ℕ∞) →
      AlgebraicGeometry.IsRatEquivGen X d w (AlgebraicGeometry.firstChernCapPoint L w))
    (β : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L (d + 1) β ∈ AlgebraicGeometry.ratEquivZero X d := by
  classical
  set S : Set X := {w : X | Order.height w = ((d + 1 : ℕ) : ℕ∞) ∧ β w ≠ 0} with hSdef
  refine ⟨↥S, fun j => (j : X),
    fun j => β (j : X) • AlgebraicGeometry.firstChernCapPoint L (j : X),
    fun _ => Set.mem_univ _, fun j => (hgen (j : X) j.2.1).zsmul _,
    AlgebraicGeometry.locallyFinitePoints_of_subset_support β (fun w hw => hw.2), fun z => ?_⟩
  have hsupp : Function.support (AlgebraicGeometry.firstChernCapTerm L (d + 1) β z) ⊆ S := by
    intro w hw
    obtain ⟨h1, h2, -⟩ := AlgebraicGeometry.firstChernCapTerm_ne_zero L hw
    exact ⟨h1, h2⟩
  have hinter : Set.univ ∩ Function.support (AlgebraicGeometry.firstChernCapTerm L (d + 1) β z)
      = S ∩ Function.support (AlgebraicGeometry.firstChernCapTerm L (d + 1) β z) := by
    rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]
  have hterm : ∀ j : ↥S,
      AlgebraicGeometry.firstChernCapTerm L (d + 1) β z (j : X)
        = (β (j : X) • AlgebraicGeometry.firstChernCapPoint L (j : X)) z := by
    intro j
    unfold AlgebraicGeometry.firstChernCapTerm
    rw [if_pos j.2.1, AlgebraicGeometry.AlgebraicCycle.zsmul_apply]
  show (∑ᶠ w : X, AlgebraicGeometry.firstChernCapTerm L (d + 1) β z w) = _
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ S hinter,
    ← finsum_set_coe_eq_finsum_mem]
  exact finsum_congr hterm

/-- `c_1(O_X) ∩ − = 0` (at the level of cycles, with values in the Chow group; the case `c_1(O)` of
Stacks 02SP). No quasi-compactness is needed: `ratEquivZero` allows the locally finite sums of Stacks 02RW,
and `firstChernCapCycleAux` is exactly the sum of the single-point contributions over the (locally finite)
support of `β`. -/
theorem firstChernCapCycle_unit_eq_zero (hX : X.IsLocallyOfFiniteTypeOverField)
    (d : ℕ) (β : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.firstChernCapCycle (X := X) hX (SheafOfModules.unit X.ringCatSheaf) d β = 0 := by
  cases d with
  | zero => exact AlgebraicGeometry.firstChernCapCycle_dim_zero hX _ β
  | succ d =>
    show AlgebraicGeometry.ChowGroup.mk
      ⟨AlgebraicGeometry.firstChernCapCycleAux (X := X) (SheafOfModules.unit X.ringCatSheaf) (d + 1) β,
        AlgebraicGeometry.firstChernCapCycleAux_mem hX _ (d + 1) β⟩ = 0
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    exact AlgebraicGeometry.firstChernCapCycleAux_mem_ratEquivZero _ d
      (fun w hw => AlgebraicGeometry.firstChernCapPoint_unit_isRatEquivGen hw) β

end AlgebraicGeometry

end
