import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme

/-! # The pushforward of the fundamental class of a point closure is a single-point cycle

Cycle-level bookkeeping for the decomposition of a cycle class into the classes of its point-closure
components. Let `W_x := Z.pointClosure x` (the reduced induced closed subscheme of `x`, integral) and
`ι_x := Z.pointClosureι x` (a closed immersion). If `height x = d` then `dim W_x = d`,
`[W_x]_d = [η_{W_x}]` (`fundamentalCycle_of_isIntegral`), and pushing forward along the closed immersion
gives `ι_{x*}[W_x]_d = [x]` (`properPushforward_closedImmersion_apply`, `pointClosureι_genericPoint`). In
the Chow group, `chowPushforward ι_x d` is by definition `QuotientAddGroup.map` under `PushforwardDescends`
(Stacks 02S2, `properPushforward_rationallyEquivalent`, `Z` locally of finite type over a field), so
`ι_{x*}[W_x] = ChowGroup.mk [x]`.

Also: a cycle with finite support is the sum of its single-point cycles
(`AlgebraicCycle.eq_sum_single_of_finite_support`).

Source: Fulton, Intersection Theory, §1.3 / Stacks 02QU, 02QW, 02S2. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.PointClosurePushforwardSingle

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

open Classical in
/-- For `height x = d`, `[W_x]_d` is the single-point cycle with coefficient `1` at the generic point. -/
theorem fundamentalCycle_pointClosure_apply {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (x : Z) {d : ℕ}
    (hx : Order.height x = (d : ℕ∞)) (y : Z.pointClosure x) :
    (Z.pointClosure x).fundamentalCycle d y =
      if y = genericPoint (Z.pointClosure x) then 1 else 0 := by
  have hd : (Z.pointClosure x).dimension = d := AlgebraicGeometry.Scheme.dimension_pointClosure x hx
  have hfc := AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral (Z.pointClosure x)
    (by
      rw [AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure x hx]
      exact fun h => ENat.natCast_ne_top d (WithBot.coe_inj.mp h))
  rw [hd] at hfc
  rw [hfc]

open Classical in
/-- The coefficient of `ι_{x*}[W_x]_d` at `z`: `1` at `z = x`, `0` elsewhere. -/
theorem properPushforward_pointClosureι_fundamentalCycle_apply {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (x : Z) {d : ℕ} (hx : Order.height x = (d : ℕ∞)) (z : Z) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward (Z.pointClosureι x) ((Z.pointClosure x).fundamentalCycle d) z =
      if z = x then 1 else 0 := by
  by_cases hz : z ∈ Set.range (Z.pointClosureι x).base
  · obtain ⟨y, rfl⟩ := hz
    rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply,
      fundamentalCycle_pointClosure_apply x hx y]
    have hinj : Function.Injective (Z.pointClosureι x).base :=
      (Z.pointClosureι x).isClosedEmbedding.injective
    by_cases hy : y = genericPoint (Z.pointClosure x)
    · rw [if_pos hy, if_pos (by rw [hy, AlgebraicGeometry.Scheme.pointClosureι_genericPoint])]
    · rw [if_neg hy, if_neg]
      intro h
      apply hy
      apply hinj
      rw [h, AlgebraicGeometry.Scheme.pointClosureι_genericPoint]
  · rw [MiyaokaMori.ClosedImmersionPushforward.properPushforward_apply_of_notMem_range _ _ hz, if_neg]
    rintro rfl
    exact hz ⟨genericPoint (Z.pointClosure z), AlgebraicGeometry.Scheme.pointClosureι_genericPoint z⟩

open Classical in
/-- `ι_{x*}[W_x]_d = [x]` (at the level of cycles). -/
theorem properPushforward_pointClosureι_fundamentalCycle {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (x : Z) {d : ℕ} (hx : Order.height x = (d : ℕ∞)) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward (Z.pointClosureι x) ((Z.pointClosure x).fundamentalCycle d) =
      Function.locallyFinsuppWithin.single x (1 : ℤ) := by
  ext z
  rw [properPushforward_pointClosureι_fundamentalCycle_apply x hx z,
    Function.locallyFinsuppWithin.single_apply]

open Classical in
/-- The single-point cycle `[x]` lies in `Z_d` when `height x = d`. -/
theorem single_mem_cycleSubgroup {Z : AlgebraicGeometry.Scheme.{u}} (x : Z) {d : ℕ}
    (hx : Order.height x = (d : ℕ∞)) :
    Function.locallyFinsuppWithin.single x (1 : ℤ) ∈ AlgebraicGeometry.cycleSubgroup Z d := by
  intro y hy
  rw [Function.locallyFinsuppWithin.single_apply] at hy
  by_cases h : y = x
  · rw [h]; exact hx
  · exact absurd (if_neg h) hy

open Classical in
/-- **`ι_{x*}[W_x] = [x]` in the Chow group**: `Z` locally of finite type over a field `K`, `height x = d`. -/
theorem chowPushforward_pointClosureι_fundamentalChowClass {K : Type u} [Field K]
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsLocallyNoetherian Z]
    (x : Z) {d : ℕ} (hx : Order.height x = (d : ℕ∞)) :
    AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
        ((Z.pointClosure x).fundamentalChowClass d) =
      AlgebraicGeometry.ChowGroup.mk
        ⟨Function.locallyFinsuppWithin.single x (1 : ℤ), single_mem_cycleSubgroup x hx⟩ := by
  let _ : (Z.pointClosure x).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have : (Z.pointClosureι x).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : AlgebraicGeometry.LocallyOfFiniteType
      ((Z.pointClosure x) ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
      (Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))))
  have hdesc : AlgebraicGeometry.PushforwardDescends (Z.pointClosureι x) d := fun β γ hβγ =>
    AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent (k := K)
      (Z.pointClosureι x) d β γ hβγ
  have hp : AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d = QuotientAddGroup.map _ _
      (AlgebraicGeometry.cyclePushforwardHom (Z.pointClosureι x) d hdesc)
      (AlgebraicGeometry.cyclePushforwardHom_rel (Z.pointClosureι x) d hdesc) := by
    unfold AlgebraicGeometry.chowPushforward
    exact dif_pos hdesc
  rw [hp]
  unfold AlgebraicGeometry.Scheme.fundamentalChowClass
  change AlgebraicGeometry.ChowGroup.mk (AlgebraicGeometry.cyclePushforwardHom (Z.pointClosureι x) d
    hdesc ⟨(Z.pointClosure x).fundamentalCycle d, _⟩) = AlgebraicGeometry.ChowGroup.mk ⟨_, _⟩
  congr 1
  exact Subtype.ext (properPushforward_pointClosureι_fundamentalCycle x hx)

open Classical in
/-- A cycle with finite support is the `ℤ`-linear combination of the single-point cycles at the points
of its support. -/
theorem _root_.AlgebraicGeometry.AlgebraicCycle.eq_sum_single_of_finite_support
    {Z : AlgebraicGeometry.Scheme.{u}} (c : AlgebraicGeometry.AlgebraicCycle Z ℤ)
    (hfin : (Function.support c).Finite) :
    c = ∑ x ∈ hfin.toFinset, c x • Function.locallyFinsuppWithin.single x (1 : ℤ) := by
  ext z
  have hsum := congrFun (Function.locallyFinsuppWithin.coe_sum (s := hfin.toFinset)
    (F := fun x => c x • Function.locallyFinsuppWithin.single x (1 : ℤ))) z
  rw [hsum, Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul]
  by_cases hz : z ∈ hfin.toFinset
  · rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h; exact absurd hz h
  · have hz0 : c z = 0 := by simpa using hz
    rw [hz0]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxz : z = x
    · subst hxz; rw [hz0, zero_mul]
    · rw [if_neg hxz, mul_zero]

end MiyaokaMori.PointClosurePushforwardSingle

end
