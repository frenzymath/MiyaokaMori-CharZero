import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointClosurePushforward

/-! # The projection formula along the closed immersion of a point closure (Stacks 02SU)

Let `X` be locally Noetherian and locally of finite type over a field, `W = X.pointClosure w` and
`ι = ι_w`. Then
(D) `pushforwardDescends_of_isClosedImmersion`: the pushforward along **any** closed immersion `i`
preserves rational equivalence (`PushforwardDescends i p`, i.e. `chowPushforward i p` takes its positive
branch; the closed-immersion case of Stacks 02S2, no finite type over a field needed);
(U) `chowPushforward_firstChernCapCycle_pullback_pointClosureι`: in the Chow group,
`ι_*(c_1(ι^*L) ∩ α) = c_1(L) ∩ ι_*α` (this special case of Stacks 02SU, for every cycle `α` on `W`).
This is all of 02SU/02S2 that Stacks 02TH and 02TI actually use: they only push forward along closed
immersions of point closures.

Proof:
1. (D): a closed immersion preserves heights, hence `Z_p`; `ι_*(α − β)` is rationally trivial by
   `ClosedImmersionPushforwardRatEquiv.lean`.
2. (U): `chowPushforward` takes its positive branch by (D); both sides are images under `ChowGroup.mk`, and
   the difference is rationally trivial by `FirstChernCapPointClosurePushforward.lean`.

Source: Stacks 02S2, 02SU (the case where `p` is the closed immersion of an integral closed subscheme).

Implementation note: `chowPushforward` is written with its full name `AlgebraicGeometry.chowPushforward`
(this module is inside `namespace AlgebraicGeometry`), to avoid the overload with the variety-level name.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open MiyaokaMori.ClosedImmersionPushforward MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.FirstChernCapPointClosurePushforward

/-- A Chow class is zero iff the representing cycle is rationally trivial (API lemma). -/
theorem ChowGroup.mk_eq_zero_iff {X : Scheme.{u}} {p : ℕ} (c : ↥(cycleSubgroup X p)) :
    ChowGroup.mk c = 0 ↔ (c : AlgebraicCycle X ℤ) ∈ ratEquivZero X p :=
  (QuotientAddGroup.eq_zero_iff _).trans AddSubgroup.mem_addSubgroupOf

/-- The pushforward along a closed immersion preserves `Z_p`. -/
theorem properPushforward_mem_cycleSubgroup_of_isClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (p : ℕ) {c : AlgebraicCycle W ℤ} (hc : c ∈ cycleSubgroup W p) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i c ∈ cycleSubgroup X p := by
  intro z hz
  by_cases hr : z ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hr
    rw [properPushforward_closedImmersion_apply] at hz
    exact (Scheme.Hom.height_of_isClosedImmersion i z').trans (hc z' hz)
  · exact absurd (properPushforward_apply_of_notMem_range i c hr) hz

/-- (D) The pushforward along **any** closed immersion preserves rational equivalence (the closed-immersion
case of Stacks 02S2; no finite type over a field is needed). -/
theorem pushforwardDescends_of_isClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (p : ℕ) : PushforwardDescends i p := by
  rintro α β ⟨hα, hβ, hsub⟩
  refine ⟨properPushforward_mem_cycleSubgroup_of_isClosedImmersion _ p hα,
    properPushforward_mem_cycleSubgroup_of_isClosedImmersion _ p hβ, ?_⟩
  have h : AlgebraicGeometry.AlgebraicCycle.properPushforward i α - AlgebraicGeometry.AlgebraicCycle.properPushforward i β =
      AlgebraicGeometry.AlgebraicCycle.properPushforward i (α - β) :=
    ((AlgebraicCycle.properPushforwardHom i).map_sub α β).symm
  rw [h]
  exact ratEquivZeroOn_le_ratEquivZero _
    (properPushforward_mem_ratEquivZeroOn_of_isClosedImmersion i p _ hsub)

theorem pushforwardDescends_pointClosureι {X : Scheme.{u}} (w : X) (p : ℕ) :
    PushforwardDescends (X.pointClosureι w) p :=
  pushforwardDescends_of_isClosedImmersion _ p

/-- The value of `chowPushforward` on its positive branch (API lemma: users need not unfold the definition
of `chowPushforward`). -/
theorem chowPushforward_mk {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (p : ℕ)
    (hdesc : PushforwardDescends f p) (c : ↥(cycleSubgroup X p)) :
    AlgebraicGeometry.chowPushforward f p (ChowGroup.mk c) = ChowGroup.mk (cyclePushforwardHom f p hdesc c) := by
  have hcp : AlgebraicGeometry.chowPushforward f p = QuotientAddGroup.map _ _ (cyclePushforwardHom f p hdesc)
      (cyclePushforwardHom_rel f p hdesc) := by
    unfold AlgebraicGeometry.chowPushforward
    exact dif_pos hdesc
  rw [hcp]
  rfl

/-- (U) Stacks 02SU along the closed immersion of a point closure, in the Chow group. -/
theorem chowPushforward_firstChernCapCycle_pullback_pointClosureι {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : X.IsLocallyOfFiniteTypeOverField) (w : X)
    [IsLocallyNoetherian (X.pointClosure w)]
    (hW : (X.pointClosure w).IsLocallyOfFiniteTypeOverField) (L : X.Modules) [L.IsLineBundle]
    (d : ℕ) (α : AlgebraicCycle (X.pointClosure w) ℤ) :
    AlgebraicGeometry.chowPushforward (X.pointClosureι w) d
        (firstChernCapCycle hW ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) (d + 1) α)
      = firstChernCapCycle hX L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) α) := by
  classical
  have hdesc := pushforwardDescends_pointClosureι w d
  refine (chowPushforward_mk (X.pointClosureι w) d hdesc
    ⟨firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) (d + 1) α,
      firstChernCapCycleAux_mem hW _ (d + 1) α⟩).trans ?_
  show _ = ChowGroup.mk ⟨firstChernCapCycleAux L (d + 1)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) α),
        firstChernCapCycleAux_mem hX L (d + 1) _⟩
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  exact ratEquivZeroOn_le_ratEquivZero _
    (firstChernCapCycleAux_pointClosure_sub_mem L (d + 1) w α)

end AlgebraicGeometry
end
