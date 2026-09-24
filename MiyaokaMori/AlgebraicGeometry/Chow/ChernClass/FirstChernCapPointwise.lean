import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointClosurePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf

/-! # Pointwise criteria for identities of caps with first Chern classes

General tools reducing an identity about `c_1(L) ∩ −` in the Chow group to pointwise identities of
principal cycles:
(G) `mem_ratEquivZero_of_pointwise`: let `D : X → Z(X)` be such that for every point `w` of height `e+1`,
    `D w` is an `IsRatEquivGen X e w` (i.e. `(ι_w)_* div(g_w)`). If a cycle `γ` satisfies pointwise
    `γ z = Σ_w [ht w = e+1] β w · D w z`, then `γ ∈ ratEquivZero X e`.
(H2) `firstChernCapCycle_eq_of_pointwise`: if for every `w` of height `e+1`,
    `firstChernCapPoint L w − firstChernCapPoint L' w` is an `IsRatEquivGen X e w`, then
    `firstChernCapCycle hX L (e+1) = firstChernCapCycle hX L' (e+1)`.
(H3) `firstChernCapCycle_eq_add_of_pointwise`: the three-term version (`T` against `L`, `M`), with
    conclusion `cap_T = cap_L + cap_M`.
(I) `isRatEquivGen_firstChernCapPoint_sub_of_iso`: for `L ≅ L'` the pointwise hypothesis of (H2) holds.

Proof:
1. (G): take the witnessing family `S = {w | ht w = e+1 ∧ β w ≠ 0}`, `c_w = β w • D w`
   (`IsRatEquivGen.zsmul`); `S ⊆ supp β` is locally finite (`locallyFinitePoints_of_subset_support`);
   restrict the finite sum to `S` (`finsum_mem_inter_support_eq`).
2. (H2), (H3): `firstChernCapCycleAux` is a pointwise finite sum (`firstChernCapTerm_support_finite`);
   subtract termwise (`finsum_sub_distrib`) and apply (G); two classes in the Chow group are equal iff the
   difference of representatives is rationally trivial (`QuotientAddGroup.eq_zero_iff`).
3. (I): `ι_w^*` preserves isomorphisms; `rationalSectionDivisor_iso` + Stacks 02SH
   (`exists_rationalSectionDivisor_eq_add_principalCycle`).

Source: Stacks 02SH, 02SP, 02RW.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open MiyaokaMori.FirstChernCapPointClosurePushforward MiyaokaMori.FirstChernCapPointGeneric

/-- (G) A locally finite sum of pointwise generators is rationally trivial. -/
theorem mem_ratEquivZero_of_pointwise {X : Scheme.{u}} (e : ℕ) (β : AlgebraicCycle X ℤ)
    (D : X → AlgebraicCycle X ℤ)
    (hD : ∀ w : X, Order.height w = ((e + 1 : ℕ) : ℕ∞) → IsRatEquivGen X e w (D w))
    (γ : AlgebraicCycle X ℤ)
    (hγ : ∀ z, γ z = ∑ᶠ w : X, (open Classical in
      if Order.height w = ((e + 1 : ℕ) : ℕ∞) then β w * D w z else 0)) :
    γ ∈ ratEquivZero X e := by
  classical
  set S : Set X := {w : X | Order.height w = ((e + 1 : ℕ) : ℕ∞) ∧ β w ≠ 0} with hSdef
  refine ⟨↥S, fun j => (j : X), fun j => β (j : X) • D (j : X),
    fun _ => Set.mem_univ _, fun j => (hD (j : X) j.2.1).zsmul _,
    locallyFinitePoints_of_subset_support β (fun w hw => hw.2), fun z => ?_⟩
  let T : X → ℤ := fun w => if Order.height w = ((e + 1 : ℕ) : ℕ∞) then β w * D w z else 0
  have hsupp : Function.support T ⊆ S := by
    intro w hw
    have hw' : T w ≠ 0 := hw
    simp only [T] at hw'
    split_ifs at hw' with hh
    · exact ⟨hh, left_ne_zero_of_mul hw'⟩
    · exact absurd rfl hw'
  have hinter : Set.univ ∩ Function.support T = S ∩ Function.support T := by
    rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]
  rw [hγ z]
  show (∑ᶠ w : X, T w) = _
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ S hinter,
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun j => ?_
  show T j = (β (j : X) • D (j : X)) z
  simp only [T]
  rw [if_pos j.2.1, AlgebraicCycle.zsmul_apply]

/-- (H2) If the pointwise differences are generators, the cycle-level caps agree in the Chow group. -/
theorem firstChernCapCycle_eq_of_pointwise {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : X.IsLocallyOfFiniteTypeOverField) (L L' : X.Modules) [L.IsLineBundle]
    [L'.IsLineBundle] (e : ℕ)
    (h : ∀ w : X, Order.height w = ((e + 1 : ℕ) : ℕ∞) →
      IsRatEquivGen X e w (firstChernCapPoint L w - firstChernCapPoint L' w))
    (β : AlgebraicCycle X ℤ) :
    firstChernCapCycle hX L (e + 1) β = firstChernCapCycle hX L' (e + 1) β := by
  classical
  rw [← sub_eq_zero]
  show ChowGroup.mk ⟨firstChernCapCycleAux L (e + 1) β, firstChernCapCycleAux_mem hX L _ β⟩ -
    ChowGroup.mk ⟨firstChernCapCycleAux L' (e + 1) β, firstChernCapCycleAux_mem hX L' _ β⟩ = 0
  rw [← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  refine mem_ratEquivZero_of_pointwise e β _ h _ fun z => ?_
  show firstChernCapCycleAux L (e + 1) β z - firstChernCapCycleAux L' (e + 1) β z = _
  show (∑ᶠ w : X, firstChernCapTerm L (e + 1) β z w) -
    (∑ᶠ w : X, firstChernCapTerm L' (e + 1) β z w) = _
  rw [← finsum_sub_distrib (firstChernCapTerm_support_finite L _ β z)
    (firstChernCapTerm_support_finite L' _ β z)]
  refine finsum_congr fun w => ?_
  unfold firstChernCapTerm
  split_ifs
  · rw [← mul_sub]; rfl
  · simp

/-- (H3) Three-term version: if `cap_T − cap_L − cap_M` is pointwise a generator, then
`cap_T = cap_L + cap_M` in the Chow group. -/
theorem firstChernCapCycle_eq_add_of_pointwise {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : X.IsLocallyOfFiniteTypeOverField) (T L M : X.Modules) [T.IsLineBundle]
    [L.IsLineBundle] [M.IsLineBundle] (e : ℕ)
    (h : ∀ w : X, Order.height w = ((e + 1 : ℕ) : ℕ∞) →
      IsRatEquivGen X e w
        (firstChernCapPoint T w - firstChernCapPoint L w - firstChernCapPoint M w))
    (β : AlgebraicCycle X ℤ) :
    firstChernCapCycle hX T (e + 1) β =
      firstChernCapCycle hX L (e + 1) β + firstChernCapCycle hX M (e + 1) β := by
  classical
  rw [← sub_eq_zero, ← sub_sub]
  show ChowGroup.mk ⟨firstChernCapCycleAux T (e + 1) β, firstChernCapCycleAux_mem hX T _ β⟩ -
    ChowGroup.mk ⟨firstChernCapCycleAux L (e + 1) β, firstChernCapCycleAux_mem hX L _ β⟩ -
    ChowGroup.mk ⟨firstChernCapCycleAux M (e + 1) β, firstChernCapCycleAux_mem hX M _ β⟩ = 0
  rw [← map_sub, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  refine mem_ratEquivZero_of_pointwise e β _ h _ fun z => ?_
  show (∑ᶠ w : X, firstChernCapTerm T (e + 1) β z w) -
    (∑ᶠ w : X, firstChernCapTerm L (e + 1) β z w) -
    (∑ᶠ w : X, firstChernCapTerm M (e + 1) β z w) = _
  have hTL : (Function.support fun w => firstChernCapTerm T (e + 1) β z w -
      firstChernCapTerm L (e + 1) β z w).Finite :=
    ((firstChernCapTerm_support_finite T _ β z).union
      (firstChernCapTerm_support_finite L _ β z)).subset (Function.support_sub _ _)
  rw [← finsum_sub_distrib (firstChernCapTerm_support_finite T _ β z)
    (firstChernCapTerm_support_finite L _ β z),
    ← finsum_sub_distrib hTL (firstChernCapTerm_support_finite M _ β z)]
  refine finsum_congr fun w => ?_
  unfold firstChernCapTerm
  split_ifs
  · rw [← mul_sub, ← mul_sub]; rfl
  · simp

/-- (I) Isomorphic line bundles: the pointwise difference is a generator. -/
theorem isRatEquivGen_firstChernCapPoint_sub_of_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (φ : L ≅ L') (e : ℕ) (w : X)
    (hw : Order.height w = ((e + 1 : ℕ) : ℕ∞)) :
    IsRatEquivGen X e w (firstChernCapPoint L w - firstChernCapPoint L' w) := by
  have hLN : IsLocallyNoetherian (X.pointClosure w) := Scheme.isLocallyNoetherian_pointClosure w
  obtain ⟨s₁, hs₁, h1⟩ := exists_firstChernCapPoint_eq L w
  obtain ⟨s₂, hs₂, h2⟩ := exists_firstChernCapPoint_eq L' w
  let ψ := (Scheme.Modules.pullback (X.pointClosureι w)).mapIso φ
  obtain ⟨g, hg⟩ := exists_rationalSectionDivisor_eq_add_principalCycle _ _ s₂
    (moduleStalkMap_iso_ne_zero ψ _ s₁ hs₁) hs₂
  refine ⟨hw, inferInstance, inferInstance, hLN, g, ?_⟩
  rw [h1, h2, rationalSectionDivisor_iso ψ s₁ hs₁, hg]
  exact sub_eq_of_eq_add' (properPushforward_add _ _ _)

end AlgebraicGeometry
end
