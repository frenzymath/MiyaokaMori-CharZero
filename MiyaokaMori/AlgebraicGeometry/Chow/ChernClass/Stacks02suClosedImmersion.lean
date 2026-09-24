import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassMk

/-! # The projection formula along a closed immersion (Stacks 02SU)

Let `i : W → X` be **any** closed immersion (`X`, `W` locally Noetherian). Then
(P) pointwise: `c_1(L) ∩ [i v] − i_*(c_1(i^*L) ∩ [v])` is the pushforward of a principal cycle on
`X.pointClosure (i v)`;
(S) at the level of cycles: `c_1(L) ∩ i_*γ − i_*(c_1(i^*L) ∩ γ) ∈ ratEquivZero X (d−1)`;
(U) in the Chow group: `i_*(c_1(i^*L) ∩ α) = c_1(L) ∩ i_*α` (in the `firstChernCapCycle` form and in the
`firstChernClass` form).
This generalizes the case `i = ι_w` of a point closure (`Stacks02suPointClosure.lean`) to arbitrary closed
immersions with the same proof: `θ` is the general `exists_iso_pointClosure_of_isClosedImmersion`
(`W.pointClosure v → W → X` is a closed immersion of integral schemes), and the rest (change of section
02SH, transport of divisors along `θ`, reindexing of the pointwise finite sums) was already stated for
general closed immersions. In the induction of repeated Cartier restriction `p` is always a composite of
closed immersions, so this lemma (with `pushforwardDescends_of_isClosedImmersion`) replaces the general
02SU and 02S2.

Source: Stacks 02SU (the case where `p` is a closed immersion), 02SH, 02RZ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

namespace MiyaokaMori.Stacks02suClosedImmersion
open AlgebraicGeometry.Divisors AlgebraicGeometry.Divisors.LineGenericCoordinates MiyaokaMori.PointClosureTransport
  MiyaokaMori.FirstChernCapPointGeneric MiyaokaMori.ClosedImmersionPushforward
  MiyaokaMori.FirstChernCapPointClosurePushforward

/-- (P) The pointwise form (general closed immersion). -/
theorem exists_firstChernCapPoint_sub_eq_principalCycle {W X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian W] (i : W ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [L.IsLineBundle] (v : W) :
    ∃ g : (X.pointClosure (i.base v)).functionFieldˣ,
      firstChernCapPoint L (i.base v)
        - AlgebraicGeometry.AlgebraicCycle.properPushforward i
            (firstChernCapPoint ((Scheme.Modules.pullback i).obj L) v)
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (i.base v))
          ((X.pointClosure (i.base v)).principalCycle g) := by
  obtain ⟨θ, hθ⟩ := exists_iso_pointClosure_of_isClosedImmersion
    (W.pointClosureι v ≫ i) (i.base v) (by
      show i.base ((W.pointClosureι v).base _) = _
      rw [Scheme.pointClosureι_genericPoint])
  let N := (Scheme.Modules.pullback (X.pointClosureι (i.base v))).obj L
  let Lw := (Scheme.Modules.pullback i).obj L
  let Lv := (Scheme.Modules.pullback (W.pointClosureι v)).obj Lw
  let φ : Lv ≅ (Scheme.Modules.pullback θ.hom).obj N :=
    (Scheme.Modules.pullbackComp (W.pointClosureι v) i).app L ≪≫
      (Scheme.Modules.pullbackCongr hθ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp θ.hom (X.pointClosureι (i.base v))).app L).symm
  obtain ⟨s₁, hs₁, h1⟩ := exists_firstChernCapPoint_eq L (i.base v)
  obtain ⟨s₂, hs₂, h2⟩ := exists_firstChernCapPoint_eq Lw v
  have e1 : AlgebraicGeometry.AlgebraicCycle.properPushforward i
      (AlgebraicGeometry.AlgebraicCycle.properPushforward (W.pointClosureι v)
        (Lv.rationalSectionDivisor s₂)) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (i.base v))
        (AlgebraicGeometry.AlgebraicCycle.properPushforward θ.hom (Lv.rationalSectionDivisor s₂)) :=
    (AlgebraicCycle.properPushforward_comp _ _ _).trans
      ((properPushforward_congr hθ.symm _).trans
        (AlgebraicCycle.properPushforward_comp _ _ _).symm)
  obtain ⟨s₃, hs₃, h3⟩ := exists_rationalSectionDivisor_eq_properPushforward_iso θ.hom N _
    (moduleStalkMap_iso_ne_zero φ _ s₂ hs₂)
  obtain ⟨g, hg⟩ := exists_rationalSectionDivisor_eq_add_principalCycle N s₁ s₃ hs₁ hs₃
  refine ⟨g, ?_⟩
  rw [h1, h2, e1, rationalSectionDivisor_iso φ s₂ hs₂, h3, hg]
  exact sub_eq_of_eq_add' (AlgebraicGeometry.properPushforward_add _ _ _)

/-- (S) The cycle-level form (general closed immersion). -/
theorem firstChernCapCycleAux_properPushforward_sub_mem {W X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian W] (i : W ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (γ : AlgebraicCycle W ℤ) :
    firstChernCapCycleAux L d (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ)
      - AlgebraicGeometry.AlgebraicCycle.properPushforward i
          (firstChernCapCycleAux ((Scheme.Modules.pullback i).obj L) d γ)
      ∈ ratEquivZero X (d - 1) := by
  classical
  cases d with
  | zero =>
    rw [firstChernCapCycleAux_dim_zero, firstChernCapCycleAux_dim_zero,
      show AlgebraicGeometry.AlgebraicCycle.properPushforward i 0 = 0 from
        (AlgebraicCycle.properPushforwardHom i).map_zero, sub_zero]
    exact zero_mem _
  | succ e =>
    choose g hg using fun v => exists_firstChernCapPoint_sub_eq_principalCycle i L v
    let S : Set W := {v | Order.height v = ((e + 1 : ℕ) : ℕ∞) ∧ γ v ≠ 0}
    let c : S → AlgebraicCycle X ℤ := fun j => γ j.1 •
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (i.base j.1))
        ((X.pointClosure (i.base j.1)).principalCycle (g j.1))
    refine ⟨S, fun j => i.base j.1, c, fun _ => Set.mem_univ _, fun j => ?_,
      locallyFinitePoints_comp_of_isClosedImmersion _
        (locallyFinitePoints_of_subset_support γ (S := S) fun v hv => hv.2), fun z => ?_⟩
    · exact IsRatEquivGen.zsmul
        ⟨(Scheme.Hom.height_of_isClosedImmersion _ j.1).trans j.2.1, inferInstance,
          inferInstance, inferInstance, g j.1, rfl⟩ (γ j.1)
    · let T : W → ℤ := fun v =>
        if Order.height v = ((e + 1 : ℕ) : ℕ∞) then γ v *
          AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (i.base v))
            ((X.pointClosure (i.base v)).principalCycle (g v)) z else 0
      have hfinA : (Function.support fun v : W =>
          firstChernCapTerm L (e + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ) z
            (i.base v)).Finite :=
        (firstChernCapTerm_support_finite L (e + 1) _ z).preimage
          (i.isClosedEmbedding.injective.injOn)
      have hLHS : (firstChernCapCycleAux L (e + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ)
          - AlgebraicGeometry.AlgebraicCycle.properPushforward i
              (firstChernCapCycleAux ((Scheme.Modules.pullback i).obj L) (e + 1) γ)) z
            = ∑ᶠ v, T v := by
        show firstChernCapCycleAux L (e + 1) _ z - AlgebraicGeometry.AlgebraicCycle.properPushforward _ _ z = _
        rw [firstChernCapCycleAux_properPushforward_apply,
          properPushforward_firstChernCapCycleAux_apply,
          ← finsum_sub_distrib hfinA (finite_support_properPushforward_firstChernCapPoint _ _ _ _ _)]
        refine finsum_congr fun v => ?_
        rw [firstChernCapTerm_properPushforward]
        show _ = T v
        simp only [T]
        split_ifs
        · rw [← mul_sub, ← hg v]; rfl
        · simp
      have hT : ∀ v, T v ≠ 0 → v ∈ S := by
        intro v h
        simp only [T] at h
        split_ifs at h with hh
        · exact ⟨hh, left_ne_zero_of_mul h⟩
        · exact absurd rfl h
      have h1 : ∑ᶠ v, T v = ∑ᶠ v ∈ S, T v := by
        rw [← finsum_mem_univ]
        refine finsum_mem_inter_support_eq _ _ _ ?_
        ext v
        simp only [Set.univ_inter, Set.mem_inter_iff, iff_and_self]
        exact hT v
      rw [hLHS, h1, ← finsum_set_coe_eq_finsum_mem S]
      refine finsum_congr fun j => ?_
      show T j.1 = c j z
      simp only [c]
      rw [AlgebraicGeometry.AlgebraicCycle.zsmul_apply]
      simp only [T]
      rw [if_pos j.2.1]

end MiyaokaMori.Stacks02suClosedImmersion

namespace AlgebraicGeometry
open MiyaokaMori.Stacks02suClosedImmersion

/-- (U) Stacks 02SU along an arbitrary closed immersion, in the Chow group (`firstChernCapCycle` form). -/
theorem chowPushforward_firstChernCapCycle_pullback_of_isClosedImmersion {W X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian W] (hX : X.IsLocallyOfFiniteTypeOverField)
    (hW : W.IsLocallyOfFiniteTypeOverField) (i : W ⟶ X) [IsClosedImmersion i]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicCycle W ℤ) :
    chowPushforward i d
        (firstChernCapCycle hW ((Scheme.Modules.pullback i).obj L) (d + 1) α)
      = firstChernCapCycle hX L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward i α) := by
  classical
  have hdesc := pushforwardDescends_of_isClosedImmersion i d
  refine (chowPushforward_mk i d hdesc
    ⟨firstChernCapCycleAux ((Scheme.Modules.pullback i).obj L) (d + 1) α,
      firstChernCapCycleAux_mem hW _ (d + 1) α⟩).trans ?_
  show _ = ChowGroup.mk ⟨firstChernCapCycleAux L (d + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward i α),
        firstChernCapCycleAux_mem hX L (d + 1) _⟩
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  exact firstChernCapCycleAux_properPushforward_sub_mem i L (d + 1) α

end AlgebraicGeometry

/-- (U) Stacks 02SU along an arbitrary closed immersion, in the `firstChernClass` form (the same shape as
`AlgebraicGeometry.chowPushforward_firstChernClass_pullback` for general proper morphisms, with `IsProper`
replaced by `IsClosedImmersion`; it does not use the general 02S2 / 02SU). -/
theorem AlgebraicGeometry.chowPushforward_firstChernClass_pullback_of_isClosedImmersion
    {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion p]
    (L : Y.Modules) [L.IsLineBundle] (d : ℕ) (α : AlgebraicGeometry.ChowGroup X (d + 1)) :
    AlgebraicGeometry.chowPushforward p d
        (AlgebraicGeometry.firstChernClass ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1) α)
      = AlgebraicGeometry.firstChernClass L (d + 1) (AlgebraicGeometry.chowPushforward p (d + 1) α) := by
  let : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective α
  change AlgebraicGeometry.chowPushforward p d
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj L) (d + 1)
        (AlgebraicGeometry.ChowGroup.mk a)) =
    AlgebraicGeometry.firstChernClass L (d + 1)
      (AlgebraicGeometry.chowPushforward p (d + 1) (AlgebraicGeometry.ChowGroup.mk a))
  rw [AlgebraicGeometry.chowPushforward_mk p (d + 1)
      (AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion p (d + 1)) a]
  rw [AlgebraicGeometry.firstChernClass_mk (k := k) _ (Nat.succ_pos d),
    AlgebraicGeometry.firstChernClass_mk (k := k) _ (Nat.succ_pos d)]
  exact AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback_of_isClosedImmersion
    _ _ p L d a.1

end
