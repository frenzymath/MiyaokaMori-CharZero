import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycleUnit

/-! # The projection formula along a point closure at the level of cycles

Let `X` be locally Noetherian, `L` a line bundle, `W = X.pointClosure w`, `ι = ι_w`, and `γ` a cycle on `W`.
Then `c_1(L) ∩ ι_*γ − ι_*(c_1(ι^*L) ∩ γ)` (at the level of cycles, `firstChernCapCycleAux`) lies in
`ratEquivZeroOn X (d−1) (closure{w})` (the closed-immersion case of Stacks 02SU at the level of cycles, with
the support information needed in the second paragraph of 02RZ).

Proof:
1. (02SH, change of section) On an integral locally Noetherian `W`, the divisors of two nonzero rational
   sections of a line bundle `M` differ by a principal cycle; an isomorphism of module sheaves does not
   change the divisor.
2. (Pointwise) For `v ∈ W`, `x := ι v`:
   `firstChernCapPoint L x − ι_* firstChernCapPoint (ι^*L) v = (ι_x)_* div(g)` with `g ∈ K(X_x)^×`:
   `ι_*(ι_v)_* = (ι_x)_* θ_*` (Stacks 02R5 + `PointClosureTransport`); `ι_v^*ι^*L ≅ θ^*ι_x^*L` (Mathlib's
   `pullbackComp`, `pullbackCongr`); `θ_* div_{θ^*N}(s) = div_N(s′)`; then step 1.
3. (Summation) For `d = 0` both sides vanish. For `d = e+1`, steps 4 and 5 write both terms as pointwise
   finite sums over `v ∈ W`; subtracting termwise gives `Σ_{ht v = d} γ(v)·(ι_{ιv})_* div(g_v)`; the family
   `{ι v : γ v ≠ 0}` is locally finite (`ClosedImmersionPushforwardRatEquiv.lean`) and lies in
   `closure{w}`, and each term is an `IsRatEquivGen X e (ι v)` (`IsRatEquivGen.zsmul`).
4. (A) `firstChernCapCycleAux L d (ι_*γ) z = Σ_v [ht v = d] γ v · firstChernCapPoint L (ι v) z`: the sum
   on `X` is nonzero only on `range ι`; reindex along the injective `ι`.
5. (B) `(ι_* firstChernCapCycleAux M d γ) z = Σ_v [ht v = d] γ v · (ι_* firstChernCapPoint M v) z`: cases
   `z = ι z′` and `z ∉ range ι`.

Source: Stacks 02SU (the case where `p` is a closed immersion), 02SH, 02RZ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace MiyaokaMori.FirstChernCapPointClosurePushforward
open AlgebraicGeometry.Divisors AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Divisors.LineGenericCoordinates MiyaokaMori.PointClosureTransport
  MiyaokaMori.FirstChernCapPointGeneric MiyaokaMori.ClosedImmersionPushforward

/-- An isomorphism of module sheaves does not change the divisor of a rational section (cycle form). -/
theorem rationalSectionDivisor_iso {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    {M N : W.Modules} [M.IsLineBundle] [N.IsLineBundle] (e : M ≅ N)
    (s : M.stalk (genericPoint W)) (hs : s ≠ 0) :
    M.rationalSectionDivisor s =
      N.rationalSectionDivisor (moduleStalkMap W (genericPoint W) e.hom s) := by
  ext z
  exact rationalSectionOrd_iso e s hs z

/-- **Stacks 02SH (change of section)**: the divisors of two nonzero rational sections of a line bundle
differ by a principal cycle. -/
theorem exists_rationalSectionDivisor_eq_add_principalCycle {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] (M : W.Modules) [M.IsLineBundle]
    (s₁ s₂ : M.stalk (genericPoint W)) (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    ∃ g : W.functionFieldˣ,
      M.rationalSectionDivisor s₁ = M.rationalSectionDivisor s₂ + W.principalCycle g := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := Scheme.Modules.exists_trivialization M (genericPoint W)
  let c := genericCoordinate W M U ⟨⟨genericPoint W, hz⟩⟩ eU
  have hc₁ : c s₁ ≠ 0 := genericCoordinate_ne_zero W M U ⟨⟨_, hz⟩⟩ eU s₁ h₁
  have hc₂ : c s₂ ≠ 0 := genericCoordinate_ne_zero W M U ⟨⟨_, hz⟩⟩ eU s₂ h₂
  refine ⟨Units.mk0 (c s₁ / c s₂) (div_ne_zero hc₁ hc₂), ?_⟩
  rw [← Scheme.Modules.rationalSectionDivisor_smul M s₂ h₂]
  congr 1
  apply c.injective
  exact ((c.map_smul _ _).trans (by
    rw [Units.val_mk0, smul_eq_mul, div_mul_cancel₀ _ hc₂])).symm

/-- The body of `firstChernCapPoint`: the pushforward of the divisor of some nonzero rational section. -/
theorem exists_firstChernCapPoint_eq {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [L.IsLineBundle] (w : X) [IsLocallyNoetherian (X.pointClosure w)] :
    ∃ s : ((Scheme.Modules.pullback (X.pointClosureι w)).obj L).stalk
        (genericPoint (X.pointClosure w)), s ≠ 0 ∧
      firstChernCapPoint L w = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
        (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor s) :=
  ⟨Classical.epsilon fun t => t ≠ 0,
    Classical.epsilon_spec (Scheme.Modules.exists_stalk_genericPoint_ne_zero
      ((Scheme.Modules.pullback (X.pointClosureι w)).obj L)), rfl⟩

/-- **Pointwise form** (the core of the proof of Stacks 02SU, `p` a closed immersion):
`c_1(L) ∩ [ι v] − ι_*(c_1(ι^*L) ∩ [v])` is the pushforward of a principal cycle on `X.pointClosure (ι v)`. -/
theorem exists_firstChernCapPoint_sub_eq_principalCycle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (w : X) [IsLocallyNoetherian (X.pointClosure w)]
    (v : X.pointClosure w)
    [IsLocallyNoetherian (X.pointClosure ((X.pointClosureι w).base v))] :
    ∃ g : (X.pointClosure ((X.pointClosureι w).base v)).functionFieldˣ,
      firstChernCapPoint L ((X.pointClosureι w).base v)
        - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            (firstChernCapPoint ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) v)
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι ((X.pointClosureι w).base v))
          ((X.pointClosure ((X.pointClosureι w).base v)).principalCycle g) := by
  have hLNv : IsLocallyNoetherian ((X.pointClosure w).pointClosure v) :=
    Scheme.isLocallyNoetherian_pointClosure v
  obtain ⟨θ, hθ⟩ := exists_iso_pointClosure_pointClosure w v
  let N := (Scheme.Modules.pullback (X.pointClosureι ((X.pointClosureι w).base v))).obj L
  let Lw := (Scheme.Modules.pullback (X.pointClosureι w)).obj L
  let Lv := (Scheme.Modules.pullback ((X.pointClosure w).pointClosureι v)).obj Lw
  let φ : Lv ≅ (Scheme.Modules.pullback θ.hom).obj N :=
    (Scheme.Modules.pullbackComp ((X.pointClosure w).pointClosureι v) (X.pointClosureι w)).app L ≪≫
      (Scheme.Modules.pullbackCongr hθ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp θ.hom
        (X.pointClosureι ((X.pointClosureι w).base v))).app L).symm
  obtain ⟨s₁, hs₁, h1⟩ := exists_firstChernCapPoint_eq L ((X.pointClosureι w).base v)
  obtain ⟨s₂, hs₂, h2⟩ := exists_firstChernCapPoint_eq Lw v
  have e1 : AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward ((X.pointClosure w).pointClosureι v)
        (Lv.rationalSectionDivisor s₂)) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι ((X.pointClosureι w).base v))
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

/-- Reindexing the summands along a closed immersion: the explicit form of `firstChernCapTerm L d (i_*γ) z (i v)`. -/
theorem firstChernCapTerm_properPushforward {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (γ : AlgebraicCycle W ℤ) (z : X) (v : W) :
    firstChernCapTerm L d (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ) z (i.base v) =
      (open Classical in
        if Order.height v = (d : ℕ∞) then γ v * firstChernCapPoint L (i.base v) z else 0) := by
  unfold firstChernCapTerm
  rw [Scheme.Hom.height_of_isClosedImmersion i v, properPushforward_closedImmersion_apply]

/-- **A**: reindexing along a closed immersion. The pointwise finite sum defining
`firstChernCapCycleAux L d (i_*γ)` on `X` is nonzero only on `range i`. -/
theorem firstChernCapCycleAux_properPushforward_apply {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (γ : AlgebraicCycle W ℤ) (z : X) :
    firstChernCapCycleAux L d (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ) z =
      ∑ᶠ v : W, firstChernCapTerm L d (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ) z (i.base v) := by
  have hinj : Function.Injective i.base := i.isClosedEmbedding.injective
  show (∑ᶠ x : X, firstChernCapTerm L d (AlgebraicGeometry.AlgebraicCycle.properPushforward i γ) z x) = _
  rw [← finsum_mem_range hinj, ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext x
  simp only [Set.univ_inter, Set.mem_inter_iff, iff_and_self]
  intro hx
  by_contra hnr
  apply hx
  unfold firstChernCapTerm
  rw [properPushforward_apply_of_notMem_range i γ hnr]
  simp

/-- **B**: the pushforward along a closed immersion commutes with the pointwise finite sum of
`firstChernCapCycleAux`. -/
theorem properPushforward_firstChernCapCycleAux_apply {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian W] (M : W.Modules) [M.IsLineBundle] (d : ℕ)
    (γ : AlgebraicCycle W ℤ) (z : X) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i (firstChernCapCycleAux M d γ) z =
      ∑ᶠ v : W, (open Classical in
        if Order.height v = (d : ℕ∞) then
          γ v * AlgebraicGeometry.AlgebraicCycle.properPushforward i (firstChernCapPoint M v) z else 0) := by
  by_cases hz : z ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hz
    rw [properPushforward_closedImmersion_apply]
    show (∑ᶠ v : W, firstChernCapTerm M d γ z' v) = _
    refine finsum_congr fun v => ?_
    unfold firstChernCapTerm
    rw [properPushforward_closedImmersion_apply]
  · rw [properPushforward_apply_of_notMem_range i _ hz]
    refine (finsum_eq_zero_of_forall_eq_zero fun v => ?_).symm
    rw [properPushforward_apply_of_notMem_range i _ hz]
    simp

/-- Only finitely many summands of B are nonzero. -/
theorem finite_support_properPushforward_firstChernCapPoint {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian W] (M : W.Modules) [M.IsLineBundle] (d : ℕ)
    (γ : AlgebraicCycle W ℤ) (z : X) :
    (Function.support fun v : W => (open Classical in
        if Order.height v = (d : ℕ∞) then
          γ v * AlgebraicGeometry.AlgebraicCycle.properPushforward i (firstChernCapPoint M v) z else 0)).Finite := by
  by_cases hz : z ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hz
    refine (firstChernCapTerm_support_finite M d γ z').subset fun v hv => ?_
    intro h0
    apply hv
    unfold firstChernCapTerm at h0
    simpa [properPushforward_closedImmersion_apply] using h0
  · convert Set.finite_empty
    ext v
    simp [properPushforward_apply_of_notMem_range i _ hz]

/-- **Stacks 02SU at the level of cycles, with restricted support (`p` the closed immersion of a point
closure).** -/
theorem firstChernCapCycleAux_pointClosure_sub_mem {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (w : X) [IsLocallyNoetherian (X.pointClosure w)]
    (γ : AlgebraicCycle (X.pointClosure w) ℤ) :
    firstChernCapCycleAux L d (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ)
      - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
          (firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) d γ)
      ∈ ratEquivZeroOn X (d - 1) (closure {w}) := by
  classical
  cases d with
  | zero =>
    rw [firstChernCapCycleAux_dim_zero, firstChernCapCycleAux_dim_zero,
      show AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) 0 = 0 from
        (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)).map_zero, sub_zero]
    exact zero_mem _
  | succ e =>
    have hLN : ∀ v : X.pointClosure w,
        IsLocallyNoetherian (X.pointClosure ((X.pointClosureι w).base v)) :=
      fun v => Scheme.isLocallyNoetherian_pointClosure _
    choose g hg using fun v =>
      @exists_firstChernCapPoint_sub_eq_principalCycle X _ L _ w _ v (hLN v)
    let S : Set (X.pointClosure w) := {v | Order.height v = ((e + 1 : ℕ) : ℕ∞) ∧ γ v ≠ 0}
    let c : S → AlgebraicCycle X ℤ := fun j => γ j.1 •
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι ((X.pointClosureι w).base j.1))
        ((X.pointClosure ((X.pointClosureι w).base j.1)).principalCycle (g j.1))
    refine ⟨S, fun j => (X.pointClosureι w).base j.1, c,
      fun j => pointClosureι_mem_closure w j.1, fun j => ?_,
      locallyFinitePoints_comp_of_isClosedImmersion _
        (locallyFinitePoints_of_subset_support γ (S := S) fun v hv => hv.2), fun z => ?_⟩
    · exact IsRatEquivGen.zsmul
        ⟨(Scheme.Hom.height_of_isClosedImmersion _ j.1).trans j.2.1, inferInstance,
          inferInstance, hLN j.1, g j.1, rfl⟩ (γ j.1)
    · let T : X.pointClosure w → ℤ := fun v =>
        if Order.height v = ((e + 1 : ℕ) : ℕ∞) then γ v *
          AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι ((X.pointClosureι w).base v))
            ((X.pointClosure ((X.pointClosureι w).base v)).principalCycle (g v)) z else 0
      have hfinA : (Function.support fun v : X.pointClosure w =>
          firstChernCapTerm L (e + 1) (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ) z
            ((X.pointClosureι w).base v)).Finite :=
        (firstChernCapTerm_support_finite L (e + 1) _ z).preimage
          ((X.pointClosureι w).isClosedEmbedding.injective.injOn)
      have hLHS : (firstChernCapCycleAux L (e + 1)
            (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ)
          - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
              (firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj L)
                (e + 1) γ)) z = ∑ᶠ v, T v := by
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

end MiyaokaMori.FirstChernCapPointClosurePushforward
end
