import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02ti
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # Commutativity of caps at the level of cycles (Stacks 02TJ)

The cycle-level form of Stacks 02TJ: `X` locally of finite type over a field `k` and locally Noetherian,
`L`, `N` line bundles, `α` any cycle. Then
`c_1(L) ∩ (c_1(N) ∩ α) − c_1(N) ∩ (c_1(L) ∩ α)` (both caps are the cycle-level `firstChernCapCycleAux`,
the outer one in dimension `n+1`, the inner one in dimension `n+2`) lies in `ratEquivZero X n`.
(CC1) Single point: for `ht w = n+2`,
`Aux L (capPoint N w) − Aux N (capPoint L w) ∈ ratEquivZeroOn X n (closure{w})`.
(CC2) The locally finite sum over `α`.

Proof:
1. (CC1): `W = X.pointClosure w` (integral, `dim = n+2`), `capPoint M w = ι_* div_{ι^*M}(s_M)`. Use
   `Aux L (ι_*D) − ι_* Aux (ι^*L) D ∈ ratEquivZeroOn (closure{w})` (`FirstChernCapPointClosurePushforward.lean`,
   i.e. the closed-immersion case of 02SU) twice; on `W`,
   `Aux (ι^*L) div(s_N) − Aux (ι^*N) div(s_L) ∈ ratEquivZero W n` is the key formula (Stacks 0AYC, the
   content of 02TH); push forward along `ι` (`ClosedImmersionPushforwardRatEquiv.lean`). Add the three
   terms.
2. (CC2): the inner `Aux N (n+2) α = Σ_w α(w)·capPoint N w` is a locally finite sum over `supp α`, and the
   outer `Aux L` commutes with it (`firstChernCapCycleAux_of_locallyFiniteSum`); subtracting the two orders
   termwise gives `Σ_w α(w)·(term of CC1)`, with witnessing family in the locally finite family
   `{closure{w}}`, assembled by the second paragraph of Stacks 02RZ (`ratEquivZero_of_locallyFinite_sum`).
   This is the same pattern as the proof of Stacks 02TI (Stacks uses the proper pushforward along
   `⊔W_j → X`; here it is expressed by locally finite sums).

Source: Stacks 02TJ (proof: write `α = Σ n_j[W_j]`, push to `W_j` by 02SU, then 02TH), 02RZ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open MiyaokaMori.ClosedImmersionPushforward MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.FirstChernCapPointClosurePushforward

theorem properPushforward_sub {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (a b : AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f (a - b) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward f a - AlgebraicGeometry.AlgebraicCycle.properPushforward f b :=
  map_sub (AlgebraicCycle.properPushforwardHom f) a b

/-- `firstChernCapCycleAux L d` as an additive homomorphism. -/
def firstChernCapCycleAuxHom {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [L.IsLineBundle] (d : ℕ) : AlgebraicCycle X ℤ →+ AlgebraicCycle X ℤ :=
  AddMonoidHom.mk' (firstChernCapCycleAux L d) (firstChernCapCycleAux_add L d)

theorem firstChernCapCycleAux_zsmul {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [L.IsLineBundle] (d : ℕ) (n : ℤ) (c : AlgebraicCycle X ℤ) :
    firstChernCapCycleAux L d (n • c) = n • firstChernCapCycleAux L d c :=
  map_zsmul (firstChernCapCycleAuxHom L d) n c

/-- Every support point of `Aux L d c` is a specialization of some support point of `c`. -/
theorem exists_specializes_of_firstChernCapCycleAux_ne_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ) (c : AlgebraicCycle X ℤ)
    {z : X} (hz : firstChernCapCycleAux L d c z ≠ 0) : ∃ t, c t ≠ 0 ∧ t ⤳ z := by
  have : ∃ t, firstChernCapTerm L d c z t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz (by show (∑ᶠ t : X, _) = 0; simp [hall])
  obtain ⟨t, ht⟩ := this
  obtain ⟨-, hc, hcap⟩ := firstChernCapTerm_ne_zero L ht
  exact ⟨t, hc, firstChernCapPoint_specializes L hcap⟩

/-- (CC1) The single-point form. -/
theorem firstChernCapCycleAux_capPoint_comm_mem {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsLocallyNoetherian X] (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ) (w : X)
    (hw : Order.height w = ((n + 2 : ℕ) : ℕ∞)) :
    firstChernCapCycleAux L (n + 1) (firstChernCapPoint N w)
      - firstChernCapCycleAux N (n + 1) (firstChernCapPoint L w)
      ∈ ratEquivZeroOn X n (closure {w}) := by
  have hLN : IsLocallyNoetherian (X.pointClosure w) := Scheme.isLocallyNoetherian_pointClosure w
  let _ : (X.pointClosure w).Over (Spec (CommRingCat.of k)) :=
    ⟨X.pointClosureι w ≫ (X ↘ Spec (CommRingCat.of k))⟩
  have hLFT : LocallyOfFiniteType ((X.pointClosure w) ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.pointClosureι w ≫ (X ↘ Spec (CommRingCat.of k))))
  obtain ⟨sL, hsL, hcapL⟩ := exists_firstChernCapPoint_eq L w
  obtain ⟨sN, hsN, hcapN⟩ := exists_firstChernCapPoint_eq N w
  -- key formula on W
  have hkey := keyFormula_ratEquivZero k ((X.pointClosure w) ↘ Spec (CommRingCat.of k))
    ((Scheme.Modules.pullback (X.pointClosureι w)).obj N)
    ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) n
    (Scheme.dimension_pointClosure w hw) sN sL hsN hsL
  have hkey' : firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) (n + 1)
        (((Scheme.Modules.pullback (X.pointClosureι w)).obj N).rationalSectionDivisor sN)
      - firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj N) (n + 1)
        (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor sL)
      ∈ ratEquivZero (X.pointClosure w) n := by
    have h0 := sub_eq_zero.mpr hkey
    have h1 : ChowGroup.mk
        (⟨firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) (n + 1)
            (((Scheme.Modules.pullback (X.pointClosureι w)).obj N).rationalSectionDivisor sN),
            firstChernCapCycleAux_mem ⟨k, inferInstance, _, hLFT⟩ _ (n + 1) _⟩
          - ⟨firstChernCapCycleAux ((Scheme.Modules.pullback (X.pointClosureι w)).obj N) (n + 1)
            (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor sL),
            firstChernCapCycleAux_mem ⟨k, inferInstance, _, hLFT⟩ _ (n + 1) _⟩) = 0 := by
      rw [map_sub]; exact h0
    have h2 := (QuotientAddGroup.eq_zero_iff _).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  have h4 := properPushforward_pointClosure_mem_ratEquivZeroOn w n _ hkey'
  have h1 := firstChernCapCycleAux_pointClosure_sub_mem L (n + 1) w
    (((Scheme.Modules.pullback (X.pointClosureι w)).obj N).rationalSectionDivisor sN)
  have h2 := firstChernCapCycleAux_pointClosure_sub_mem N (n + 1) w
    (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor sL)
  have hsum := (ratEquivZeroOn X n (closure {w})).add_mem
    ((ratEquivZeroOn X n (closure {w})).sub_mem h1 h2) h4
  rw [properPushforward_sub] at hsum
  rw [hcapL, hcapN]
  convert hsum using 1
  abel

/-- (CC2) **The cycle-level form of Stacks 02TJ**: two operators `c_1 ∩ −` commute at the level of cycles up
to a rationally trivial difference. -/
theorem firstChernCapCycleAux_comm_mem {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [IsLocallyNoetherian X] (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ)
    (α : AlgebraicCycle X ℤ) :
    firstChernCapCycleAux L (n + 1) (firstChernCapCycleAux N (n + 2) α)
      - firstChernCapCycleAux N (n + 1) (firstChernCapCycleAux L (n + 2) α)
      ∈ ratEquivZero X n := by
  classical
  let S : Set X := {w : X | Order.height w = ((n + 2 : ℕ) : ℕ∞) ∧ α w ≠ 0}
  have hlf : LocallyFinitePoints (fun j : S => (j : X)) :=
    locallyFinitePoints_of_subset_support α (fun w hw => hw.2)
  have hinner : ∀ (M : X.Modules) [M.IsLineBundle] (t : X),
      firstChernCapCycleAux M (n + 2) α t =
        ∑ᶠ j : S, (α (j : X) • firstChernCapPoint M (j : X)) t := by
    intro M _ t
    have hsupp : Function.support (firstChernCapTerm M (n + 2) α t) ⊆ S := by
      intro w hw
      obtain ⟨h1, h2, -⟩ := firstChernCapTerm_ne_zero M hw
      exact ⟨h1, h2⟩
    have hinter : Set.univ ∩ Function.support (firstChernCapTerm M (n + 2) α t)
        = S ∩ Function.support (firstChernCapTerm M (n + 2) α t) := by
      rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]
    show (∑ᶠ w : X, firstChernCapTerm M (n + 2) α t w) = _
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ Set.univ S hinter,
      ← finsum_set_coe_eq_finsum_mem]
    refine finsum_congr fun j => ?_
    unfold firstChernCapTerm
    rw [if_pos j.2.1, AlgebraicCycle.zsmul_apply]
  have hsupc : ∀ (M : X.Modules) [M.IsLineBundle] (j : S) (t : X),
      (α (j : X) • firstChernCapPoint M (j : X)) t ≠ 0 → (j : X) ⤳ t := by
    intro M _ j t ht
    rw [AlgebraicCycle.zsmul_apply] at ht
    exact firstChernCapPoint_specializes M (right_ne_zero_of_mul ht)
  have houter : ∀ (M M' : X.Modules) [M.IsLineBundle] [M'.IsLineBundle] (z : X),
      firstChernCapCycleAux M (n + 1) (firstChernCapCycleAux M' (n + 2) α) z =
        ∑ᶠ j : S, (α (j : X) •
          firstChernCapCycleAux M (n + 1) (firstChernCapPoint M' (j : X))) z := by
    intro M M' _ _ z
    rw [firstChernCapCycleAux_of_locallyFiniteSum M (n + 1) hlf (hsupc M') _ (hinner M') z]
    refine finsum_congr fun j => ?_
    rw [firstChernCapCycleAux_zsmul]
  have hfin : ∀ (M M' : X.Modules) [M.IsLineBundle] [M'.IsLineBundle] (z : X),
      (Function.support fun j : S => (α (j : X) •
        firstChernCapCycleAux M (n + 1) (firstChernCapPoint M' (j : X))) z).Finite := by
    intro M M' _ _ z
    refine finite_support_of_locallyFinitePoints hlf
      (fun j : S => α (j : X) • firstChernCapCycleAux M (n + 1) (firstChernCapPoint M' (j : X)))
      (fun j t ht => ?_) z
    rw [AlgebraicCycle.zsmul_apply] at ht
    obtain ⟨t', ht', hsp⟩ := exists_specializes_of_firstChernCapCycleAux_ne_zero M (n + 1) _
      (right_ne_zero_of_mul ht)
    exact (firstChernCapPoint_specializes M' ht').trans hsp
  refine ratEquivZero_of_locallyFinite_sum (fun j : S => closure {(j : X)})
    ((locallyFinitePoints_iff_locallyFinite_closure _).mp hlf) _
    (fun j : S => α (j : X) •
      (firstChernCapCycleAux L (n + 1) (firstChernCapPoint N (j : X))
        - firstChernCapCycleAux N (n + 1) (firstChernCapPoint L (j : X))))
    (fun j => (ratEquivZeroOn X n (closure {(j : X)})).zsmul_mem
      (firstChernCapCycleAux_capPoint_comm_mem (k := k) L N n (j : X) j.2.1) _) (fun z => ?_)
  show firstChernCapCycleAux L (n + 1) _ z - firstChernCapCycleAux N (n + 1) _ z = _
  rw [houter L N z, houter N L z, ← finsum_sub_distrib (hfin L N z) (hfin N L z)]
  refine finsum_congr fun j => ?_
  simp only [AlgebraicCycle.zsmul_apply]
  rw [← mul_sub]
  rfl

end AlgebraicGeometry
end
