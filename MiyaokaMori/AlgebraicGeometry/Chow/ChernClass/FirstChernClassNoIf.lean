import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycleUnit

/-! # The first Chern class without the `if`

Of the three conjuncts in the `if` of the definition of `firstChernClass`, only "`X` locally Noetherian and
locally of finite type over some field" is a genuine condition on the setting; "`0 < d`" and "`∀ α β`,
rationally equivalent ⇒ equal caps" can be dropped. Precisely:
(W) `firstChernCapCycle_ratEquivZero_le_ker`: for `X` locally Noetherian and locally of finite type over a
    field, the kernel of `(firstChernCapCycle hX L d) ∘ subtype` contains `ratEquivZero ⊓ Z_d` (the shape
    needed to write 02TI as a `QuotientAddGroup.lift`).
(E) `firstChernClass_eq_noIf`: the definition equals the body without the theorem half of the `if`,
    `if h : ∃ _ : IsLocallyNoetherian X, X.IsLocallyOfFiniteTypeOverField then lift _ (cap ∘ subtype) (W) else 0`
    (written on the right side of the statement, not as a separate `def`).

Proof:
1. (W): extract `k`, `π` from `hX`, let `X.Over (Spec k) := ⟨π⟩`, and apply Stacks 02TI to `α := x`, `β := 0`.
2. (E): when the structural condition fails both sides are `0`. When it holds: for `d = 0` the original
   definition takes the `else` branch and gives `0`, while the new body is the lift of
   `firstChernCapCycle … 0`, also `0` by `firstChernCapCycle_dim_zero`; for `d > 0` the third conjunct of the
   original condition follows from the argument of (W), and both sides are the same lift.
3. Consequences: (K) `firstChernClass_mk'`: when the structural condition holds,
   `firstChernClass L d (mk c) = firstChernCapCycle hX L d c` (no `0 < d`, no `X.Over` instance required);
   (K0) `firstChernClass_eq_zero_of_not`: when it fails, `firstChernClass L d = 0`. Downstream lemmas use
   `firstChernClass` only through (K), (K0) and never unfold the definition.

Source: Stacks 02TI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry

/-- (W) The well-definedness condition for writing 02TI as a `QuotientAddGroup.lift`. -/
theorem firstChernCapCycle_ratEquivZero_le_ker {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : X.IsLocallyOfFiniteTypeOverField) (L : X.Modules) [L.IsLineBundle] (d : ℕ) :
    (ratEquivZero X d).addSubgroupOf (cycleSubgroup X d) ≤
      ((firstChernCapCycle hX L d).comp (cycleSubgroup X d).subtype).ker := by
  obtain ⟨k, _, π, hπ⟩ := hX
  let _ : X.Over (Spec (CommRingCat.of k)) := ⟨π⟩
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) := hπ
  intro x hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
  have h := firstChernCapCycle_rationallyEquivalent (k := k) L d x 0
    ⟨x.2, zero_mem _, by rw [sub_zero]; exact AddSubgroup.mem_addSubgroupOf.mp hx⟩
  exact h.trans (map_zero _)

private theorem dite_addMonoidHom_apply_pos {c : Prop} {_ : Decidable c} {A B : Type*}
    [AddZeroClass A] [AddZeroClass B] (t : c → (A →+ B)) (e : ¬c → (A →+ B)) (hc : c) (x : A) :
    (dite c t e) x = t hc x := by
  rw [dif_pos hc]

private theorem dite_addMonoidHom_apply_neg {c : Prop} {_ : Decidable c} {A B : Type*}
    [AddZeroClass A] [AddZeroClass B] (t : c → (A →+ B)) (e : ¬c → (A →+ B)) (hc : ¬c) (x : A) :
    (dite c t e) x = e hc x := by
  rw [dif_neg hc]

/-- (E) The definition equals the body without the `if`. The right side is deliberately **not** made into a
separate `def`. -/
theorem firstChernClass_eq_noIf {X : Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (d : ℕ) :
    firstChernClass L d =
      (open Classical in
      if h : ∃ (_ : IsLocallyNoetherian X), X.IsLocallyOfFiniteTypeOverField then
        haveI : IsLocallyNoetherian X := h.1
        QuotientAddGroup.lift _ ((firstChernCapCycle h.2 L d).comp (cycleSubgroup X d).subtype)
          (firstChernCapCycle_ratEquivZero_le_ker h.2 L d)
      else 0) := by
  refine AddMonoidHom.ext fun x => ?_
  unfold firstChernClass
  by_cases hB : ∃ (_ : IsLocallyNoetherian X), X.IsLocallyOfFiniteTypeOverField
  · obtain ⟨hLN, hX⟩ := id hB
    by_cases hd : 0 < d
    · have hA : 0 < d ∧ ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
          ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
            firstChernCapCycle hX L d α = firstChernCapCycle hX L d β := by
        refine ⟨hd, hLN, hX, fun α β hαβ => ?_⟩
        obtain ⟨hα, hβ, hsub⟩ := hαβ
        have h0 := firstChernCapCycle_ratEquivZero_le_ker hX L d
          (x := ⟨α, hα⟩ - ⟨β, hβ⟩) (AddSubgroup.mem_addSubgroupOf.mpr hsub)
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype] at h0
        have h3 : firstChernCapCycle hX L d (α - β) = 0 := h0
        rwa [map_sub, sub_eq_zero] at h3
      refine Eq.trans (dite_addMonoidHom_apply_pos _ _ hA x) ?_
      symm
      exact Eq.trans (dite_addMonoidHom_apply_pos _ _ hB x) rfl
    · have hd0 : d = 0 := by omega
      subst hd0
      refine Eq.trans (dite_addMonoidHom_apply_neg _ _ (fun hc => hd hc.1) x) ?_
      symm
      refine Eq.trans (dite_addMonoidHom_apply_pos _ _ hB x) ?_
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact firstChernCapCycle_dim_zero hX L c.1
  · refine Eq.trans (dite_addMonoidHom_apply_neg _ _ (fun hc => hB ⟨hc.2.1, hc.2.2.1⟩) x) ?_
    symm
    exact dite_addMonoidHom_apply_neg _ _ hB x

/-- (K) When the structural condition holds, the value of `firstChernClass` on the class `[c]` (no `0 < d`
required). -/
theorem firstChernClass_mk' {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : X.IsLocallyOfFiniteTypeOverField) (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (c : ↥(cycleSubgroup X d)) :
    firstChernClass L d (ChowGroup.mk c) = firstChernCapCycle hX L d c.1 := by
  rw [firstChernClass_eq_noIf]
  exact Eq.trans (dite_addMonoidHom_apply_pos _ _ ⟨‹IsLocallyNoetherian X›, hX⟩ _) rfl

/-- (K0) When the structural condition fails, `firstChernClass` is the zero map. **Independent of 02TI**
(read off the definition). -/
theorem firstChernClass_eq_zero_of_not {X : Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (h : ¬ ∃ (_ : IsLocallyNoetherian X), X.IsLocallyOfFiniteTypeOverField) :
    firstChernClass L d = 0 := by
  unfold firstChernClass
  exact dif_neg (fun hc => h ⟨hc.2.1, hc.2.2.1⟩)

/-- (K1) A weak form **independent of 02TI**: `firstChernClass L d [c]` is either `0` or the class of the
cycle-level cap. Used for conclusions where the class of the cap is `0` anyway (such as `c_1(O) ∩ − = 0`),
so that they do not depend on 02TI. -/
theorem firstChernClass_mk_eq_zero_or {X : Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (c : ↥(cycleSubgroup X d)) :
    firstChernClass L d (ChowGroup.mk c) = 0 ∨
      ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
        firstChernClass L d (ChowGroup.mk c) = firstChernCapCycle hX L d c.1 := by
  classical
  unfold firstChernClass
  by_cases hA : 0 < d ∧ ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
      ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
        firstChernCapCycle hX L d α = firstChernCapCycle hX L d β
  · exact Or.inr ⟨hA.2.1, hA.2.2.1, Eq.trans (dite_addMonoidHom_apply_pos _ _ hA _) rfl⟩
  · exact Or.inl (Eq.trans (dite_addMonoidHom_apply_neg _ _ hA _) rfl)

/-- (K2) **Independent of 02TI**: if the cycle-level caps agree as maps to the Chow group, then the
`firstChernClass`es agree (the conditions of the two `if`s are then equivalent). Used e.g. for the
independence of `c_1` of the isomorphism class. -/
theorem firstChernClass_eq_of_capCycle_eq {X : Scheme.{u}} (L L' : X.Modules) [L.IsLineBundle]
    [L'.IsLineBundle] (d : ℕ)
    (h : ∀ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField)
      (β : AlgebraicCycle X ℤ), firstChernCapCycle hX L d β = firstChernCapCycle hX L' d β) :
    firstChernClass L d = firstChernClass L' d := by
  classical
  have key : ∀ (M M' : X.Modules) [M.IsLineBundle] [M'.IsLineBundle],
      (∀ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField)
        (β : AlgebraicCycle X ℤ), firstChernCapCycle hX M d β = firstChernCapCycle hX M' d β) →
      (0 < d ∧ ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
        ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
          firstChernCapCycle hX M d α = firstChernCapCycle hX M d β) →
      (0 < d ∧ ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
        ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
          firstChernCapCycle hX M' d α = firstChernCapCycle hX M' d β) := by
    intro M M' _ _ hMM' hA
    obtain ⟨hd, hLN, hX, hW⟩ := hA
    exact ⟨hd, hLN, hX, fun α β hαβ => by
      rw [← hMM' hLN hX α, ← hMM' hLN hX β]; exact hW α β hαβ⟩
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  unfold firstChernClass
  by_cases hA : 0 < d ∧ ∃ (_ : IsLocallyNoetherian X) (hX : X.IsLocallyOfFiniteTypeOverField),
      ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
        firstChernCapCycle hX L d α = firstChernCapCycle hX L d β
  · have hA' := key L L' h hA
    refine Eq.trans (dite_addMonoidHom_apply_pos _ _ hA _) ?_
    symm
    refine Eq.trans (dite_addMonoidHom_apply_pos _ _ hA' _) ?_
    exact (h hA.2.1 hA.2.2.1 c.1).symm
  · have hA' : ¬ (0 < d ∧ ∃ (_ : IsLocallyNoetherian X)
        (hX : X.IsLocallyOfFiniteTypeOverField),
        ∀ α β : AlgebraicCycle X ℤ, RationallyEquivalent d α β →
          firstChernCapCycle hX L' d α = firstChernCapCycle hX L' d β) :=
      fun hc => hA (key L' L (fun a b β => (h a b β).symm) hc)
    refine Eq.trans (dite_addMonoidHom_apply_neg _ _ hA _) ?_
    symm
    exact dite_addMonoidHom_apply_neg _ _ hA' _

end AlgebraicGeometry
end
