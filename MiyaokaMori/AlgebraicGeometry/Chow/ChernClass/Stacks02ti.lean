import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycleUnit
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapLocallyFiniteSum
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks0ayc
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointClosurePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # The cap with the first Chern class descends to rational equivalence (Stacks 02TI)

Stacks 02TI: the cycle-level `c_1(L) ∩ −` is invariant under rational equivalence (`X` locally of finite
type over a field), hence descends to `CH_d(X) → CH_{d−1}(X)`.

Source: Stacks 02TI (the proof uses 02SU, the compatibility of pushforward and cap; 02TH, commutativity on
integral schemes; 02SP, additivity). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The integral case (second paragraph of the proof of Stacks 02TI): `W` integral, locally of finite type
over a field, `dim W = n + 2`; then `c_1(M) ∩ div_W(f) = 0 ∈ CH_n(W)`. View `f` as a rational section `t` of
`O_W`, take a nonzero rational section `s` of `M`; the key formula (Stacks 0AYC) gives
`c_1(M) ∩ div(t) = c_1(O_W) ∩ div_M(s)`, and the right side vanishes (`FirstChernCapCycleUnit.lean`). -/
theorem AlgebraicGeometry.firstChernCapCycle_principalCycle_eq_zero {K : Type u} [Field K]
    {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    [AlgebraicGeometry.IsLocallyNoetherian W]
    (π : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) [AlgebraicGeometry.LocallyOfFiniteType π]
    (M : W.Modules) [M.IsLineBundle] (n : ℕ) (hW : W.dimension = n + 2) (f : W.functionFieldˣ) :
    AlgebraicGeometry.firstChernCapCycle ⟨K, inferInstance, π, inferInstance⟩ M (n + 1)
      (W.principalCycle f) = 0 := by
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨t, ht, hdiv⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_unit_rationalSection_divisor_eq_principalCycle f
  rw [← hdiv, ← AlgebraicGeometry.keyFormula_ratEquivZero K π M
    (SheafOfModules.unit W.ringCatSheaf) n hW s t hs ht]
  exact AlgebraicGeometry.firstChernCapCycle_unit_eq_zero _ _ _

/-- A single generator (first paragraph of the proof of Stacks 02TI): `w` of height `d + 1`, `W_w` integral
and locally Noetherian, `f ∈ K(W_w)^×`; then `c_1(L) ∩ ι_{w*} div(f) = 0 ∈ CH_{d−1}(X)`. Use 02SU (at the
level of cycles) to move the problem to `W_w`, then the integral case. -/
theorem AlgebraicGeometry.firstChernCapCycle_generator_eq_zero {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ) (w : X)
    (hw : Order.height w = ((d + 1 : ℕ) : ℕ∞))
    [AlgebraicGeometry.IsIntegral (X.pointClosure w)]
    [AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w)]
    (f : (X.pointClosure w).functionFieldˣ) :
    AlgebraicGeometry.firstChernCapCycle
        (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X) L d
        (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle f))
      = 0 := by
  cases d with
  | zero => exact AlgebraicGeometry.firstChernCapCycle_dim_zero _ L _
  | succ d =>
    let _ : (X.pointClosure w).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨X.pointClosureι w ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    have hLFT : AlgebraicGeometry.LocallyOfFiniteType
        ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
        (X.pointClosureι w ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    have hover : (X.pointClosureι w).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    have hdim : topologicalKrullDim (X.pointClosure w) = ((d + 1 + 1 : ℕ) : WithBot ℕ∞) :=
      AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure w hw
    have hγ : (X.pointClosure w).principalCycle f ∈
        AlgebraicGeometry.cycleSubgroup (X.pointClosure w) (d + 1) :=
      AlgebraicGeometry.Scheme.principalCycle_mem_cycleSubgroup
        ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hdim f
    -- the special case of 02SU for the closed immersion of a point closure
    have h02su := AlgebraicGeometry.chowPushforward_firstChernCapCycle_pullback_pointClosureι
      (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X) w
      (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) (X.pointClosure w))
      L d ((X.pointClosure w).principalCycle f)
    have hzero := AlgebraicGeometry.firstChernCapCycle_principalCycle_eq_zero
      ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L) d
      (AlgebraicGeometry.Scheme.dimension_pointClosure w hw) f
    exact h02su.symm.trans ((congrArg _ hzero).trans (map_zero _))

/-- **Stacks 02SU at the level of cycles, with restricted support.**

The first paragraph of the proof of Stacks 02TI uses the proper pushforward along `p : ∐ W_j → X` to rewrite
`c_1(L) ∩ α` as `p_*(c_1(p^*L) ∩ α')` and then treats each component. Without `∐`, this step reads: at the
level of cycles, `c_1(L) ∩ (ι_w)_* γ` and `(ι_w)_*(c_1(ι_w^*L) ∩ γ)` differ by a rationally trivial cycle,
**and the witnessing family of this rational equivalence lies in `W_w = closure{w}`**.

The support information cannot be dropped: the first paragraph of Stacks 02RZ says that knowing only that
each `α_i` is rationally trivial does not imply that `Σ α_i` is; the remedy of the second paragraph is
exactly that the witnessing families lie in a locally finite family of closed sets `{T_i}`. Hence the
Chow-group form `chowPushforward_firstChernCapCycle_pullback` does not suffice for the locally finite
sum version of 02TI.

Proof route: as for 02SU (02SH change of section + compatibility of pushforward along closed immersions
with `div`), keeping track that the principal cycles produced by the change of section come from points of
`W_w`, so their generic points lie in `closure {w}`. -/
theorem AlgebraicGeometry.firstChernCapCycleAux_pointClosure_sub_mem
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (w : X)
    [AlgebraicGeometry.IsIntegral (X.pointClosure w)]
    [AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w)]
    (γ : AlgebraicGeometry.AlgebraicCycle (X.pointClosure w) ℤ) :
    AlgebraicGeometry.firstChernCapCycleAux L d
        (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ)
      - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
          (AlgebraicGeometry.firstChernCapCycleAux
            ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L) d γ)
      ∈ AlgebraicGeometry.ratEquivZeroOn X (d - 1) (closure {w}) :=
  MiyaokaMori.FirstChernCapPointClosurePushforward.firstChernCapCycleAux_pointClosure_sub_mem
    L d w γ

/-- **Stacks 02S2 along the closed immersion of a point closure, with restricted support.**

`ι_w : W_w → X` is a closed immersion; it sends rationally trivial cycles on `W_w` to rationally trivial
cycles on `X`, **with witnessing family still inside `W_w`**: a point `v` of `W_w` of height `p+1`
corresponds to the point `ι_w(v)` of `X`, their point closures are isomorphic with the same function field,
so `(ι_w)_*((ι_v)_* div f) = (ι_{ι_w(v)})_* div f`, and `ι_w(v) ∈ closure {w}`. The support part is
automatic; the content is "generators map to generators" (the closed-immersion case of Stacks 02S2). -/
theorem AlgebraicGeometry.properPushforward_pointClosure_mem_ratEquivZeroOn
    {X : AlgebraicGeometry.Scheme.{u}} (w : X)
    [AlgebraicGeometry.IsIntegral (X.pointClosure w)]
    [AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w)] (p : ℕ)
    (γ : AlgebraicGeometry.AlgebraicCycle (X.pointClosure w) ℤ)
    (hγ : γ ∈ AlgebraicGeometry.ratEquivZero (X.pointClosure w) p) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) γ
      ∈ AlgebraicGeometry.ratEquivZeroOn X p (closure {w}) :=
  MiyaokaMori.ClosedImmersionPushforward.properPushforward_pointClosure_mem_ratEquivZeroOn
    w p γ hγ

/-- A single generator (first paragraph of the proof of Stacks 02TI), in the **restricted-support** form:
the witnesses of the rational equivalence `c_1(L) ∩ ι_{w*} div(f) ~ 0` can be taken inside
`W_w = closure {w}`.

This strengthens the Chow-group statement `firstChernCapCycle_generator_eq_zero` to the form usable in
locally finite sums; the two strengthening steps are the two preceding statements, and the integral case
still goes through 0AYC (`firstChernCapCycle_principalCycle_eq_zero`). -/
theorem AlgebraicGeometry.firstChernCapCycleAux_generator_mem_ratEquivZeroOn {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ) (w : X)
    (hw : Order.height w = ((d + 1 : ℕ) : ℕ∞))
    [AlgebraicGeometry.IsIntegral (X.pointClosure w)]
    [AlgebraicGeometry.IsLocallyNoetherian (X.pointClosure w)]
    (f : (X.pointClosure w).functionFieldˣ) :
    AlgebraicGeometry.firstChernCapCycleAux L d
        (AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
          ((X.pointClosure w).principalCycle f))
      ∈ AlgebraicGeometry.ratEquivZeroOn X (d - 1) (closure {w}) := by
  cases d with
  | zero =>
    rw [AlgebraicGeometry.firstChernCapCycleAux_dim_zero]
    exact zero_mem _
  | succ e =>
    let _ : (X.pointClosure w).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨X.pointClosureι w ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    have hLFT : AlgebraicGeometry.LocallyOfFiniteType
        ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
        (X.pointClosureι w ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    have h0 := AlgebraicGeometry.firstChernCapCycle_principalCycle_eq_zero
      ((X.pointClosure w) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L) e
      (AlgebraicGeometry.Scheme.dimension_pointClosure w hw) f
    have hW : AlgebraicGeometry.firstChernCapCycleAux
        ((AlgebraicGeometry.Scheme.Modules.pullback (X.pointClosureι w)).obj L) (e + 1)
        ((X.pointClosure w).principalCycle f)
        ∈ AlgebraicGeometry.ratEquivZero (X.pointClosure w) e := by
      have h1 := (QuotientAddGroup.eq_zero_iff _).mp h0
      rwa [AddSubgroup.mem_addSubgroupOf] at h1
    have hpush := AlgebraicGeometry.properPushforward_pointClosure_mem_ratEquivZeroOn w e _ hW
    have hA := AlgebraicGeometry.firstChernCapCycleAux_pointClosure_sub_mem L (e + 1) w
      ((X.pointClosure w).principalCycle f)
    have := (AlgebraicGeometry.ratEquivZeroOn X e (closure {w})).add_mem hA hpush
    simpa using this

/-- **The main statement of Stacks 02TI**: the cycle-level `c_1(L) ∩ −` sends rationally equivalent cycles
to the same class. No quasi-compactness is assumed: `ratEquivZero` is the sum of a **locally finite** family
as in Stacks 02RW (Stacks 02RV explains that without locally finite sums this statement is not known), and
the proof follows Stacks: `c_1(L) ∩ −` commutes with locally finite sums
(`firstChernCapCycleAux_of_locallyFiniteSum`), the witnesses of rational equivalence for each generator lie
in `W_j = closure {w_j}` (`firstChernCapCycleAux_generator_mem_ratEquivZeroOn`), the family `{W_j}` is
locally finite, and the second paragraph of Stacks 02RZ (`ratEquivZero_of_locallyFinite_sum`) assembles the
witnesses into a single one. -/
theorem AlgebraicGeometry.firstChernCapCycle_rationallyEquivalent {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    (α β : AlgebraicGeometry.AlgebraicCycle X ℤ) (h : AlgebraicGeometry.RationallyEquivalent d α β) :
    AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X) L d α =
      AlgebraicGeometry.firstChernCapCycle (AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X) L d β := by
  obtain ⟨-, -, hsub⟩ := h
  have hXk := AlgebraicGeometry.Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  have key : ∀ c ∈ AlgebraicGeometry.ratEquivZero X d,
      AlgebraicGeometry.firstChernCapCycle hXk L d c = 0 := by
    intro c hc
    obtain ⟨J, w, cj, -, hg, hlf, hs⟩ := hc
    show AlgebraicGeometry.ChowGroup.mk
      ⟨AlgebraicGeometry.firstChernCapCycleAux L d c,
        AlgebraicGeometry.firstChernCapCycleAux_mem hXk L d c⟩ = 0
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine AlgebraicGeometry.ratEquivZero_of_locallyFinite_sum (fun j => closure {w j})
      ((AlgebraicGeometry.locallyFinitePoints_iff_locallyFinite_closure w).mp hlf) _
      (fun j => AlgebraicGeometry.firstChernCapCycleAux L d (cj j)) (fun j => ?_) (fun z => ?_)
    · obtain ⟨hwj, hint, hci, hLN, f, hcf⟩ := hg j
      rw [hcf]
      exact AlgebraicGeometry.firstChernCapCycleAux_generator_mem_ratEquivZeroOn
        (k := k) L d (w j) hwj f
    · exact AlgebraicGeometry.firstChernCapCycleAux_of_locallyFiniteSum L d hlf
        (fun j t htne => (hg j).specializes htne) c hs z
  have h0 := key _ hsub
  rwa [map_sub, sub_eq_zero] at h0

end
