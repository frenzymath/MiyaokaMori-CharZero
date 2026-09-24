import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierCanonicalSection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure

/-! # The cycle of a closed subscheme as a pushforward

Let `X` be locally Noetherian, `I` a quasi-coherent ideal sheaf on `X`, `Z = V(I)` and `ι : Z → X` the
closed immersion.
(a) `Z` is locally Noetherian.
(b) At the level of cycles, `[Z]_d` (`IdealSheafData.cycle`, Stacks 02QU) equals the pushforward
`AlgebraicGeometry.AlgebraicCycle.properPushforward ι ([Z]_d^Z)` (by definition).
(c) In the Chow group: if the pushforward along `ι` descends in dimension `d` (`PushforwardDescends ι d`;
true by Stacks 02S2 when `X` is locally of finite type over a field `k`), then `[Z]_d ∈ Z_d(X)` and its
class is `chowPushforward ι d (Z.fundamentalChowClass d)`.
(d) The hypothesis of (c) holds automatically when `X` is locally of finite type over a field.
(e) Together: if `X` is an integral scheme of dimension `d+1`, locally Noetherian and locally of finite
type over a field `k`, and `D` an effective Cartier divisor, then `c_1(O(D)) ∩ [X]_{d+1} = ι_*[D]_d` in
`CH_d(X)` (`ι : D → X`).

Proof:
1. (a): a closed immersion is locally of finite type; `LocallyOfFiniteType.isLocallyNoetherian`.
2. (b): by definition of `IdealSheafData.cycle`; the locally Noetherian instance inside the definition is a
   `Prop`, equal by proof irrelevance to the one from (a).
3. (c): when `PushforwardDescends` holds, `chowPushforward` takes the positive branch of its `dite`, i.e.
   `QuotientAddGroup.map`; its value at `ChowGroup.mk ⟨[Z]_d^Z, _⟩` is
   `ChowGroup.mk ⟨properPushforward ι [Z]_d^Z, _⟩` (`QuotientAddGroup.map_mk`), membership by
   `properPushforward_mem_cycleSubgroup`; rewrite with (b).
4. (d): `Z` becomes a `k`-scheme through `ι ≫ (X ↘ Spec k)`, `ι` is a `k`-morphism, and the composite of
   a closed immersion with a morphism locally of finite type is locally of finite type; Stacks 02S2 gives
   `PushforwardDescends`.
5. (e): the canonical section satisfies `1_D ≠ 0` and `idealSheafOfSection O(D) 1_D = I_D`; the
   comparison of the cap with the zero-scheme cycle (Stacks 02SQ) for `(O(D), 1_D)` gives the class
   `c_1(O(D)) ∩ [X]_{d+1} = [V(1_D)]_d`, rewritten as the class of `[I_D]_d`; then (c), (d).

Source: comparison of the definition of Stacks 02QU with the pushforward of 02R3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- (a) A closed subscheme of a locally Noetherian scheme is locally Noetherian. -/
instance AlgebraicGeometry.Scheme.IdealSheafData.isLocallyNoetherian_subscheme
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (I : X.IdealSheafData) : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι

/-- (b) `[Z]_d = ι_*([Z]_d^Z)`, with the pushforward used by `chowPushforward` and the projection formula on
the right; `IdealSheafData.cycle` is defined by `AlgebraicGeometry.AlgebraicCycle.properPushforward`, so
this is `rfl`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.cycle_eq_properPushforward
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (I : X.IdealSheafData) (d : ℕ) :
    I.cycle d = AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι (I.subscheme.fundamentalCycle d) :=
  rfl

/-- (c) In the Chow group: when the pushforward descends, the class of `[Z]_d` is `ι_*` of the class of
`[Z]_d^Z`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.chowClass_cycle_eq_chowPushforward
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (I : X.IdealSheafData) (d : ℕ)
    (hdesc : AlgebraicGeometry.PushforwardDescends I.subschemeι d) :
    ∃ h : I.cycle d ∈ AlgebraicGeometry.cycleSubgroup X d,
      AlgebraicGeometry.ChowGroup.mk ⟨I.cycle d, h⟩
        = AlgebraicGeometry.chowPushforward I.subschemeι d (I.subscheme.fundamentalChowClass d) := by
  have hmem := AlgebraicGeometry.properPushforward_mem_cycleSubgroup I.subschemeι d hdesc
    ⟨I.subscheme.fundamentalCycle d,
      (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension _).mpr fun x hx => by
        by_contra h
        exact hx (if_neg h)⟩
  rw [← I.cycle_eq_properPushforward d] at hmem
  refine ⟨hmem, ?_⟩
  have hcp : AlgebraicGeometry.chowPushforward I.subschemeι d
      = QuotientAddGroup.map _ _ (AlgebraicGeometry.cyclePushforwardHom I.subschemeι d hdesc)
          (AlgebraicGeometry.cyclePushforwardHom_rel I.subschemeι d hdesc) := by
    unfold AlgebraicGeometry.chowPushforward
    exact dif_pos hdesc
  rw [hcp]
  have hsub : (⟨I.cycle d, hmem⟩ : ↥(AlgebraicGeometry.cycleSubgroup X d))
      = AlgebraicGeometry.cyclePushforwardHom I.subschemeι d hdesc
          ⟨I.subscheme.fundamentalCycle d,
            (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension _).mpr fun x hx => by
              by_contra h
              exact hx (if_neg h)⟩ :=
    Subtype.ext (I.cycle_eq_properPushforward d)
  rw [hsub]
  rfl

/-- (d) When `X` is locally of finite type over a field `k`, the pushforward along the closed immersion `ι`
descends (Stacks 02S2). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.pushforwardDescends_subschemeι {k : Type u}
    [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (I : X.IdealSheafData) (d : ℕ) :
    AlgebraicGeometry.PushforwardDescends I.subschemeι d :=
  -- `ι` is a closed immersion, so the closed-immersion case of Stacks 02S2 applies (it holds for any
  -- closed immersion, without finite type over a field)
  AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion I.subschemeι d

/-- (e) `c_1(O(D)) ∩ [X]_{d+1} = ι_*[D]_d` (the divisor form of Stacks 02SQ, with the Chow pushforward on
the right). -/
theorem AlgebraicGeometry.EffectiveCartierDivisor.firstChernClass_cap_fundamentalChowClass
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (D : AlgebraicGeometry.EffectiveCartierDivisor X) (d : ℕ) (hX : X.dimension = d + 1) :
    AlgebraicGeometry.firstChernClass D.lineBundle (d + 1) (X.fundamentalChowClass (d + 1))
      = AlgebraicGeometry.chowPushforward D.idealSheaf.subschemeι d
          (D.toScheme.fundamentalChowClass d) := by
  obtain ⟨h, hcap⟩ := AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section
    (k := k) D.lineBundle D.canonicalSection D.canonicalSection_ne_zero d hX
  obtain ⟨h', hpush⟩ := D.idealSheaf.chowClass_cycle_eq_chowPushforward d
    (D.idealSheaf.pushforwardDescends_subschemeι (k := k) d)
  rw [hcap, ← hpush]
  congr 1
  exact Subtype.ext (congrArg (fun I : X.IdealSheafData => I.cycle d)
    D.idealSheafOfSection_canonicalSection)

end
