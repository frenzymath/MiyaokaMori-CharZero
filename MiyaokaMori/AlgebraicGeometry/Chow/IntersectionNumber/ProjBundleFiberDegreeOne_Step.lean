import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle

/-! # Inductive step for top self-intersections through a zero scheme

Inductive step for top self-intersection numbers: if `X` is proper over `k` of dimension `m + 1`,
`L` a line bundle and `Z ⊂ X` a closed subscheme with `c₁(L) ∩ [X] = [Z]_m` in `A_m(X)`
(e.g. `Z = Z(σ)` for a nonzero global section `σ` of `L` when `X` is integral, Stacks 02SQ),
then `(L^{m+1})_X = ((L|_Z)^m)_Z` provided `dim Z = m`.

Source: Fulton, Intersection Theory, Prop. 2.3(c) (projection formula) + Prop. 2.5(c) / Stacks 02TW proof
(cutting by hyperplane sections). Proof: `(L^{m+1})_X = deg(c₁(L)^m ∩ (c₁(L) ∩ [X]))`;
`c₁(L) ∩ [X] = ι_*[Z]` (hypothesis, via `IdealSheafData.chowClass_cycle_eq_chowPushforward`);
`c₁(L)^m ∩ ι_*[Z] = ι_*(c₁(ι^*L)^m ∩ [Z])` (iterated projection formula
`chowPushforward_capPow_of_pullbackIso`); `deg ι_* = deg` (`degreeOver_chowPushforward`).

Implementation note: `chowPushforward` is written with its full name `AlgebraicGeometry.chowPushforward`.
Under `open AlgebraicGeometry` the bare name is an overload of the variety-side and scheme-side names,
and unifying the types of the variety-side candidate (`?X.toScheme =?= I.subscheme`, unfolding
`IdealSheafData.subscheme`) is expensive (it exceeds the heartbeat limit); with the full name the file elaborates in 5 s.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry

/-- `topSelfIntersection` at a known dimension `d`. -/
theorem topSelfIntersection_eq_of_dimension_eq {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] {d : ℕ} (hd : X.dimension = d) :
    topSelfIntersection X hX L =
      ChowGroup.degreeOver k X hX (firstChernClass.capPow L d 0
        (cast (congrArg (ChowGroup X) (zero_add d).symm) (X.fundamentalChowClass d))) := by
  subst hd
  rfl

/-- `cast` along the dimension index commutes with `AlgebraicGeometry.chowPushforward`. -/
theorem chowPushforward_cast {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {d d' : ℕ} (h : d = d')
    (α : ChowGroup X d) :
    AlgebraicGeometry.chowPushforward f d' (cast (congrArg (ChowGroup X) h) α)
      = cast (congrArg (ChowGroup Y) h) (AlgebraicGeometry.chowPushforward f d α) := by
  subst h
  rfl

/-- **Inductive step (general form).** `X` proper over `k` of dimension `m + 1`, `L` a line bundle,
`I` an ideal sheaf with closed subscheme `Z = I.subscheme`, `ι : Z → X`, such that
`c₁(L) ∩ [X]_{m+1} = [Z]_m` (the class of `I.cycle m`). Then `(L^{m+1})_X = ((ι^*L)^m)_Z`,
provided `dim Z = m` (and `Z` is proper over `k` via `ι`). -/
theorem topSelfIntersection_eq_of_firstChernClass_cap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (m : ℕ) (hdX : X.dimension = m + 1)
    (I : X.IdealSheafData) [I.subscheme.Over (Spec (CommRingCat.of k))]
    [I.subschemeι.IsOver (Spec (CommRingCat.of k))]
    (hZ : IsProperOver k I.subscheme) (hdZ : I.subscheme.dimension = m)
    [((Scheme.Modules.pullback I.subschemeι).obj L).IsLineBundle]
    (hcap : ∃ h : I.cycle m ∈ cycleSubgroup X m,
      firstChernClass L (m + 1) (X.fundamentalChowClass (m + 1)) = ChowGroup.mk ⟨I.cycle m, h⟩) :
    topSelfIntersection X hX L =
      topSelfIntersection I.subscheme hZ ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  haveI : IsProper (I.subscheme ↘ Spec (CommRingCat.of k)) := hZ
  haveI : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subscheme ↘ Spec (CommRingCat.of k))
  obtain ⟨h, hcap⟩ := hcap
  obtain ⟨h', hpush⟩ := I.chowClass_cycle_eq_chowPushforward m
    (I.pushforwardDescends_subschemeι (k := k) m)
  have step1 : firstChernClass L (m + 1) (X.fundamentalChowClass (m + 1)) =
      AlgebraicGeometry.chowPushforward I.subschemeι m (I.subscheme.fundamentalChowClass m) := by
    rw [hcap, ← hpush]
  have key : ∀ (e : ℕ) (he : m = e),
      firstChernClass L (e + 1)
          (cast (congrArg (ChowGroup X) (congrArg Nat.succ he)) (X.fundamentalChowClass (m + 1)))
        = cast (congrArg (ChowGroup X) he)
            (AlgebraicGeometry.chowPushforward I.subschemeι m (I.subscheme.fundamentalChowClass m)) := by
    intro e he
    subst he
    simpa using step1
  rw [topSelfIntersection_eq_of_dimension_eq X hX L hdX,
    topSelfIntersection_eq_of_dimension_eq _ hZ _ hdZ,
    ← MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hZ hX I.subschemeι,
    chowPushforward_capPow_of_pullbackIso (k := k) I.subschemeι L _ ⟨Iso.refl _⟩ m 0]
  refine congrArg (ChowGroup.degreeOver k X hX) ?_
  show (firstChernClass.capPow L m 0)
      (firstChernClass L (0 + m + 1)
        (cast (congrArg (ChowGroup X) (zero_add (m + 1)).symm) (X.fundamentalChowClass (m + 1)))) = _
  rw [chowPushforward_cast I.subschemeι (zero_add m).symm]
  exact congrArg (firstChernClass.capPow L m 0) (key (0 + m) (zero_add m).symm)

/-- **Inductive step for the zero scheme of a section.** `X` integral, proper over `k`, of dimension
`m + 1`; `σ ≠ 0` a global section of the line bundle `L`; `Z = Z(σ)` (Stacks 02SQ:
`c₁(L) ∩ [X] = [Z(σ)]`, `firstChernClass_cap_fundamentalClass_of_regular_section`). Then
`(L^{m+1})_X = ((L|_Z)^m)_Z` provided `dim Z = m`. -/
theorem topSelfIntersection_eq_zeroScheme {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsIntegral X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (op ⊤) : Type u)) (hσ : σ ≠ 0)
    (m : ℕ) (hdX : X.dimension = m + 1)
    [(Scheme.idealSheafOfSection L σ).subscheme.Over (Spec (CommRingCat.of k))]
    [(Scheme.idealSheafOfSection L σ).subschemeι.IsOver (Spec (CommRingCat.of k))]
    (hZ : IsProperOver k (Scheme.idealSheafOfSection L σ).subscheme)
    (hdZ : (Scheme.idealSheafOfSection L σ).subscheme.dimension = m)
    [((Scheme.Modules.pullback (Scheme.idealSheafOfSection L σ).subschemeι).obj L).IsLineBundle] :
    topSelfIntersection X hX L =
      topSelfIntersection (Scheme.idealSheafOfSection L σ).subscheme hZ
        ((Scheme.Modules.pullback (Scheme.idealSheafOfSection L σ).subschemeι).obj L) := by
  haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  haveI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  exact topSelfIntersection_eq_of_firstChernClass_cap_eq hX L m hdX _ hZ hdZ
    (firstChernClass_cap_fundamentalClass_of_regular_section (k := k) L σ hσ m hdX)

end ProjBundleFiberDegreeOne

end
