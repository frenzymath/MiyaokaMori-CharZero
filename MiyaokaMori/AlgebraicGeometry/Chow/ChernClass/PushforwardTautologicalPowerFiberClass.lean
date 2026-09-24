import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PushforwardTautologicalPowerAlgebra
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapEffectiveEqDivisorCycle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupTopDimension
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierCanonicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.HomogeneousEquationSectionAtTotalSpaceSectionLemmas
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks02or

/-! # The cap of a pulled-back point divisor with the fundamental class is the fiber class

The cap of a pulled-back point divisor with the fundamental class is the class of the fiber:
`c_1(π^*O_C(c)) ∩ [Y] = ι_*[Y_c]`. One of the inputs for the pushforward of the tautological power
(`pushforward_taut_pow_eq_fiberDegree`) in the proof of Proposition 2.4 of the paper; the
route is in the docstring of the theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/-- The ℚ-fundamental class of an integral, locally Noetherian, finite-dimensional scheme is the image of the
ℤ-fundamental class `fundamentalChowClass`: the `dite` condition `height ξ = dim X` of `fundamentalClassRat`
holds by `height_genericPoint_eq`, so the positive branch is taken, and `fundamentalCycle_of_isIntegral`
says that `[X]_{dim X}` is the single-point cycle with coefficient `1` at the generic point. -/
theorem AlgebraicGeometry.fundamentalClassRat_eq_of_fundamentalChowClass
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X] (hfin : topologicalKrullDim X ≠ ⊤)
    (s : ℕ) (hs : X.dimension = s) :
    AlgebraicGeometry.fundamentalClassRat X s hs
      = AlgebraicGeometry.ChowGroupRat.of (X.fundamentalChowClass s) := by
  subst hs
  have hη : Order.height (genericPoint X) = (X.dimension : ℕ∞) :=
    AlgebraicGeometry.ChowGroupTopDimension.height_genericPoint_eq hfin
  have hfund := X.fundamentalCycle_of_isIntegral hfin
  unfold AlgebraicGeometry.fundamentalClassRat
  rw [dif_pos hη]
  unfold AlgebraicGeometry.Scheme.fundamentalChowClass
  apply congrArg AlgebraicGeometry.ChowGroupRat.of
  apply congrArg AlgebraicGeometry.ChowGroup.mk
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  have hx := congrFun hfund x
  simpa [Function.locallyFinsuppWithin.single_apply] using hx.symm

/-- The pushforward depends only on the morphism, not on the proof of the `IsProper` instance. -/
theorem AlgebraicGeometry.AlgebraicCycle.properPushforward_congr_hom
    {A B : AlgebraicGeometry.Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsProper g]
    (c : AlgebraicGeometry.AlgebraicCycle A ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f c = AlgebraicGeometry.AlgebraicCycle.properPushforward g c := by
  subst h; rfl

/-- **The cap of a pulled-back point divisor with the fundamental class is the fiber class**: `Y` integral,
`π : Y → C` proper, `c` a closed point, the fiber `Y_c` integral with `dim Y_c = dim Y − 1`; then in
`CH_d(Y)_ℚ`, `c_1(π^*O_C(c)) ∩ [Y] = ι_*[Y_c]` (`ι = π.fiberι c`).

Source: Stacks 02OR (the zero scheme of a pulled-back section is the pullback of the zero scheme), 02SK.

**Proof.**
0. `Over` structures: `Y`, `Y_c` are viewed as `K`-schemes through `π` and `C → Spec K`; both are proper
   over `K` (`C.isProper`, composition of proper morphisms), hence locally of finite type, locally Noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian`) and finite-dimensional
   (`topologicalKrullDim_ne_top_of_isProperOver`). `c` closed ⇒ `fromSpecResidueField c` is a closed
   immersion (`isClosed_singleton_iff_isClosedImmersion`) ⇒ `ι = pullback.fst` is a closed immersion.
1. Let `L := π^*O_C(c)`, `σ := π^*1_c = sectionPullbackAlong π D.canonicalSection`, and
   `I := Z(σ) = idealSheafOfSection L σ`. **`I = ker ι`**: `ker(pullback.fst π g) = (ker g).comap π` for a
   closed immersion `g` (Mathlib's `IdealSheafData.ker_fst_of_isClosedImmersion`); `hD` gives
   `ker(fromSpecResidueField c) = D.idealSheaf = Z(1_c)` (`idealSheafOfSection_canonicalSection`), and 02OR
   (`Scheme.zeroScheme_pullback`) gives `Z(1_c).comap π = Z(π^*1_c) = I`.
2. `σ ≠ 0`: otherwise `I = ⊥` (`idealSheafOfSection_eq_bot_iff`), `ker ι = ⊥`, the closed immersion `ι` is an
   isomorphism (`isIso_iff_ker_eq_bot`), so `dim Y_c = dim Y` (`Scheme.dimension_eq_of_iso`), contradicting
   `hfib`, `hY` (`d ≠ d + 1`).
3. Stacks 02SK (`firstChernClass_cap_fundamentalClass_of_regular_section`):
   `c_1(L) ∩ [Y]_{d+1} = mk⟨I.cycle d, h⟩`; `IdealSheafData.chowClass_cycle_eq_chowPushforward` (descent
   condition `pushforwardDescends_of_isClosedImmersion`): `mk⟨I.cycle d, h⟩ = (I.subschemeι)_* [I.subscheme]_d`.
4. The isomorphism `e : I.subscheme ≅ Y_c` is compatible with the embeddings into `Y`:
   `ker ι = I = ker I.subschemeι` (`ker_subschemeι`), and Mathlib's `IsClosedImmersion.lift` / `isIso_lift` /
   `lift_fac` give `e.hom ≫ ι = I.subschemeι`. Transport the fundamental class along `e`: `chowPushforward_mk`
   reduces both sides to cycles, and `fundamentalCycle_properPushforward_of_iso e` with
   `properPushforward_comp` give `(I.subschemeι)_*[I.subscheme]_d = ι_*(e_*[I.subscheme]_d) = ι_*[Y_c]_d`.
5. Pass to ℚ: `ratDivisorOpOfLineBundle L d = (c_1(L) (d+1)).ratExtend` and
   `chowPushforwardRat ι d = (chowPushforward ι d).ratExtend` hold by definition;
   `fundamentalClassRat X s hs = of (X.fundamentalChowClass s)` (`fundamentalClassRat_eq_of_fundamentalChowClass`
   in this file), and `ratExtend` on `1 ⊗ₜ z` is `1 ⊗ₜ φ z` (`rfl`). -/
theorem AlgebraicGeometry.ratDivisorOpOfLineBundle_pullback_pointDivisor_fundamentalClassRat
    {K : Type u} [Field K] {C : SmoothProjectiveCurve K} {Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] (π : Y ⟶ C.carrier) [AlgebraicGeometry.IsProper π]
    (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier))
    (D : AlgebraicGeometry.EffectiveCartierDivisor C.carrier)
    (hD : D.idealSheaf = (C.carrier.fromSpecResidueField c).ker)
    (d : ℕ) (hY : Y.dimension = d + 1) [AlgebraicGeometry.IsIntegral (π.fiber c)]
    (hfib : (π.fiber c).dimension = d) :
    haveI : AlgebraicGeometry.IsProper (π.fiberι c) := AlgebraicGeometry.isProper_fiberι_of_isClosed π c hc
    AlgebraicGeometry.ratDivisorOpOfLineBundle
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj D.lineBundle) d
        (AlgebraicGeometry.fundamentalClassRat Y (d + 1) hY)
      = AlgebraicGeometry.chowPushforwardRat (π.fiberι c) d
          (AlgebraicGeometry.fundamentalClassRat (π.fiber c) d hfib) := by
  -- `Over` structures: `Y` and `Y_c` as `K`-schemes through `C` (locally of finite type, locally Noetherian,
  -- finite-dimensional)
  let _ : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hC : IsProperOver K C.carrier := C.isProper
  have hYprop : IsProperOver K Y := by
    change AlgebraicGeometry.IsProper (π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have : AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hYprop
  have : AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    inferInstance
  have : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  have hfinY : topologicalKrullDim Y ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver (k := K) Y hYprop
  have hι : AlgebraicGeometry.IsProper (π.fiberι c) :=
    AlgebraicGeometry.isProper_fiberι_of_isClosed π c hc
  have : AlgebraicGeometry.IsClosedImmersion (C.carrier.fromSpecResidueField c) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hc
  have hιcl : AlgebraicGeometry.IsClosedImmersion (π.fiberι c) :=
    (inferInstance : AlgebraicGeometry.IsClosedImmersion
      (CategoryTheory.Limits.pullback.fst π (C.carrier.fromSpecResidueField c)))
  have : AlgebraicGeometry.IsLocallyNoetherian (π.fiber c) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (π.fiberι c)
  let _ : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have hFprop : IsProperOver K (π.fiber c) := by
    change AlgebraicGeometry.IsProper
      (π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have hfinF : topologicalKrullDim (π.fiber c) ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver (k := K) (π.fiber c) hFprop
  -- notation: `L = π^*O_C(c)`, `σ = π^*1_c`, `I = Z(σ)`
  set L : Y.Modules := (AlgebraicGeometry.Scheme.Modules.pullback π).obj D.lineBundle with hL
  set σ : (L.val.obj (Opposite.op ⊤) : Type u) := sectionPullbackAlong π D.canonicalSection with hσdef
  set I : Y.IdealSheafData := AlgebraicGeometry.Scheme.idealSheafOfSection L σ with hI
  -- step 1 (02OR + `hD`): `I = ker(π.fiberι c)`
  have hker : (π.fiberι c).ker = I := by
    change (CategoryTheory.Limits.pullback.fst π (C.carrier.fromSpecResidueField c)).ker = I
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hD,
      ← D.idealSheafOfSection_canonicalSection]
    exact (AlgebraicGeometry.Scheme.zeroScheme_pullback π D.lineBundle D.canonicalSection).symm
  -- step 2: `σ ≠ 0` (otherwise `I = ⊥`, the fiber embedding is an isomorphism, contradicting the dimensions)
  have hσ : σ ≠ 0 := by
    intro h0
    have hbot : I = ⊥ := (AlgebraicGeometry.Scheme.idealSheafOfSection_eq_bot_iff L σ).mpr h0
    have : CategoryTheory.IsIso (π.fiberι c) :=
      AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (hker.trans hbot)
    have hdim := AlgebraicGeometry.Scheme.dimension_eq_of_iso (CategoryTheory.asIso (π.fiberι c))
    omega
  -- step 3 (02SK): `c_1(L) ∩ [Y]_{d+1} = [I.cycle d] = (I.subschemeι)_*[I.subscheme]_d`
  obtain ⟨h, hcap⟩ := AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section
    (k := K) L σ hσ d hY
  obtain ⟨h', hpush⟩ := I.chowClass_cycle_eq_chowPushforward d
    (AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion I.subschemeι d)
  -- step 4: `I.subscheme ≅ π.fiber c`, compatibly with the embeddings into `Y`
  have hkereq : (π.fiberι c).ker = I.subschemeι.ker := by rw [hker, I.ker_subschemeι]
  let φ : I.subscheme ⟶ π.fiber c :=
    AlgebraicGeometry.IsClosedImmersion.lift (π.fiberι c) I.subschemeι hkereq.le
  have : CategoryTheory.IsIso φ := AlgebraicGeometry.IsClosedImmersion.isIso_lift _ _ hkereq
  let e : I.subscheme ≅ π.fiber c := CategoryTheory.asIso φ
  have hφ : e.hom ≫ π.fiberι c = I.subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac (π.fiberι c) I.subschemeι hkereq.le
  -- step 4 (continued): transport the fundamental class along the isomorphism
  have hchow : AlgebraicGeometry.chowPushforward I.subschemeι d (I.subscheme.fundamentalChowClass d)
      = AlgebraicGeometry.chowPushforward (π.fiberι c) d ((π.fiber c).fundamentalChowClass d) := by
    unfold AlgebraicGeometry.Scheme.fundamentalChowClass
    rw [AlgebraicGeometry.chowPushforward_mk _ _
        (AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion _ d),
      AlgebraicGeometry.chowPushforward_mk _ _
        (AlgebraicGeometry.pushforwardDescends_of_isClosedImmersion _ d)]
    congr 1
    apply Subtype.ext
    change AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι (I.subscheme.fundamentalCycle d)
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (π.fiberι c) ((π.fiber c).fundamentalCycle d)
    rw [← AlgebraicGeometry.Scheme.fundamentalCycle_properPushforward_of_iso e d,
      AlgebraicGeometry.AlgebraicCycle.properPushforward_comp]
    exact AlgebraicGeometry.AlgebraicCycle.properPushforward_congr_hom hφ.symm _
  -- step 5: pass to ℚ
  have hYrat := AlgebraicGeometry.fundamentalClassRat_eq_of_fundamentalChowClass Y hfinY (d + 1) hY
  have hFrat := AlgebraicGeometry.fundamentalClassRat_eq_of_fundamentalChowClass (π.fiber c) hfinF d hfib
  change (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend
      (AlgebraicGeometry.fundamentalClassRat Y (d + 1) hY)
    = (AlgebraicGeometry.chowPushforward (π.fiberι c) d).ratExtend
      (AlgebraicGeometry.fundamentalClassRat (π.fiber c) d hfib)
  rw [hYrat, hFrat]
  change ((1 : ℚ) ⊗ₜ[ℤ] AlgebraicGeometry.firstChernClass L (d + 1) (Y.fundamentalChowClass (d + 1)) :
      AlgebraicGeometry.ChowGroupRat Y d)
    = ((1 : ℚ) ⊗ₜ[ℤ] AlgebraicGeometry.chowPushforward (π.fiberι c) d
        ((π.fiber c).fundamentalChowClass d) : AlgebraicGeometry.ChowGroupRat Y d)
  rw [hcap, hpush, hchow]

end
