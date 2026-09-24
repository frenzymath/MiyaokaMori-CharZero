import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward

/-! # The degree of a point divisor is one

The degree of a point divisor is `1`: `deg_C(c_1(O_C(c)) ∩ [C]_ℚ) = 1`. One of the inputs for the
pushforward of the tautological power (`pushforward_taut_pow_eq_fiberDegree`) in the proof of Proposition 2.4 of the paper; the route is in the docstring of the theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The degree of a point divisor is `1`**: `deg_C(c_1(O_C(c)) ∩ [C]_ℚ) = 1` (`K` algebraically closed).

Source: Stacks 02SK (`c_1(O(D)) ∩ [X] = [D]`); the degree computation in the proof of Proposition 2.4 of the paper.

**Proof.**
1. `fundamentalClassRat C 1 hdimC = ChowGroupRat.of (C.fundamentalChowClass 1)`: `C` is integral, locally
   Noetherian (of finite type over `K`) and finite-dimensional (`C.dim_one`); `fundamentalCycle_of_isIntegral`
   says `[C]_1` is the cycle with multiplicity `1` at the generic point `η`; the `if` condition
   `Order.height η = 1` of `fundamentalClassRat` holds by `height_genericPoint_of_dimension_pos hdimC`, so
   both sides are `of(mk(single η 1))`.
2. `ratDivisorOpOfLineBundle D.lineBundle 0 = (firstChernClass D.lineBundle 1).ratExtend`, and `ratExtend`
   is compatible with `of` (`LinearMap.baseChange_tmul`), so the left side is the degree of
   `of(c_1(O(D)) ∩ [C]_1)`, i.e. `degreeOver K C (c_1(O(D)) ∩ [C]_1)` (`ChowGroupRat.degree_tmul`, `q = 1`).
3. Stacks 02SK: `EffectiveCartierDivisor.firstChernClass_cap_fundamentalChowClass` (`d = 0`, `hX = hdimC`):
   `c_1(O(D)) ∩ [C]_1 = ι_*([D]_0)`, `ι : D.toScheme → C` a closed immersion (`IsClosedImmersion I.subschemeι`,
   hence proper).
4. The degree is compatible with the pushforward: `degreeOver_chowPushforward` (`D.toScheme` is proper over
   `K`: closed immersion ≫ proper): `degreeOver K C (ι_*[D]_0) = degreeOver K D.toScheme [D]_0`.
5. `D.toScheme ≅ Spec κ(c)`: `ι` and `j := fromSpecResidueField c` are both closed immersions (`{c}` is
   closed, Mathlib's `isClosed_singleton_iff_isClosedImmersion`) with equal kernels (`ker_subschemeι` + `hD`),
   so Mathlib's `IsClosedImmersion.lift ι j` is an isomorphism (`isIso_lift`) with `lift ≫ ι = j`
   (`lift_fac`). Fundamental class and degree are transported along the isomorphism
   (`chowPushforward_fundamentalChowClass_of_iso`, `degreeOver_chowPushforward_of_iso`).
6. `Spec κ(c)` is a one-point (Mathlib's `Unique (Spec (X.residueField x))`) integral scheme, whose
   zero-dimensional fundamental cycle has `integralFundamentalMultiplicity = 1` at the point
   (`pointClosureDimension_eq_height` + `height_eq_zero`; the stalk at the generic point is the field
   `functionField`, of length `1`, as in `fundamentalCycle_of_isIntegral`); `degreeOver` is
   `Σ multiplicity × residue degree` (`finsum_unique`) `= [κ(c) : K]`.
7. `K` algebraically closed, `c` closed, `C` of finite type over `K` ⇒ `[κ(c) : K] = 1`
   (`AlgebraicGeometry.Intersection.residueFieldDegree_eq_one` applied to `j ≫ (C ↘ Spec K)`, converted to Mathlib's
   `residueDegree` by `residueFieldDegree_eq_residueDegree`). Altogether the degree is `1`. -/
theorem SmoothProjectiveCurve.degree_pointDivisor_cap_fundamentalClassRat {K : Type u} [Field K]
    [IsAlgClosed K] (C : SmoothProjectiveCurve K) (hC : IsProperOver K C.carrier)
    (hdimC : C.carrier.dimension = 1) (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier))
    (D : AlgebraicGeometry.EffectiveCartierDivisor C.carrier)
    (hD : D.idealSheaf = (C.carrier.fromSpecResidueField c).ker) :
    AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle D.lineBundle 0
          (AlgebraicGeometry.fundamentalClassRat C.carrier 1 hdimC)) = 1 := by
  classical
  have _ : AlgebraicGeometry.IsProper (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hC
  -- step 1: `[C]_ℚ = of [C]_1`
  have hfin : topologicalKrullDim C.carrier ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_dimension_pos (m := 0) hdimC
  have hη : Order.height (genericPoint C.carrier) = ((1 : ℕ) : ℕ∞) :=
    AlgebraicGeometry.height_genericPoint_of_dimension_pos (m := 0) hdimC
  have h1 : AlgebraicGeometry.fundamentalClassRat C.carrier 1 hdimC
      = AlgebraicGeometry.ChowGroupRat.of (C.carrier.fundamentalChowClass 1) := by
    unfold AlgebraicGeometry.fundamentalClassRat
    rw [dif_pos hη]
    congr 1
    unfold AlgebraicGeometry.Scheme.fundamentalChowClass
    congr 1
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    have h := congrFun (C.carrier.fundamentalCycle_of_isIntegral hfin) x
    rw [hdimC] at h
    show Function.locallyFinsuppWithin.single (genericPoint C.carrier) (1 : ℤ) x = _
    rw [h, Function.locallyFinsuppWithin.single_apply]
  -- step 3 (Stacks 02SK): `c_1(O(D)) ∩ [C]_1 = ι_*[D]_0`
  have h3 : AlgebraicGeometry.firstChernClass D.lineBundle (0 + 1)
        (C.carrier.fundamentalChowClass (0 + 1))
      = AlgebraicGeometry.chowPushforward D.idealSheaf.subschemeι 0
          (D.toScheme.fundamentalChowClass 0) :=
    AlgebraicGeometry.EffectiveCartierDivisor.firstChernClass_cap_fundamentalChowClass
      (k := K) D 0 hdimC
  -- step 2: `ratExtend` is compatible with `of`
  have h2 : AlgebraicGeometry.ratDivisorOpOfLineBundle D.lineBundle 0
        (AlgebraicGeometry.ChowGroupRat.of (C.carrier.fundamentalChowClass 1))
      = AlgebraicGeometry.ChowGroupRat.of
          (AlgebraicGeometry.chowPushforward D.idealSheaf.subschemeι 0
            (D.toScheme.fundamentalChowClass 0)) := by
    rw [← h3]
    exact LinearMap.baseChange_tmul
      (AlgebraicGeometry.firstChernClass D.lineBundle (0 + 1)).toIntLinearMap (1 : ℚ)
      (C.carrier.fundamentalChowClass (0 + 1))
  have hdeg : ∀ β : AlgebraicGeometry.ChowGroup C.carrier 0,
      AlgebraicGeometry.ChowGroupRat.degree C.carrier hC (AlgebraicGeometry.ChowGroupRat.of β)
        = (AlgebraicGeometry.ChowGroup.degreeOver K C.carrier hC β : ℚ) := by
    intro β
    show AlgebraicGeometry.ChowGroupRat.degree C.carrier hC ((1 : ℚ) ⊗ₜ[ℤ] β) = _
    rw [AlgebraicGeometry.ChowGroupRat.degree_tmul, one_mul]
  -- step 4: `D.toScheme` as a `K`-scheme; the degree is compatible with the pushforward
  let _ : D.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨D.idealSheaf.subschemeι ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have _ : D.idealSheaf.subschemeι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hDp : IsProperOver K D.toScheme := by
    change AlgebraicGeometry.IsProper
      (D.idealSheaf.subschemeι ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have _ : AlgebraicGeometry.LocallyOfFiniteType
      (D.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    change AlgebraicGeometry.LocallyOfFiniteType
      (D.idealSheaf.subschemeι ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have h4 : AlgebraicGeometry.ChowGroup.degreeOver K C.carrier hC
        (AlgebraicGeometry.chowPushforward D.idealSheaf.subschemeι 0
          (D.toScheme.fundamentalChowClass 0))
      = AlgebraicGeometry.ChowGroup.degreeOver K D.toScheme hDp
          (D.toScheme.fundamentalChowClass 0) :=
    MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hDp hC _ _
  -- step 5: `D.toScheme ≅ Spec κ(c)`
  have hjci : AlgebraicGeometry.IsClosedImmersion (C.carrier.fromSpecResidueField c) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hc
  let _ : (AlgebraicGeometry.Spec (C.carrier.residueField c)).Over
      (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨C.carrier.fromSpecResidueField c ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have hPp : IsProperOver K (AlgebraicGeometry.Spec (C.carrier.residueField c)) := by
    change AlgebraicGeometry.IsProper
      (C.carrier.fromSpecResidueField c ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have _ : AlgebraicGeometry.LocallyOfFiniteType
      ((AlgebraicGeometry.Spec (C.carrier.residueField c)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    change AlgebraicGeometry.LocallyOfFiniteType
      (C.carrier.fromSpecResidueField c ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have hker : D.idealSheaf.subschemeι.ker = (C.carrier.fromSpecResidueField c).ker := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
    exact hD
  let f : AlgebraicGeometry.Spec (C.carrier.residueField c) ⟶ D.toScheme :=
    AlgebraicGeometry.IsClosedImmersion.lift D.idealSheaf.subschemeι
      (C.carrier.fromSpecResidueField c) hker.le
  have _ : IsIso f := AlgebraicGeometry.IsClosedImmersion.isIso_lift _ _ hker
  have hf : f ≫ D.idealSheaf.subschemeι = C.carrier.fromSpecResidueField c :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  let e : AlgebraicGeometry.Spec (C.carrier.residueField c) ≅ D.toScheme := asIso f
  have _ : e.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨by
    show f ≫ (D.idealSheaf.subschemeι ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
      = C.carrier.fromSpecResidueField c ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
    rw [← Category.assoc, hf]⟩
  have h5 : AlgebraicGeometry.ChowGroup.degreeOver K D.toScheme hDp
        (D.toScheme.fundamentalChowClass 0)
      = AlgebraicGeometry.ChowGroup.degreeOver K
          (AlgebraicGeometry.Spec (C.carrier.residueField c)) hPp
          ((AlgebraicGeometry.Spec (C.carrier.residueField c)).fundamentalChowClass 0) := by
    rw [← AlgebraicGeometry.chowPushforward_fundamentalChowClass_of_iso (k := K) e 0]
    exact AlgebraicGeometry.ChowGroup.degreeOver_chowPushforward_of_iso hPp hDp e _
  -- steps 6–7: the degree of the fundamental class of `Spec κ(c)` is `[κ(c) : K] = 1`
  have h6 : AlgebraicGeometry.ChowGroup.degreeOver K
      (AlgebraicGeometry.Spec (C.carrier.residueField c)) hPp
      ((AlgebraicGeometry.Spec (C.carrier.residueField c)).fundamentalChowClass 0) = 1 := by
    change AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      ((AlgebraicGeometry.Spec (C.carrier.residueField c)).fundamentalCycle 0) = 1
    unfold AlgebraicGeometry.AlgebraicCycle.degree
    rw [finsum_unique]
    have hgen : genericPoint (AlgebraicGeometry.Spec (C.carrier.residueField c)) = default :=
      Subsingleton.elim _ _
    have hmult : (AlgebraicGeometry.Spec (C.carrier.residueField c)).fundamentalCycle 0 default
        = 1 := by
      show (if AlgebraicGeometry.Intersection.pointClosureDimension
          (AlgebraicGeometry.Spec (C.carrier.residueField c)) default = ((0 : ℕ) : WithBot ℕ∞)
        then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity
          (AlgebraicGeometry.Spec (C.carrier.residueField c)) default else 0) = 1
      have hd : AlgebraicGeometry.Intersection.pointClosureDimension
          (AlgebraicGeometry.Spec (C.carrier.residueField c)) default = ((0 : ℕ) : WithBot ℕ∞) := by
        rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height]
        have h0 : Order.height (default : AlgebraicGeometry.Spec (C.carrier.residueField c)) = 0 :=
          Order.height_eq_zero.mpr (fun y _ => le_of_eq (Subsingleton.elim _ _))
        rw [h0]
        rfl
      rw [if_pos hd]
      have hmem : genericPoint (AlgebraicGeometry.Spec (C.carrier.residueField c)) ∈
          genericPoints (AlgebraicGeometry.Spec (C.carrier.residueField c)) := by
        rw [genericPoints_eq_singleton]; rfl
      have hlen : AlgebraicGeometry.Intersection.fundamentalMultiplicity
          (AlgebraicGeometry.Spec (C.carrier.residueField c))
          (genericPoint (AlgebraicGeometry.Spec (C.carrier.residueField c))) = 1 := by
        rw [AlgebraicGeometry.Intersection.fundamentalMultiplicity_of_generic _ _ hmem]
        unfold AlgebraicGeometry.Intersection.stalkLength
        let _ : Field ((AlgebraicGeometry.Spec (C.carrier.residueField c)).presheaf.stalk
            (genericPoint (AlgebraicGeometry.Spec (C.carrier.residueField c)))) :=
          inferInstanceAs (Field (AlgebraicGeometry.Spec (C.carrier.residueField c)).functionField)
        exact Module.length_eq_one _ _
      rw [hgen] at hlen
      unfold AlgebraicGeometry.Intersection.integralFundamentalMultiplicity
      simp [hlen]
    have hres : ((AlgebraicGeometry.Spec (C.carrier.residueField c)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree default = 1 := by
      change (C.carrier.fromSpecResidueField c ≫
        (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))).residueDegree default = 1
      rw [← AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree]
      apply AlgebraicGeometry.Intersection.residueFieldDegree_eq_one
      have huniv : ({default} : Set (AlgebraicGeometry.Spec (C.carrier.residueField c))) = Set.univ :=
        Set.eq_univ_of_forall (fun y => Set.mem_singleton_iff.mpr (Subsingleton.elim y default))
      rw [huniv]
      exact isClosed_univ
    rw [hmult, hres]
    simp
  -- assembly
  rw [h1, h2, hdeg, h4, h5, h6]
  norm_num

end
