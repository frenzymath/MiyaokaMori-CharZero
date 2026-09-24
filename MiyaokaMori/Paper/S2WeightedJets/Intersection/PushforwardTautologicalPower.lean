import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpOfCycleClass
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupTopDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PushforwardTautologicalPowerAlgebra
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.PushforwardTautologicalPowerFiberClass
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PushforwardTautologicalPowerFiberTopIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PushforwardTautologicalPowerPointDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.PushforwardTautologicalPowerPointDivisor
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PushforwardTautologicalPowerSplitFiber
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitTautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatCapPowBinomial

/-! # Pushforward of a power of the tautological class

`π_sp` pushes `H^{s_k−1} ∩ [Y^sp]` forward to `v · [C]`, where `v = (top self-intersection of O(m) on a fiber)/m^{s_k−1}`
is the fiber degree at a closed point `c`: `CH_1(C)_ℚ = ℚ[C]`, and the coefficient is measured with the point
divisor at `c` (Proposition 2.4 of the paper; the fiber degree `v_k`, eq. (2.6)).

The top-level statement is assembled from `PushforwardTautologicalPowerAlgebra` (the algebraic part) and the
geometric modules `PushforwardTautologicalPower{PointDivisor,PointDegree,FiberClass,FiberTopIntersection,SplitFiber}`:
`pushforward_taut_pow_core` is the general form for an arbitrary integral scheme `Y` and line bundle `Lm`
(`H = c_1(Lm)/m`), and the target theorem substitutes `H^sp = c_1(O(m))/m` (`splitTautologicalClass_eq_of_dvd`) and
the facts about the fibers of `Y^sp` (`splitWeightedProjectivization_fiber_isIntegral_and_dimension`).
-/


set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/-- General form: `Y` integral, `π : Y → C` proper, `dim Y = s ≥ 1`, the fiber `Y_c` over a closed point `c`
integral with `dim Y_c = s − 1`, `Lm` a line bundle and `H := c_1(Lm)/m`. Then
`π_*(H^{s−1} ∩ [Y]) = (v / m^{s−1}) · [C]`, where `v = (Lm|_{Y_c})^{s−1}` is the fiber degree at `c`.

Proof: `CH_1(C)_ℚ = ℚ[C]` (`exists_eq_smul_fundamentalClassRat`), and the coefficient is measured with the point
divisor `O_C(c)`: `deg(c_1(O_C(c)) ∩ [C]) = 1`; the projection formula and the compatibility of degree with
pushforward turn `deg(c_1(O_C(c)) ∩ π_*β)` into `deg(c_1(π^*O_C(c)) ∩ β)`; `c_1(π^*O_C(c))` commutes with
`H^{s−1}`; `c_1(π^*O_C(c)) ∩ [Y] = ι_*[Y_c]`; finally use the projection formula for `ι` and
`(c_1/m)^{s−1} = c_1^{s−1}/m^{s−1}`. -/
theorem pushforward_taut_pow_core {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Y]
    (π : Y ⟶ C.carrier) [AlgebraicGeometry.IsProper π] (Lm : Y.Modules) [Lm.IsLineBundle]
    (m : ℕ) (s : ℕ) (hs : 1 ≤ s) (hdim : Y.dimension = s)
    (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier))
    (h₁ : letI := π.fiberOverSpecResidueField c;
      IsProperOver (C.carrier.residueField c) (π.fiber c))
    [AlgebraicGeometry.IsIntegral (π.fiber c)] (hfib : (π.fiber c).dimension = s - 1)
    (hdimC : C.carrier.dimension = 1) :
    AlgebraicGeometry.chowPushforwardRat π 1
        (AlgebraicGeometry.RatDivisorOp.capPow
          ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle Lm) (s - 1) 1
          (AlgebraicGeometry.ChowGroupRat.congr Y (by omega : s = 1 + (s - 1))
            (AlgebraicGeometry.fundamentalClassRat Y s hdim)))
      = ((AlgebraicGeometry.relativePolarizationFiberDegree π Lm c h₁ : ℚ) / (m : ℚ) ^ (s - 1))
          • AlgebraicGeometry.fundamentalClassRat C.carrier 1 hdimC := by
  obtain ⟨e, rfl⟩ : ∃ e, s = e + 1 := ⟨s - 1, by omega⟩
  -- `Over` structures: `Y` and `Y_c` as `K`-schemes via `C`
  let _ : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have _ : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hC : IsProperOver K C.carrier := C.isProper
  have hY : IsProperOver K Y := by
    change AlgebraicGeometry.IsProper (π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  have hfin : topologicalKrullDim C.carrier ≠ ⊤ := by
    rw [show topologicalKrullDim C.carrier = 1 from C.dim_one]
    exact fun h => ENat.one_ne_top (WithBot.coe_eq_coe.mp h)
  have hι : AlgebraicGeometry.IsProper (π.fiberι c) :=
    AlgebraicGeometry.isProper_fiberι_of_isClosed π c hc
  let _ : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have _ : (π.fiberι c).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hfibK : IsProperOver K (π.fiber c) := by
    change AlgebraicGeometry.IsProper
      (π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    infer_instance
  -- the point divisor
  obtain ⟨D, hD⟩ := SmoothProjectiveCurve.exists_effectiveCartierDivisor_point C c hc
  -- notation
  set G : AlgebraicGeometry.RatDivisorOp Y := AlgebraicGeometry.ratDivisorOpOfLineBundle Lm with hG
  set DY : AlgebraicGeometry.RatDivisorOp Y :=
    AlgebraicGeometry.ratDivisorOpOfLineBundle
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj D.lineBundle) with hDY
  set D₀ : AlgebraicGeometry.RatDivisorOp C.carrier :=
    AlgebraicGeometry.ratDivisorOpOfLineBundle D.lineBundle with hD₀
  set z : AlgebraicGeometry.ChowGroupRat Y (1 + e) :=
    AlgebraicGeometry.ChowGroupRat.congr Y (by omega : e + 1 = 1 + e)
      (AlgebraicGeometry.fundamentalClassRat Y (e + 1) hdim) with hz
  set β : AlgebraicGeometry.ChowGroupRat Y 1 :=
    AlgebraicGeometry.RatDivisorOp.capPow ((m : ℚ)⁻¹ • G) e 1 z with hβ
  have hcomm : ∀ d, (DY d).comp (((m : ℚ)⁻¹ • G) (d + 1)) = (((m : ℚ)⁻¹ • G) d).comp (DY (d + 1)) := by
    intro d
    show (DY d).comp ((m : ℚ)⁻¹ • G (d + 1)) = ((m : ℚ)⁻¹ • G d).comp (DY (d + 1))
    rw [LinearMap.comp_smul, LinearMap.smul_comp, hG, hDY,
      AlgebraicGeometry.ratDivisorOpOfLineBundle_comm (k := K)]
  -- π_*β = r • [C]
  obtain ⟨r, hr⟩ := AlgebraicGeometry.ChowGroupRat.exists_eq_smul_fundamentalClassRat
    (X := C.carrier) 1 hdimC hfin (AlgebraicGeometry.chowPushforwardRat π 1 β)
  show AlgebraicGeometry.chowPushforwardRat π 1 β = _
  rw [hr]
  congr 1
  -- `r` is measured by the point divisor
  have h1 : AlgebraicGeometry.ChowGroupRat.degree C.carrier hC
      (D₀ 0 (AlgebraicGeometry.chowPushforwardRat π 1 β)) = r := by
    rw [hr, map_smul, map_smul, hD₀,
      SmoothProjectiveCurve.degree_pointDivisor_cap_fundamentalClassRat C hC hdimC c hc D hD,
      smul_eq_mul, mul_one]
  rw [← h1]
  -- projection formula and compatibility of degree with pushforward
  have h2 : D₀ 0 (AlgebraicGeometry.chowPushforwardRat π 1 β)
      = AlgebraicGeometry.chowPushforwardRat π 0 (DY 0 β) :=
    (AlgebraicGeometry.chowPushforwardRat_ratDivisorOpOfLineBundle_pullback (k := K) π D.lineBundle 0 β).symm
  rw [h2, AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat hY hC π]
  -- commute `c_1(π^*O_C(c))` with `H^e`
  have h3 : DY 0 β = AlgebraicGeometry.RatDivisorOp.capPow ((m : ℚ)⁻¹ • G) e 0
      (DY (0 + e) (AlgebraicGeometry.ChowGroupRat.congr Y (by omega) z)) :=
    AlgebraicGeometry.RatDivisorOp.comp_capPow_of_comm DY ((m : ℚ)⁻¹ • G) hcomm e 0 z
  -- c_1(π^*O_C(c)) ∩ [Y] = ι_*[Y_c]
  have hdim' : Y.dimension = 0 + e + 1 := by omega
  have hfib' : (π.fiber c).dimension = 0 + e := by omega
  have h4 : DY (0 + e) (AlgebraicGeometry.ChowGroupRat.congr Y (by omega) z)
      = AlgebraicGeometry.chowPushforwardRat (π.fiberι c) (0 + e)
          (AlgebraicGeometry.fundamentalClassRat (π.fiber c) (0 + e) hfib') := by
    rw [hz, AlgebraicGeometry.ChowGroupRat.congr_congr,
      AlgebraicGeometry.ChowGroupRat.congr_fundamentalClassRat _ hdim hdim', hDY]
    exact AlgebraicGeometry.ratDivisorOpOfLineBundle_pullback_pointDivisor_fundamentalClassRat
      π c hc D hD (0 + e) hdim' hfib'
  rw [h3, h4, AlgebraicGeometry.RatDivisorOp.capPow_smul, LinearMap.smul_apply, map_smul,
    ← AlgebraicGeometry.chowPushforwardRat_capPow_pullback (k := K) (π.fiberι c) Lm e 0,
    AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat hfibK hY (π.fiberι c),
    ← AlgebraicGeometry.ChowGroupRat.congr_fundamentalClassRat (zero_add e).symm hfib hfib',
    AlgebraicGeometry.degree_capPow_pullback_fiberι_eq_relativePolarizationFiberDegree
      π c hc Lm e hfib h₁ hfibK]
  rw [smul_eq_mul, inv_pow, div_eq_inv_mul]
  rfl

theorem pushforward_taut_pow_eq_fiberDegree {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} (hkk : 1 ≤ kk) {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    [AlgebraicGeometry.IsIntegral (splitWeightedProjectivization F kk).left]
    [AlgebraicGeometry.IsProper (splitWeightedProjectivization F kk).hom]
    [SheafOfModules.IsLineBundle
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ))]
    (hdim : (splitWeightedProjectivization F kk).left.dimension = (n + 1) * kk)
    (c : C.carrier) (hc : IsClosed {c})
    (h₁ : letI := (splitWeightedProjectivization F kk).hom.fiberOverSpecResidueField c;
      IsProperOver (C.carrier.residueField c) ((splitWeightedProjectivization F kk).hom.fiber c)) :
    AlgebraicGeometry.chowPushforwardRat (splitWeightedProjectivization F kk).hom 1
        (AlgebraicGeometry.RatDivisorOp.capPow
          (ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm))
          ((n + 1) * kk - 1) 1
          (AlgebraicGeometry.ChowGroupRat.congr (splitWeightedProjectivization F kk).left
            (by have : 1 ≤ (n + 1) * kk := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero n) (by omega)); omega :
              (n + 1) * kk = 1 + ((n + 1) * kk - 1))
            (AlgebraicGeometry.fundamentalClassRat
              (splitWeightedProjectivization F kk).left ((n + 1) * kk) hdim)))
      = ((AlgebraicGeometry.relativePolarizationFiberDegree (splitWeightedProjectivization F kk).hom
            (AlgebraicGeometry.Scheme.relativeProj.twist
              (splitWeightedAlgebraOf F kk) (m : ℤ)) c h₁ : ℚ)
          / (m : ℚ) ^ ((n + 1) * kk - 1))
          • AlgebraicGeometry.fundamentalClassRat C.carrier 1
            (by simp [AlgebraicGeometry.Scheme.dimension,
              show topologicalKrullDim C.carrier = 1 from C.dim_one])  := by
  have hs : 1 ≤ (n + 1) * kk :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero n) (by omega))
  obtain ⟨hfibInt, hfibDim⟩ :=
    splitWeightedProjectivization_fiber_isIntegral_and_dimension hkk F c
  have hH : ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm)
      = (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)) := by
    funext d
    exact splitTautologicalClass_eq_of_dvd F kk m hm hdiv (d + 1)
  rw [hH]
  exact pushforward_taut_pow_core (splitWeightedProjectivization F kk).hom
    (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)) m
    ((n + 1) * kk) hs hdim c hc h₁ hfibDim _

end
