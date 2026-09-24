import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackSquareVanishes
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PushforwardTautologicalPower
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggGeometry
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor

/-! # Expansion of the top power of the shifted class

Expansion of the top power of the shifted class: `(H+θπ^*P)^{s} = H^{s} + sθ (H^{s-1}·π^*P)`, because the square of
a class pulled back from the curve is zero (§2.4 of the paper, proof of Lemma 2.5).

Route. Write `H + θP = θP + 1·H` and expand with `RatDivisorOp.capPow_add_smul`
(`c₁(π^*O_C(p₀))` and `c₁(B)` commute, `ratDivisorOpOfLineBundle_comm`).
The term with `a` factors of `P` (outermost, `capPow_succ_left`) is
* `a = 0`: `H^s ∩ [Y]`, the top self-intersection of `H`;
* `a = 1`: `s θ · deg(P ∩ H^{s-1} ∩ [Y])`; projection formula + degree/pushforward compatibility turn
  it into `s θ · deg_C(c₁(O_C(p₀)) ∩ π_*(H^{s-1} ∩ [Y]))`, `pushforward_taut_pow_core`
  (`π_*(H^{s-1} ∩ [Y]) = (v/m^{s-1})·[C]`) and `deg(c₁(O_C(p₀)) ∩ [C]) = 1` give `s θ v/m^{s-1}`;
* `a ≥ 2`: zero, `pullback_divisor_mul_cap_degree_eq_zero`.
The fibre class enters only through
`pushforward_taut_pow_core`. The fibre `π_κ^{-1}(p₀)` is integral of dimension `s − 1`
(`YGG.fiber_isIntegral_and_dimension`: it is the weighted projective space `P_{κ(p₀)}(w)`,
`relativeProj_fiber_weightedProjectiveSpace`; `dim Y = (n+1)κ` by `relativeProj_locallyWeighted_krullDim`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `D^{e+1} = D ∘ D^e` with the outermost factor peeled off (`capPow` is defined by peeling
off the innermost one). -/
theorem AlgebraicGeometry.RatDivisorOp.capPow_succ_left {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) (e : ℕ) :
    ∀ (d : ℕ) (z : AlgebraicGeometry.ChowGroupRat X (d + (e + 1))),
      AlgebraicGeometry.RatDivisorOp.capPow D (e + 1) d z
        = D d (AlgebraicGeometry.RatDivisorOp.capPow D e (d + 1)
            (AlgebraicGeometry.ChowGroupRat.congr X (by omega) z)) := by
  induction e with
  | zero =>
      intro d z
      rfl
  | succ e ih =>
      intro d z
      show AlgebraicGeometry.RatDivisorOp.capPow D (e + 1) d (D (d + (e + 1)) z) = _
      rw [ih d (D (d + (e + 1)) z)]
      show D d (AlgebraicGeometry.RatDivisorOp.capPow D e (d + 1) _)
        = D d (AlgebraicGeometry.RatDivisorOp.capPow D e (d + 1) (D (d + 1 + e) _))
      congr 1
      congr 1
      exact (AlgebraicGeometry.ChowGroupRat.congr_apply_ratDivisorOp D (p := d + (e + 1))
        (q := d + 1 + e) (by omega) (by omega) z).symm

/-- A term with at least two factors of a class pulled back from the curve has degree zero
(`pullback_divisor_mul_cap_degree_eq_zero`). -/
theorem shifted_term_degree_eq_zero_of_two_le {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hY : IsProperOver K Y)
    (π : Y ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsProper π]
    (Lc : C.toScheme.Modules) [Lc.IsLineBundle]
    [((AlgebraicGeometry.Scheme.Modules.pullback π).obj Lc).IsLineBundle]
    (θ : ℚ) (a : ℕ) (z : AlgebraicGeometry.ChowGroupRat Y (0 + (a + 2))) :
    AlgebraicGeometry.ChowGroupRat.degree Y hY
        (AlgebraicGeometry.RatDivisorOp.capPow
          (θ • AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Lc)) (a + 2) 0 z) = 0 := by
  have hC : IsProperOver K C.toScheme := C.isProper
  rw [AlgebraicGeometry.RatDivisorOp.capPow_smul, LinearMap.smul_apply, map_smul,
    AlgebraicGeometry.RatDivisorOp.capPow_succ_left,
    AlgebraicGeometry.RatDivisorOp.capPow_succ_left]
  rw [pullback_divisor_mul_cap_degree_eq_zero hY hC π Lc Lc]
  simp

/-- `deg (c₁(O_C(p₀)) ∩ [C]) = 1` for the point divisor `Divisor.ofPoint p₀` of a closed point
(`LineBundle.degree_eq_topSelfIntersection`, `CartierDivisor.lineBundle_degree`,
`Divisor.ofPoint_degree`). -/
theorem SmoothProjectiveCurve.degree_ofPoint_cap_fundamentalClassRat {K : Type u} [Field K]
    [IsAlgClosed K] (C : SmoothProjectiveCurve K) (hC : IsProperOver K C.toScheme)
    (hdimC : C.toScheme.dimension = 1) (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme)) :
    AlgebraicGeometry.ChowGroupRat.degree C.toScheme hC
        (AlgebraicGeometry.ratDivisorOpOfLineBundle (Divisor.ofPoint p₀).lineBundle.toModules 0
          (AlgebraicGeometry.fundamentalClassRat C.toScheme 1 hdimC)) = 1 := by
  have h1 := AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle C.toScheme hC
    (Divisor.ofPoint p₀).lineBundle.toModules 1 hdimC
  unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection at h1
  have h2 : AlgebraicGeometry.RatDivisorOp.capPow
      (AlgebraicGeometry.ratDivisorOpOfLineBundle (Divisor.ofPoint p₀).lineBundle.toModules) 1 0
        ((zero_add 1).symm ▸ AlgebraicGeometry.fundamentalClassRat C.toScheme 1 hdimC)
      = AlgebraicGeometry.ratDivisorOpOfLineBundle (Divisor.ofPoint p₀).lineBundle.toModules 0
          (AlgebraicGeometry.fundamentalClassRat C.toScheme 1 hdimC) := rfl
  rw [h2] at h1
  rw [h1, ← LineBundle.degree_eq_topSelfIntersection C hC (Divisor.ofPoint p₀).lineBundle,
    CartierDivisor.lineBundle_degree C (Divisor.ofPoint p₀), Divisor.ofPoint_degree p₀ hp₀]
  simp

/-- `P_k(w)` on an empty set of variables is empty: `k[∅] = k` sits in degree `0`, so the
irrelevant ideal is `0`, which is contained in every homogeneous prime. -/
theorem weightedProjectiveSpace_isEmpty_of_isEmpty (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    [IsEmpty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    IsEmpty (weightedProjectiveSpace k w hw) := by
  let _ : GradedRing (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
      (fun i : σ => (⟨w i, hw i⟩ : ℕ+))) :=
    MvPolynomial.weightedGradedAlgebra (R := k) (w := fun i : σ => w i)
  refine ⟨fun x => ?_⟩
  change AlgebraicGeometry.Proj (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
    (fun i : σ => (⟨w i, hw i⟩ : ℕ+))) at x
  apply x.not_irrelevant_le
  intro a ha
  have hmem : a ∈ MiyaokaMori.WeightedJets.weightedPolynomialGrading k
      (fun i : σ => (⟨w i, hw i⟩ : ℕ+)) 0 := by
    rw [MvPolynomial.eq_C_of_isEmpty a]
    exact MvPolynomial.isWeightedHomogeneous_C _ _
  have h0 : a = 0 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same _ hmem] at ha
    exact ha
  rw [h0]
  exact zero_mem _

/-- `κ ≥ 1` when `Y_κ^GG` is integral (nonempty): for `κ = 0` every fibre of `π_0` is the weighted
projective space on the empty set `Fin (n+1) × Fin 0` of variables, which is empty. -/
theorem YGG.one_le_of_isIntegral {K : Type u} [Field K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    [AlgebraicGeometry.IsIntegral (YGG f κ)] : 1 ≤ κ := by
  by_contra hκ
  have hκ0 : κ = 0 := by omega
  subst hκ0
  obtain ⟨n, hn⟩ : ∃ n, X.toVariety.dim = n := ⟨_, rfl⟩
  let σ := ULift.{u} (Fin (n + 1) × Fin 0)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  have hS : (jetAlgebra f 0).IsLocallyWeightedPolynomial w hw :=
    YGG.jetAlgebra_isLocallyWeightedPolynomial f hn 0
  haveI : IsEmpty σ := ⟨fun i => i.down.2.elim0⟩
  obtain ⟨y⟩ : Nonempty (YGG f 0) := inferInstance
  let c : C.toScheme := (YGG.proj f 0) y
  obtain ⟨e, -, -⟩ := relativeProj_fiber_weightedProjectiveSpace (jetAlgebra f 0) w hw hS c
  have e' : (YGG.proj f 0).fiber c ≅ weightedProjectiveSpace (C.toScheme.residueField c) w hw := e
  have hy : y ∈ Set.range ((YGG.proj f 0).fiberι c) := by
    rw [AlgebraicGeometry.Scheme.Hom.range_fiberι]
    exact rfl
  obtain ⟨z, -⟩ := hy
  exact (weightedProjectiveSpace_isEmpty_of_isEmpty _ w hw).false (e'.hom.base z)

/-- The fibre of `π_κ : Y_κ^GG → C` over any point is integral of dimension `dim Y − 1`
(it is the weighted projective space `P_{κ(p)}(w)`). -/
theorem YGG.fiber_isIntegral_and_dimension {K : Type u} [Field K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    [AlgebraicGeometry.IsIntegral (YGG f κ)] (s : ℕ) (hs : (YGG f κ).dimension = s)
    (p : C.toScheme) :
    AlgebraicGeometry.IsIntegral ((YGG.proj f κ).fiber p) ∧
      ((YGG.proj f κ).fiber p).dimension = s - 1 := by
  have hκ : 1 ≤ κ := YGG.one_le_of_isIntegral f κ
  obtain ⟨n, hn⟩ : ∃ n, X.toVariety.dim = n := ⟨_, rfl⟩
  let σ := ULift.{u} (Fin (n + 1) × Fin κ)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  have hS : (jetAlgebra f κ).IsLocallyWeightedPolynomial w hw :=
    YGG.jetAlgebra_isLocallyWeightedPolynomial f hn κ
  haveI : Nonempty σ := ⟨⟨(0, ⟨0, hκ⟩)⟩⟩
  have hcard : Fintype.card σ = (n + 1) * κ := by
    simp [σ, Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin]
  have hprod : 1 ≤ (n + 1) * κ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero n) (Nat.ne_of_gt hκ))
  -- dim Y = (n+1)κ
  haveI : AlgebraicGeometry.IsProper (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper
  have hkr := relativeProj_locallyWeighted_krullDim
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) (jetAlgebra f κ) w hw hS
  have hYdim : (YGG f κ).dimension = (n + 1) * κ := by
    have hkr' : topologicalKrullDim (YGG f κ) =
        topologicalKrullDim C.toScheme + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞) := hkr
    unfold AlgebraicGeometry.Scheme.dimension
    rw [hkr', C.dim_one, hcard]
    have hNat : 1 + ((n + 1) * κ - 1) = (n + 1) * κ := by omega
    have hCast : (1 : WithBot ℕ∞) + (((n + 1) * κ - 1 : ℕ) : WithBot ℕ∞) =
        (((n + 1) * κ : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hNat
    rw [hCast]
    change (((n + 1) * κ : ℕ) : ℕ∞).toNat = (n + 1) * κ
    simp
  have hsval : s = (n + 1) * κ := hs.symm.trans hYdim
  -- the fibre is P_{κ(p)}(w)
  obtain ⟨e, -, -⟩ := relativeProj_fiber_weightedProjectiveSpace (jetAlgebra f κ) w hw hS p
  have e' : (YGG.proj f κ).fiber p ≅ weightedProjectiveSpace (C.toScheme.residueField p) w hw := e
  haveI := weightedProjectiveSpace.isIntegral (C.toScheme.residueField p) w hw
  haveI : Nonempty ((YGG.proj f κ).fiber p) := ⟨e'.inv.base (Classical.arbitrary _)⟩
  refine ⟨AlgebraicGeometry.isIntegral_of_isOpenImmersion e'.hom, ?_⟩
  unfold AlgebraicGeometry.Scheme.dimension
  rw [IsHomeomorph.topologicalKrullDim_eq _ (AlgebraicGeometry.Scheme.homeoOfIso e').isHomeomorph,
    weightedProjectiveSpace_dimension _ w hw, hcard, hsval]
  exact ENat.toNat_natCast _

/-- The finite sum appearing in the binomial expansion: only the terms with `s − j ∈ {0, 1}` survive. -/
theorem shifted_sum_eval (s : ℕ) (TS W : ℚ) :
    ∑ j ∈ Finset.range (s + 1),
        (s.choose j : ℚ) • (if s - j = 0 then TS else if s - j = 1 then W else 0)
      = TS + (s : ℚ) * W := by
  match s with
  | 0 => simp
  | e + 1 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero (fun j hj => by
        have hj' : j < e := Finset.mem_range.mp hj
        rw [if_neg (by omega), if_neg (by omega), smul_zero])]
      rw [Nat.sub_self, Nat.add_sub_cancel_left, if_pos rfl, if_neg one_ne_zero, if_pos rfl,
        Nat.choose_self, Nat.choose_succ_self_right]
      push_cast
      ring

/-- General form of the expansion: `Y` integral and proper over `K`, `π : Y → C` proper,
`dim Y = s`, the fibre over the closed point `p₀` integral of dimension `s − 1`, `H = c₁(Lm)/m`,
`P = c₁(π^*O_C(p₀))`. Then `(H + θP)^s = H^s + s θ v/m^{s-1}` with `v` the fibre degree of `Lm`. -/
theorem topSelfIntersection_add_smul_pullback_point {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsIntegral Y]
    (hY : IsProperOver K Y)
    (π : Y ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsProper π]
    (Lm : Y.Modules) [Lm.IsLineBundle] (m : ℕ)
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme)) (θ : ℚ)
    (s : ℕ) (hs : Y.dimension = s)
    (h₁ : letI := π.fiberOverSpecResidueField p₀;
      IsProperOver (C.toScheme.residueField p₀) (π.fiber p₀))
    [AlgebraicGeometry.IsIntegral (π.fiber p₀)] (hfib : (π.fiber p₀).dimension = s - 1) :
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
        ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle Lm
          + θ • AlgebraicGeometry.ratDivisorOpOfLineBundle
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
                (Divisor.ofPoint p₀).lineBundle.toModules)) s hs
      = AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
          ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle Lm) s hs
        + (s : ℚ) * θ * ((AlgebraicGeometry.relativePolarizationFiberDegree π Lm p₀ h₁ : ℚ)
            / (m : ℚ) ^ (s - 1)) := by
  have hC : IsProperOver K C.toScheme := C.isProper
  have hdimC : C.toScheme.dimension = 1 := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [C.dim_one]
    simp
  haveI : AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hY
  haveI : AlgebraicGeometry.IsProper (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hC
  -- notation
  set Lc : C.toScheme.Modules := (Divisor.ofPoint p₀).lineBundle.toModules with hLc
  set G : AlgebraicGeometry.RatDivisorOp Y := AlgebraicGeometry.ratDivisorOpOfLineBundle Lm with hG
  set P : AlgebraicGeometry.RatDivisorOp Y := AlgebraicGeometry.ratDivisorOpOfLineBundle
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Lc) with hP
  set Hm : AlgebraicGeometry.RatDivisorOp Y := (m : ℚ)⁻¹ • G with hHm
  set D₀ : AlgebraicGeometry.RatDivisorOp C.toScheme :=
    AlgebraicGeometry.ratDivisorOpOfLineBundle Lc with hD₀
  set α₀ : AlgebraicGeometry.ChowGroupRat Y (0 + s) :=
    AlgebraicGeometry.ChowGroupRat.congr Y (zero_add s).symm
      (AlgebraicGeometry.fundamentalClassRat Y s hs) with hα₀
  set v : ℚ := (AlgebraicGeometry.relativePolarizationFiberDegree π Lm p₀ h₁ : ℚ) with hv
  -- commutation of θP and Hm
  have hcomm : ∀ d, ((θ • P) d).comp (Hm (d + 1)) = (Hm d).comp ((θ • P) (d + 1)) := by
    intro d
    have h := AlgebraicGeometry.ratDivisorOpOfLineBundle_comm (k := K)
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Lc) Lm d
    show (θ • P d).comp ((m : ℚ)⁻¹ • G (d + 1)) = ((m : ℚ)⁻¹ • G d).comp (θ • P (d + 1))
    rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      smul_comm]
    rw [hP, hG, h]
  -- the individual terms of the binomial expansion
  have hterm : ∀ (a b : ℕ) (h : 0 + s = 0 + a + b),
      AlgebraicGeometry.ChowGroupRat.degree Y hY
          (AlgebraicGeometry.RatDivisorOp.capPow (θ • P) a 0
            (AlgebraicGeometry.RatDivisorOp.capPow Hm b (0 + a)
              (AlgebraicGeometry.ChowGroupRat.congr Y h α₀)))
        = if a = 0 then
            AlgebraicGeometry.ChowGroupRat.degree Y hY
              (AlgebraicGeometry.RatDivisorOp.capPow Hm s 0 α₀)
          else if a = 1 then θ * (v / (m : ℚ) ^ (s - 1)) else 0 := by
    intro a b h
    match a with
    | 0 =>
        obtain rfl : b = s := by omega
        rw [if_pos rfl]
        rfl
    | 1 =>
        rw [if_neg one_ne_zero, if_pos rfl]
        have hsb : s = b + 1 := by omega
        subst hsb
        show AlgebraicGeometry.ChowGroupRat.degree Y hY
          (θ • P 0 (AlgebraicGeometry.RatDivisorOp.capPow Hm b 1
            (AlgebraicGeometry.ChowGroupRat.congr Y h α₀))) = _
        rw [map_smul]
        have hα : AlgebraicGeometry.ChowGroupRat.congr Y h α₀
            = AlgebraicGeometry.fundamentalClassRat Y (1 + b) (by omega) := by
          rw [hα₀, AlgebraicGeometry.ChowGroupRat.congr_congr,
            AlgebraicGeometry.ChowGroupRat.congr_fundamentalClassRat _ hs (by omega)]
        rw [hα]
        set β : AlgebraicGeometry.ChowGroupRat Y 1 :=
          AlgebraicGeometry.RatDivisorOp.capPow Hm b 1
            (AlgebraicGeometry.fundamentalClassRat Y (1 + b) (by omega)) with hβ
        have hcore := pushforward_taut_pow_core π Lm m (b + 1) (by omega) hs p₀ hp₀ h₁
          (by simpa using hfib) hdimC
        rw [AlgebraicGeometry.ChowGroupRat.congr_fundamentalClassRat _ hs
          (by omega : Y.dimension = 1 + (b + 1 - 1))] at hcore
        have hcore' : AlgebraicGeometry.chowPushforwardRat π 1 β
            = (v / (m : ℚ) ^ b) • AlgebraicGeometry.fundamentalClassRat C.toScheme 1 hdimC :=
          hcore
        rw [← AlgebraicGeometry.ChowGroupRat.degree_chowPushforwardRat hY hC π (P 0 β),
          hP, AlgebraicGeometry.chowPushforwardRat_ratDivisorOpOfLineBundle_pullback (k := K) π Lc 0 β,
          hcore', map_smul, map_smul,
          SmoothProjectiveCurve.degree_ofPoint_cap_fundamentalClassRat C hC hdimC p₀ hp₀]
        simp only [smul_eq_mul, mul_one, Nat.add_sub_cancel]
    | a + 2 =>
        rw [if_neg (by omega : a + 2 ≠ 0), if_neg (by omega : a + 2 ≠ 1)]
        exact shifted_term_degree_eq_zero_of_two_le hY π Lc θ a _
  -- expand
  rw [← AlgebraicGeometry.ChowGroupRat.degree_capPow_congr_fundamentalClassRat Y hY _ s hs,
    ← AlgebraicGeometry.ChowGroupRat.degree_capPow_congr_fundamentalClassRat Y hY Hm s hs,
    ← hα₀]
  have hsum : Hm + θ • P = θ • P + (1 : ℚ) • Hm := by rw [one_smul, add_comm]
  rw [hsum, AlgebraicGeometry.RatDivisorOp.capPow_add_smul (θ • P) Hm hcomm 1 s 0,
    LinearMap.coe_sum, Finset.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, one_pow, mul_one]
  simp only [hterm]
  -- evaluate the finite sum
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (s.choose j : ℚ) •
    (if s - j = 0 then AlgebraicGeometry.ChowGroupRat.degree Y hY
        (AlgebraicGeometry.RatDivisorOp.capPow Hm s 0 α₀)
      else if s - j = 1 then θ * (v / (m : ℚ) ^ (s - 1)) else 0)) (s + 1),
    shifted_sum_eval]
  ring

theorem topSelfIntersection_shift {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hm : 0 < m)
    [AlgebraicGeometry.IsIntegral (YGG f κ)]
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme)) (θ : ℚ)
    (hY : IsProperOver K (YGG f κ)) (s : ℕ) (hs : (YGG f κ).dimension = s)
    (hfib : letI := (YGG.proj f κ).fiberOverSpecResidueField p₀;
      IsProperOver (C.toScheme.residueField p₀) ((YGG.proj f κ).fiber p₀)) :
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY
        (tautClass f κ m + θ • ratPullbackOp (YGG.proj f κ) (Divisor.ofPoint p₀)) s hs
      = AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY (tautClass f κ m) s hs
        + (s : ℚ) * θ * ((AlgebraicGeometry.relativePolarizationFiberDegree (YGG.proj f κ)
            (polarization f κ m) p₀ hfib : ℚ) / (m : ℚ) ^ (s - 1)) := by
  haveI : AlgebraicGeometry.IsProper (YGG.proj f κ) := YGG.proj_isProper f rfl κ
  haveI : (YGG.proj f κ).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  obtain ⟨hint, hdim⟩ := YGG.fiber_isIntegral_and_dimension f κ s hs p₀
  haveI := hint
  unfold tautClass ratPullbackOp
  exact topSelfIntersection_add_smul_pullback_point hY (YGG.proj f κ) (polarization f κ m) m p₀ hp₀
    θ s hs hfib hdim

end
