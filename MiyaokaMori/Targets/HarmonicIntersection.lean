import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothRelativeDimensionOfDim
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjProperLocal
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConePunctured
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeRankDegree
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatePowerSection
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationNonlinear
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationToSplit
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeAdditiveFiltration
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharConstant
import MiyaokaMori.Paper.S2WeightedJets.Intersection.ExpandWeightedRelation
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FiberDegreePositive
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FiberDegreeExplicit
import MiyaokaMori.AlgebraicGeometry.Modules.FiltrationLineQuotients
import MiyaokaMori.Paper.S2WeightedJets.Ygg.FlatFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Charts.GradedPieceLocallyFree
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGradingNonnegative
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinates
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetTransition
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetWeightOfOrderQ
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.LocallyIntegralConnectedIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.Paper.S2WeightedJets.Intersection.PullbackClassDegree
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackSquareVanishes
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.RationalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjLocallyWeightedDimension
import MiyaokaMori.AlgebraicGeometry.Modules.RelativelyVeryAmple
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.SectionClosedImmersion
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionEquationsVanish
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperIntersectionEqChow
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitFiberDegree
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitTautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedCoordinate
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.Paper.S2WeightedJets.Cone.TangentSequence
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopIntersectionDeformationInvariant
import MiyaokaMori.Paper.S2WeightedJets.Intersection.TopIntersectionEquality
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.TopIntersectionFromEuler
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGeneration
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGenerationMultiple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.VeronesePolarizationVeryAmple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjNormal
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceIntegral
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiber
import MiyaokaMori.Paper.S2WeightedJets.Intersection.WeightedRelation
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatCapPowBinomial
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # The weighted intersection number

**Proposition 2.4** of the paper** (§2, "The weighted intersection"), together with the
supporting properties of `Y_k^GG` and `B_k` from Lemma 2.2 and the
surrounding text.

For the twisted affine cone `Z` of the paper and its seed section `s` (built from the embedding `e`,
the homogeneous equations `E` and the homogeneous coordinates `coord` of `f`), the weighted
projectivization `Y_k^GG = Proj_C 𝒮` is integral, normal and projective over `C`, of dimension
`s_k = (n+1)k`. For `m` a positive multiple of `s_k · w_k` the twist `B_k = O(m)` is invertible and
relatively very ample; for a closed point `c` the fiber degree
`v_k = (B_k|_{π^{-1}(c)})^{s_k−1} / m^{s_k−1}` is positive and equals `1/(k!)^{n+1}` ((2.6) of the paper), and the top self-intersection is

  `H_k^{s_k} = (B_k^{s_k}) / m^{s_k} = −v_k · d · h_k = −d/(k!)^{n+1} · Σ_{q=1}^k 1/q`.

The theorem `harmonic_intersection` states all of these at once. Here `H_k = (1/m) c_1(B_k)`, so
`v_k = relativePolarizationFiberDegree / m^{(n+1)k-1}`; the explicit value of `v_k` comes from
`fiberDegree_div_pow_eq` (`Paper/S2WeightedJets/Ygg/FiberDegreeExplicit.lean`, the paper's power-map
computation `(deg φ_k) v_k = 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem harmonic_proper_relativeProj_of_localProduct
    {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}}
    (pX : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsProper pX]
    (S : X.GradedQCAlgebra)
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) :
    AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.relativeProj S).hom := by
  obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u} pX S w hw hS
  letI : AlgebraicGeometry.IsProper
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    unfold weightedProjectiveSpace
    exact MiyaokaMori.WeightedJets.local_weightedProjToSpec_isProper
      (R := k) (ι := σ) (w := fun i => (⟨w i, hw i⟩ : ℕ+))
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
    (P := @AlgebraicGeometry.IsProper) 𝒰]
  intro i
  obtain ⟨φ, hφ, _⟩ := h𝒰 i
  change AlgebraicGeometry.IsProper
    (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.relativeProj S).hom
      (𝒰.f i))
  rw [← hφ]
  infer_instance

private lemma harmonic_line_rank_local {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (i : Fin (n + 1)) (x : C.toScheme) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (F.lineQuotient i).toModules x = 1 := by
  exact ((F.lineQuotient i).rankAtStalk_eq x).trans (F.lineQuotient i).rank_eq_one

private lemma harmonic_biproduct_rank {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) :
    ∀ x : C.toScheme,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (CategoryTheory.Limits.biproduct
          (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)) x = n + 1 := by
  intro x
  let Q : Fin (n + 1) → C.toScheme.Modules :=
    fun i => (F.lineQuotient i).toModules
  have hQlf : ∀ i, (Q i).IsLocallyFree := fun i => (F.lineQuotient i).locallyFree
  have hQft : ∀ i, (Q i).IsFiniteType := fun i => (F.lineQuotient i).isFiniteType
  let P : Fin (n + 1) → C.toScheme.Opens → Prop := fun i U =>
    ∃ I : Type u, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
  have hmono : ∀ (i : Fin (n + 1)) (V U : C.toScheme.Opens), V ≤ U → P i U → P i V := by
    intro i V U hVU h
    obtain ⟨I, ⟨e⟩⟩ := h
    exact ⟨I, AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le (Q i) hVU I e⟩
  have hex : ∀ i, ∃ U : C.toScheme.Opens, x ∈ U ∧ P i U := by
    intro i
    obtain ⟨U, I, hxU, e⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree (Q i) x
    exact ⟨U, hxU, I, e⟩
  obtain ⟨U, hxU, hU⟩ := AlgebraicGeometry.Scheme.Modules.exists_common_open x P hmono hex
  choose I hI using hU
  have hfin : ∀ i, Finite (I i) := by
    intro i
    exact AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free
      (Q i) U (I i) (hI i).some x hxU
  letI : ∀ i, Fintype (I i) := fun i => Fintype.ofFinite (I i)
  have eB : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      (CategoryTheory.Limits.biproduct Q) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Sigma I) := by
    let e0 : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        (CategoryTheory.Limits.biproduct Q) ≅
        CategoryTheory.Limits.biproduct (fun i =>
          (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i)) :=
      (AlgebraicGeometry.Scheme.Modules.pullback U.ι).mapBiproduct Q
    exact e0 ≪≫
      (AlgebraicGeometry.Scheme.Modules.biproduct_iso_free
        (fun i => (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (Q i)) I
        (fun i => (hI i).some)).some
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
    (CategoryTheory.Limits.biproduct Q) U (Sigma I) eB x hxU]
  have hcard : ∀ i, Fintype.card (I i) = 1 := by
    intro i
    rw [← harmonic_line_rank_local F i x]
    exact (AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
      (Q i) U (I i) (hI i).some x hxU).symm
  simp [Fintype.card_sigma, hcard]

private lemma harmonic_cycle_class_op_eq {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {a r m : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E a) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 r, q ∣ m)
    [LIs : (AlgebraicGeometry.Scheme.relativeProj.twist
      (splitWeightedAlgebraOf F r) (m : ℤ)).IsLineBundle] :
    ratDivisorOpOfCycleClass (splitTautologicalClass F r m hm) =
      (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F r) (m : ℤ)) := by
  funext d
  simp only [ratDivisorOpOfCycleClass, splitTautologicalClass_eq_of_dvd F r m hm hdiv]
  rfl

private lemma harmonic_rational_top_scaled_line {K : Type u} [Field K]
    (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Y] (hY : IsProperOver K Y)
    (L : Y.Modules) [L.IsLineBundle] (m s : ℕ) (hs : Y.dimension = s) :
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
        ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs =
      (AlgebraicGeometry.topSelfIntersection Y hY L : ℚ) / (m : ℚ) ^ s := by
  have hscale :
      AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
          ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs =
        ((m : ℚ)⁻¹) ^ s *
          AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
            (AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs := by
    unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection
    rw [AlgebraicGeometry.RatDivisorOp.capPow_smul]
    exact (AlgebraicGeometry.ChowGroupRat.degree Y hY).map_smul _ _
  rw [hscale,
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle Y hY L s hs]
  rw [inv_pow]
  exact inv_mul_eq_div _ _

/-- **The weighted intersection number** (Proposition 2.4 of the paper, with the
supporting properties of `Y_k^GG` and `B_k`): `Y_k^GG` is integral, normal and projective over `C` of
dimension `(n+1)k`; `B_k = O(m)` is a relatively very ample line bundle; the fiber degree `v_k` is
positive and equals `1/(k!)^{n+1}`; and `H_k^{(n+1)k} = −v_k d h_k`. -/
theorem harmonic_intersection {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {C : SmoothProjectiveCurve K} {X : SmoothProjectiveVariety K}
    (f : C.toScheme ⟶ X.toScheme) {N δ n : ℕ}
    (e : ProjectiveEmbedding K X.toScheme N) (E : EmbeddingEquations K e δ)
    (hn : X.toVariety.dim = n) (hn1 : 1 ≤ n)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (d : ℤ) (hd : TangentBundle.pullbackDegree f = d)
    (kk : ℕ) (hkk : 1 ≤ kk) (m : ℕ) (hm : 0 < m)
    (hdiv : (n + 1) * kk * jetWeight kk ∣ m) :
    let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
    let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous
      (seedSection_equations_vanish e E f coord hcoord)
    let Y := weightedJetProjectivization (k := K) Z s.1 s.2 kk
    let B : Y.left.Modules := AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1 (m : ℤ)
    letI : Y.left.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨Y.hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩;
    ∀ (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
      (hfib : letI := Y.hom.fiberOverSpecResidueField c;
        IsProperOver (C.toScheme.residueField c) (Y.hom.fiber c)) (hY : IsProperOver K Y.left),
    AlgebraicGeometry.IsIntegral Y.left ∧ Y.left.IsNormal ∧
    AlgebraicGeometry.IsProjectiveMorphism Y.hom ∧ Y.left.dimension = (n + 1) * kk ∧
    ∃ hB : B.IsLineBundle, haveI := hB; AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple Y.hom B ∧
    0 < AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib ∧
    tautologicalTopSelfIntersection Y.left hY B m hm
      = - ((AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
            (m : ℚ) ^ ((n + 1) * kk - 1))
          * (d : ℚ) * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) ∧
    (AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
        (m : ℚ) ^ ((n + 1) * kk - 1)
      = 1 / ((kk.factorial : ℚ) ^ (n + 1)) ∧
    tautologicalTopSelfIntersection Y.left hY B m hm
      = - ((d : ℚ) / (kk.factorial : ℚ) ^ (n + 1))
          * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
  dsimp
  intro c hc hfib hY
  let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
  let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous
    (seedSection_equations_vanish e E f coord hcoord)
  let Y := weightedJetProjectivization (k := K) Z s.1 s.2 kk
  let B : Y.left.Modules := AlgebraicGeometry.Scheme.relativeProj.twist
    (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1 (m : ℤ)
  letI : Y.left.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨Y.hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  letI : AlgebraicGeometry.SmoothOfRelativeDimension n
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    exact smoothOfRelativeDimension_of_dim (X := X) hn
  have hp := puncturedCone_spec (n := n) e E f coord hcoord
  let Zx := puncturedCone (seedLineBundle e f) N E.deg E.deg_pos E.F E.homogeneous
  have hsZx : ∀ c : C.toScheme, s.1.base c ∈ Zx := by
    intro c
    obtain ⟨s', hs'⟩ := seedSection_mem_punctured e E f coord hcoord E.deg_pos
      (fun j => seedSection_equations_vanish e E f coord hcoord j)
    have hmem : (Zx.ι.base (s' c)) ∈ Zx := (s' c).property
    have heq : (s' ≫ Zx.ι) c = s.1 c := by
      simpa [s, Zx] using congrArg (fun g => g c) hs'
    rw [← heq]
    exact hmem
  letI : AlgebraicGeometry.IsClosedImmersion s.1 :=
    AlgebraicGeometry.IsClosedImmersion.of_section Z.hom s.1 s.2
  letI : AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom) :=
    hp.2.1
  have hloc := jetGradedAlgebra_isLocallyWeightedPolynomial Z s.1 s.2 Zx hsZx n kk
  have hgeom := ykGG_integral_normal_projective Z s.1 s.2 n kk hkk hloc
  have hdiv' : ∀ q ∈ Finset.Icc 1 kk, q ∣ m := by
    intro q hq
    exact dvd_trans (dvd_mul_of_dvd_right (Finset.dvd_lcm hq) ((n + 1) * kk)) hdiv
  obtain ⟨mult, hmult⟩ := hdiv
  have hprod : 0 < ((n + 1) * kk * jetWeight kk) * mult := by
    rw [← hmult]
    exact hm
  have hmult_pos : 0 < mult := Nat.pos_of_mul_pos_left hprod
  let σ := ULift.{u} (Fin (n + 1) × Fin kk)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  letI : Fintype σ := inferInstance
  letI : Nonempty σ := ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  have hw : ∀ i, w i ∈ Finset.Icc 1 kk := by
    intro i
    simp [w]
  have hSuff0 := veronese_generation_multiple
    (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1 w hw hloc mult hmult_pos
  have hcard : Fintype.card σ = (n + 1) * kk := by
    simp [σ]
  have hEq : mult * (Fintype.card σ * jetWeight kk) = m := by
    rw [hcard]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult.symm
  have hSuff : (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1.SufficientlyDivisible m := by
    rw [← hEq]
    exact hSuff0
  have hvery := twist_isLineBundle_relativelyVeryAmple
    (S := (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1)
    (σ := σ) (k := kk) w hw hloc mult m hmult_pos hEq.symm
  have hB : B.IsLineBundle := hvery.1
  have hpos := fiberDegree_pos Z s.1 s.2 n kk hkk hloc m hSuff hdiv' c hc hfib
  have hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j)
      (E.homogeneous j) coord = 0 := by
    intro j
    exact seedSection_equations_vanish e E f coord hcoord j
  obtain ⟨V, hEZ, hVrank, hVdeg⟩ := cone_rank_degree e E f coord hcoord hvanish
  have hVr : V.rank = n + 1 := by simpa [hn] using hVrank
  obtain ⟨F⟩ : Nonempty (SubbundleFiltration V (n + 1)) := by
    simpa [hVr] using (exists_subbundleFiltration V)
  letI : (splitWeightedProjectivization F kk).left.Over
      (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨(splitWeightedProjectivization F kk).hom ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  let pC : C.toScheme ⟶ AlgebraicGeometry.Spec (CommRingCat.of K) :=
    C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)
  have hSplitLoc : (splitWeightedAlgebraOf F kk).IsLocallyWeightedPolynomial w
      (fun _ => Nat.succ_pos _) := by
    let Q : Fin kk → C.toScheme.Modules := fun _ =>
      CategoryTheory.Limits.biproduct
        (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)
    letI : ∀ q, (Q q).IsLocallyFree := fun q => by
      dsimp [Q]
      infer_instance
    letI : ∀ q, (Q q).IsFiniteType := fun q => by
      dsimp [Q]
      infer_instance
    have hS0 := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
      _ kk (n + 1) Q (fun _ => inferInstance) (fun _ => inferInstance)
        (fun q x => harmonic_biproduct_rank F x)
    simpa [splitWeightedAlgebraOf, Q] using hS0.1
  letI : AlgebraicGeometry.IsProper pC := by
    exact IsProjectiveOver.isProper C.projective
  letI : AlgebraicGeometry.IsProper (splitWeightedProjectivization F kk).hom := by
    exact harmonic_proper_relativeProj_of_localProduct pC
      (splitWeightedAlgebraOf F kk) w (fun _ => Nat.succ_pos _) hSplitLoc
  have hSplitProper : IsProperOver K (splitWeightedProjectivization F kk).left := by
    change AlgebraicGeometry.IsProper
      ((splitWeightedProjectivization F kk).hom ≫ pC)
    infer_instance
  letI : AlgebraicGeometry.IsIntegral (splitWeightedProjectivization F kk).left := by
    letI : AlgebraicGeometry.IsIntegral C.toScheme :=
      SmoothProjectiveCurve.isIntegral_of_smooth_connected C
    letI : IrreducibleSpace C.toScheme :=
      AlgebraicGeometry.irreducibleSpace_of_isIntegral C.toScheme
    letI : AlgebraicGeometry.Smooth pC := by
      simpa [pC, IsSmoothOver] using C.smooth
    letI : GradedRing (MiyaokaMori.WeightedJets.weightedPolynomialGrading K
        (fun i : σ => (⟨w i, Nat.succ_pos _⟩ : ℕ+))) :=
      MvPolynomial.weightedGradedAlgebra (R := K) (w := fun i : σ => w i)
    have hFirr : IrreducibleSpace (weightedProjectiveSpace K w (fun _ => Nat.succ_pos _)) := by
      change IrreducibleSpace (AlgebraicGeometry.Proj
        (MiyaokaMori.WeightedJets.weightedPolynomialGrading K
          (fun i : σ => (⟨w i, Nat.succ_pos _⟩ : ℕ+))))
      apply AlgebraicGeometry.Proj.irreducibleSpace_of_isDomain
      let i : σ := Classical.choice (inferInstance : Nonempty σ)
      refine ⟨w i, MvPolynomial.X i, ?_, ?_, ?_⟩
      · exact Nat.succ_pos _
      · exact (MvPolynomial.mem_weightedHomogeneousSubmodule K _ _ _).mpr
          (MvPolynomial.isWeightedHomogeneous_X K (fun j => (w j : ℕ)) i)
      · exact MvPolynomial.X_ne_zero i
    obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u} pC
      (splitWeightedAlgebraOf F kk) w (fun _ => Nat.succ_pos _) hSplitLoc
    let 𝒱 : C.toScheme.OpenCover.{u} := 𝒰.ulift
    apply isIntegral_of_locally_product_over_irreducible pC
      (weightedProjectiveSpace K w (fun _ => Nat.succ_pos _) ↘
        AlgebraicGeometry.Spec (CommRingCat.of K))
      (splitWeightedProjectivization F kk).hom 𝒱
    · intro i
      obtain ⟨φ, hφ, _⟩ := h𝒰 (𝒰.idx i)
      exact ⟨φ, hφ⟩
    · intro i
      letI : Nonempty (𝒱.X i) := by
        obtain ⟨y, hy⟩ := 𝒰.covers i
        exact ⟨y⟩
      letI : AlgebraicGeometry.IsIntegral (𝒱.X i) :=
        AlgebraicGeometry.isIntegral_of_isOpenImmersion (𝒱.f i)
      letI : AlgebraicGeometry.Smooth (𝒱.f i ≫ pC) := inferInstance
      -- normality of U_i: smooth over a field with dim ≤ 1 implies normal
      -- (`Smooth.isNormal_of_field_of_dim_le_one`).
      letI : (𝒱.X i).IsNormal :=
        AlgebraicGeometry.Smooth.isNormal_of_field_of_dim_le_one (𝒱.f i ≫ pC)
          (le_trans (𝒱.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le
            (le_of_eq C.dim_one))
      apply weightedProjectiveSpace_prod_isIntegral K w (fun _ => Nat.succ_pos _)
        (𝒱.X i) (𝒱.f i ≫ pC)
  letI : (AlgebraicGeometry.Scheme.relativeProj.twist
      (splitWeightedAlgebraOf F kk) (m : ℤ)).IsLineBundle := by
    have hSplitSuff0 := veronese_generation_multiple
      (splitWeightedAlgebraOf F kk) w hw hSplitLoc mult hmult_pos
    have hSplitSuff : (splitWeightedAlgebraOf F kk).SufficientlyDivisible m := by
      rw [← hEq]
      exact hSplitSuff0
    exact AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist _ m hSplitSuff
  have hSplitFib : letI := (splitWeightedProjectivization F kk).hom.fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) ((splitWeightedProjectivization F kk).hom.fiber c) := by
    change AlgebraicGeometry.IsProper
      (CategoryTheory.Limits.pullback.snd
        (splitWeightedProjectivization F kk).hom
        (C.toScheme.fromSpecResidueField c))
    infer_instance
  have hJetFib : letI := Y.hom.fiberOverSpecResidueField c;
      IsProperOver (C.toScheme.residueField c) (Y.hom.fiber c) := hfib
  have hdimSplit : (splitWeightedProjectivization F kk).left.dimension =
      (n + 1) * kk := by
    let Q : Fin kk → C.toScheme.Modules := fun _ =>
      CategoryTheory.Limits.biproduct
        (fun i : Fin (n + 1) => (F.lineQuotient i).toModules)
    letI : ∀ q, (Q q).IsLocallyFree := fun q => by
      dsimp [Q]
      infer_instance
    letI : ∀ q, (Q q).IsFiniteType := fun q => by
      dsimp [Q]
      infer_instance
    have hS0 := @AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
      _ kk (n + 1) Q (fun _ => inferInstance) (fun _ => inferInstance)
        (fun q x => harmonic_biproduct_rank F x)
    have hS : (splitWeightedAlgebraOf F kk).IsLocallyWeightedPolynomial
        (fun iq : ULift.{u} (Fin (n + 1) × Fin kk) => ((iq.down.2 : ℕ) + 1))
        (fun _ => Nat.succ_pos _) := by
      simpa [splitWeightedAlgebraOf, Q] using hS0.1
    let σ : Type u := ULift.{u} (Fin (n + 1) × Fin kk)
    let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
    letI : Fintype σ := inferInstance
    letI : Nonempty σ := ⟨ULift.up ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
    have hkw := relativeProj_locallyWeighted_krullDim
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      (splitWeightedAlgebraOf F kk) w (fun i => by dsimp [w]; omega) hS
    have hraw : topologicalKrullDim (splitWeightedProjectivization F kk).left =
        ((1 : WithBot ℕ∞) + ((Fintype.card σ - 1 : ℕ) : WithBot ℕ∞)) := by
      simpa [splitWeightedProjectivization] using hkw.trans (by rw [C.dim_one])
    have hprod : 1 ≤ (n + 1) * kk := by
      calc
        1 ≤ kk := hkk
        _ ≤ (n + 1) * kk := Nat.le_mul_of_pos_left kk (by omega)
    have hcardσ : Fintype.card σ = (n + 1) * kk := by simp [σ]
    have hraw' : topologicalKrullDim (splitWeightedProjectivization F kk).left =
        (((n + 1) * kk : ℕ) : WithBot ℕ∞) := by
      rw [hraw, hcardσ, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hprod]
    have hbot : topologicalKrullDim (splitWeightedProjectivization F kk).left ≠ ⊥ := by
      rw [hraw']
      exact WithBot.coe_ne_bot
    have htop : topologicalKrullDim (splitWeightedProjectivization F kk).left ≠ ⊤ := by
      rw [hraw']
      intro h
      apply ENat.natCast_ne_top ((n + 1) * kk)
      exact WithBot.coe_eq_top.mp h
    have hs := AlgebraicGeometry.Scheme.dimension_spec
      (splitWeightedProjectivization F kk).left hbot htop
    exact_mod_cast hs.symm.trans hraw'
  have hdimJet : Y.left.dimension = (n + 1) * kk := hgeom.2.2.2.2
  have hVd : VectorBundle.degree V = d := hVdeg.trans hd
  have htop := split_tautological_top_intersection_eq Z s.1 s.2 Zx hsZx hkk V hVr hEZ hloc F m hm
    ⟨mult, by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmult⟩
    hSplitProper hY
  have hexpand := expand_weighted_relation hkk V hVr d hVd F m hm hdiv'
    hdimSplit hSplitProper c hc hSplitFib
  have hclass := harmonic_cycle_class_op_eq (r := kk) F hm hdiv'
  have hfiber := split_fiberDegree_eq Z s.1 s.2 hkk V hVr hloc F m hSuff hdiv' c hc
    hSplitFib hJetFib
  have hscaled := harmonic_rational_top_scaled_line
    (splitWeightedProjectivization F kk).left hSplitProper
    (AlgebraicGeometry.Scheme.relativeProj.twist
      (splitWeightedAlgebraOf F kk) (m : ℤ)) m ((n + 1) * kk) hdimSplit
  have hsplit_taut :
      AlgebraicGeometry.RatDivisorOp.topSelfIntersection
          (splitWeightedProjectivization F kk).left hSplitProper
          ((m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
            (AlgebraicGeometry.Scheme.relativeProj.twist
              (splitWeightedAlgebraOf F kk) (m : ℤ))) ((n + 1) * kk) hdimSplit =
        tautologicalTopSelfIntersection (splitWeightedProjectivization F kk).left
          hSplitProper
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (splitWeightedAlgebraOf F kk) (m : ℤ)) m hm := by
    simpa [tautologicalTopSelfIntersection, hdimSplit] using hscaled
  have hsplit_formula :
      tautologicalTopSelfIntersection (splitWeightedProjectivization F kk).left
          hSplitProper
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (splitWeightedAlgebraOf F kk) (m : ℤ)) m hm =
        - ((AlgebraicGeometry.relativePolarizationFiberDegree
          (splitWeightedProjectivization F kk).hom
          (AlgebraicGeometry.Scheme.relativeProj.twist
            (splitWeightedAlgebraOf F kk) (m : ℤ)) c hSplitFib : ℚ) /
          (m : ℚ) ^ ((n + 1) * kk - 1)) * (d : ℚ) *
          ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
    rw [← hsplit_taut, ← hclass]
    exact hexpand
  -- the explicit fiber degree v_k / m^{(n+1)k-1} = 1/(k!)^{n+1} (Lemma 2.2)
  have hv : (AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
      (m : ℚ) ^ ((n + 1) * kk - 1) = 1 / ((kk.factorial : ℚ) ^ (n + 1)) :=
    fiberDegree_div_pow_eq Z s.1 s.2 n kk hkk hloc m hSuff hdiv' c hc hfib
  have hmain : tautologicalTopSelfIntersection Y.left hY B m hm =
      - ((AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
            (m : ℚ) ^ ((n + 1) * kk - 1))
          * (d : ℚ) * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
    calc
      tautologicalTopSelfIntersection Y.left hY B m hm =
          tautologicalTopSelfIntersection (splitWeightedProjectivization F kk).left
            hSplitProper
            (AlgebraicGeometry.Scheme.relativeProj.twist
              (splitWeightedAlgebraOf F kk) (m : ℤ)) m hm := by
        simpa [Y, B] using htop.symm
      _ = - ((AlgebraicGeometry.relativePolarizationFiberDegree
            (splitWeightedProjectivization F kk).hom
            (AlgebraicGeometry.Scheme.relativeProj.twist
            (splitWeightedAlgebraOf F kk) (m : ℤ)) c hSplitFib : ℚ) /
            (m : ℚ) ^ ((n + 1) * kk - 1)) * (d : ℚ) *
            ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
        exact hsplit_formula
      _ = - ((AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
            (m : ℚ) ^ ((n + 1) * kk - 1)) * (d : ℚ) *
            ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
        rw [hfiber.1]
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.2, hB,
    hvery.2, hpos, hmain, hv, ?_⟩
  -- H_k^{(n+1)k} = −d/(k!)^{n+1} · Σ 1/q (Proposition 2.4)
  rw [hmain, hv]
  ring

end
