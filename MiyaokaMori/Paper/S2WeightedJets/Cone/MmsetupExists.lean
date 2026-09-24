import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TautologicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.Stacks01ne

/-! # Existence of the setup data

The data fixed at the beginning of §2 of the paper always exist: for a `k`-morphism `f : C → X` with
`X ⊂ ℙ^N` (the fixed embedding `X.embedding`), the homogeneous ideal of `X` has homogeneous generators
of degrees in `[1, δ]`, and `f` has homogeneous coordinate sections `f_ℓ = f^*x_ℓ ∈ H⁰(C, f^*O_X(1))`;
hence `MMSetup f` has an instance.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma projective_coordinate_cover {k : Type u} [Field k] {N : ℕ}
    (y : ProjectiveSpace N k) :
    ∃ i : Fin (N + 1),
      y ∈ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
        (MvPolynomial.X i) := by
  have hcover : (⨆ i : Fin (N + 1),
      AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
        (MvPolynomial.X i)) = ⊤ := by
    apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
      (AlgebraicGeometry.Proj.projectiveGrading k N) MvPolynomial.X
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
      exact (Algebra.adjoin ((AlgebraicGeometry.Proj.projectiveGrading k N) 0)
        (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k))).algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (N + 1)) r⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ y))

private lemma away_mk_zero_eq_fromZero
    {k : Type u} [Field k] {N : ℕ} {i : Fin (N + 1)}
    {F : MvPolynomial (Fin (N + 1)) k}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) :
    (HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
          (MvPolynomial.isHomogeneous_X k i)) 0 F hF :
      HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) =
      HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (Submonoid.powers (MvPolynomial.X i)) ⟨F, hF⟩ := by
  apply HomogeneousLocalization.val_injective
  rfl

private lemma projectiveVanishingIdealDeg_zero_eq_zero
    {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {F : MvPolynomial (Fin (X.embDim + 1)) k}
    (hF : F ∈ projectiveVanishingIdealDeg X.embedding.emb.ker 0) : F = 0 := by
  rcases hF with ⟨hhom, hsections⟩
  have htotal : F.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (X.embDim + 1))).mpr hhom
  have hC : F = MvPolynomial.C (F.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp htotal
  let e := X.embedding
  obtain ⟨x⟩ := (AlgebraicGeometry.IsIntegral.nonempty : Nonempty X.toScheme)
  obtain ⟨i, hi⟩ := projective_coordinate_cover (e.emb.base x)
  let U : (ProjectiveSpace X.embDim k).affineOpens :=
    ⟨AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k X.embDim)
      (MvPolynomial.X i),
      AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
          (MvPolynomial.isHomogeneous_X k i)) Nat.one_pos⟩
  let V : X.toScheme.Opens := e.emb ⁻¹ᵁ U.1
  have hV : Nonempty V := by
    exact ⟨⟨x, (AlgebraicGeometry.Scheme.Hom.mem_preimage e.emb).2 hi⟩⟩
  letI : Nonempty V := hV
  by_contra hFne
  have hrne : F.coeff 0 ≠ 0 := by
    intro hr
    apply hFne
    rw [hC]
    simp [hr]
  have hFmem : F ∈ MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k 0 := by
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 hhom
  have hsub_eq : (⟨F, hFmem⟩ : MvPolynomial.homogeneousSubmodule
      (Fin (X.embDim + 1)) k 0) =
      algebraMap k (MvPolynomial.homogeneousSubmodule
        (Fin (X.embDim + 1)) k 0) (F.coeff 0) := by
    apply Subtype.ext
    change F = (algebraMap k (MvPolynomial.homogeneousSubmodule
      (Fin (X.embDim + 1)) k 0) (F.coeff 0) :
        MvPolynomial (Fin (X.embDim + 1)) k)
    rw [hC]
    simp
  have hsub_unit : IsUnit (⟨F, hFmem⟩ :
      MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k 0) := by
    rw [hsub_eq]
    exact (isUnit_iff_ne_zero.mpr hrne).map
      (algebraMap k (MvPolynomial.homogeneousSubmodule
        (Fin (X.embDim + 1)) k 0))
  have haway_unit : IsUnit (
      HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
          (MvPolynomial.isHomogeneous_X k i)) 0 F
        (by simpa [hFmem] using hFmem)) := by
    rw [away_mk_zero_eq_fromZero hFmem]
    exact hsub_unit.map
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k)
        (Submonoid.powers (MvPolynomial.X i)))
  have hsec_unit : IsUnit (
      (AlgebraicGeometry.Proj.awayToSection
        (MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k)
        (MvPolynomial.X i)).hom
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k)
          ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
            (MvPolynomial.isHomogeneous_X k i)) 0 F
          (by simpa [hFmem] using hFmem))) := by
    exact haway_unit.map
      (AlgebraicGeometry.Proj.awayToSection
        (MvPolynomial.homogeneousSubmodule (Fin (X.embDim + 1)) k)
        (MvPolynomial.X i)).hom
  have hmem := hsections i
  have htop : e.emb.ker.ideal U = ⊤ :=
    (e.emb.ker.ideal U).eq_top_of_isUnit_mem hmem hsec_unit
  have htop' : (1 : Γ(ProjectiveSpace X.embDim k, U.1)) ∈ e.emb.ker.ideal U := by
    rw [htop]
    simp
  have hmemker : (1 : Γ(ProjectiveSpace X.embDim k, U.1)) ∈
      RingHom.ker (e.emb.app U).hom := by
    rw [← AlgebraicGeometry.Scheme.Hom.ker_apply e.emb U]
    exact htop'
  have hzero : ((e.emb.app U).hom : _ →+* _) 1 = 0 := RingHom.mem_ker.mp hmemker
  have hcontra : ((1 : Γ(X.toScheme, V)) = 0) := by
    simpa using hzero
  exact one_ne_zero hcontra

private lemma homogeneous_mem_irrelevant {k : Type u} [Field k] {N d : ℕ}
    {F : MvPolynomial (Fin (N + 1)) k} (hF : F.IsHomogeneous d) (hd : 0 < d) :
    F ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (N + 1)))) := by
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdeg := hF (MvPolynomial.mem_support_iff.mp hm)
  have hmne : m ≠ 0 := by
    intro hm0
    subst m
    simp at hdeg
    omega
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hmne
  exact ⟨i, Set.mem_univ i, Finsupp.mem_support_iff.mp hi⟩

private lemma projectiveVanishingIdeal_proper
    {k : Type u} [Field k] {X : SmoothProjectiveVariety k} :
    (projectiveVanishingIdeal X.embedding.emb.ker).toIdeal ≠ ⊤ := by
  let R := MvPolynomial (Fin (X.embDim + 1)) k
  let c : R →+* k := MvPolynomial.constantCoeff
  have hX : ∀ i : Fin (X.embDim + 1),
      MvPolynomial.X i ∈ RingHom.ker c := by
    intro i
    change MvPolynomial.constantCoeff (MvPolynomial.X i) = 0
    simp
  have hspanX : Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (X.embDim + 1)))) ≤
      RingHom.ker c := by
    apply Ideal.span_le.2
    rintro _ ⟨i, -, rfl⟩
    exact hX i
  have hgen : ∀ d : ℕ, ∀ F ∈ projectiveVanishingIdealDeg
      X.embedding.emb.ker d, F ∈ RingHom.ker c := by
    intro d F hF
    rcases hF with ⟨hhom, hcond⟩
    by_cases hd : d = 0
    · subst d
      have hzero : F = 0 := projectiveVanishingIdealDeg_zero_eq_zero ⟨hhom, hcond⟩
      simp [hzero, c]
    · apply hspanX
      exact homogeneous_mem_irrelevant hhom (Nat.pos_of_ne_zero hd)
  have hle : (projectiveVanishingIdeal X.embedding.emb.ker).toIdeal ≤ RingHom.ker c := by
    change Ideal.span (⋃ d, projectiveVanishingIdealDeg X.embedding.emb.ker d) ≤ _
    apply Ideal.span_le.2
    intro F hF
    obtain ⟨d, hFd⟩ := Set.mem_iUnion.1 hF
    exact hgen d F hFd
  intro htop
  have hone : (1 : R) ∈ RingHom.ker c := by
    apply hle
    rw [htop]
    simp
  have hc1 : c 1 = 1 := by simp [c]
  exact one_ne_zero (hc1 ▸ RingHom.mem_ker.mp hone)

private lemma homogeneous_degree_pos_of_proper
    {k : Type u} [Field k] {N : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) k)}
    (hproper : I ≠ ⊤) {F : MvPolynomial (Fin (N + 1)) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFI : F ∈ I) (hFne : F ≠ 0) : 0 < d := by
  by_contra hnot
  have hd : d = 0 := Nat.eq_zero_of_not_pos hnot
  subst d
  have htotal : F.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (N + 1))).mpr hF
  have hr : F = MvPolynomial.C (F.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp htotal
  have hrne : F.coeff 0 ≠ 0 := by
    intro hr0
    apply hFne
    rw [hr]
    simp [hr0]
  have hunitF : IsUnit F := by
    rw [hr]
    exact (isUnit_iff_ne_zero.mpr hrne).map MvPolynomial.C
  exact hproper (I.eq_top_of_isUnit_mem hFI hunitF)

private theorem embeddingEquations_of_proper
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N)
    (hproper : (projectiveVanishingIdeal e.emb.ker).toIdeal ≠ ⊤) :
    ∃ δ : ℕ, Nonempty (EmbeddingEquations k e δ) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k
  let I := (projectiveVanishingIdeal e.emb.ker).toIdeal
  have hhom : I.IsHomogeneous 𝒜 := (projectiveVanishingIdeal e.emb.ker).isHomogeneous
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists 𝒜 I).mp hhom
  have hfg : I.FG := by
    letI : IsNoetherianRing (MvPolynomial (Fin (N + 1)) k) := inferInstance
    exact Ideal.fg_of_isNoetherianRing I
  let vals : Set (MvPolynomial (Fin (N + 1)) k) :=
    Subtype.val '' (S : Set (SetLike.homogeneousSubmonoid 𝒜))
  have hspanvals : Ideal.span vals = I := hS.symm
  have hvalI : vals ⊆ I := by
    intro x hx
    rw [← hspanvals]
    exact Ideal.subset_span hx
  have hspanvals_fg : (Submodule.span (MvPolynomial (Fin (N + 1)) k) vals).FG := by
    change (Ideal.span vals).FG
    exact hspanvals ▸ hfg
  obtain ⟨T, hTsub, hTeq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset vals).mp hspanvals_fg
  let ι := T
  let F : ι → MvPolynomial (Fin (N + 1)) k := fun j => j.1
  have hmem : ∀ j : ι, ∃ d, (F j).IsHomogeneous d := by
    intro j
    rcases hTsub j.2 with ⟨s, hs, hsj⟩
    rcases s.property with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    simpa [F] using hsj ▸ hd
  classical
  let deg : ι → ℕ := fun j => if hj : F j = 0 then 1 else Classical.choose (hmem j)
  have hdeg_hom : ∀ j, (F j).IsHomogeneous (deg j) := by
    intro j
    by_cases hj : F j = 0
    · simp [deg, hj, MvPolynomial.isHomogeneous_zero]
    · simp only [deg, dif_neg hj]
      exact Classical.choose_spec (hmem j)
  have hdeg_pos : ∀ j, 0 < deg j := by
    intro j
    by_cases hj : F j = 0
    · simp [deg, hj]
    · apply homogeneous_degree_pos_of_proper hproper
        (hdeg_hom j) (hvalI (hTsub j.2)) hj
  letI : Fintype ι := Fintype.ofFinite ι
  let δ : ℕ := Finset.univ.sup deg + 1
  have hdeg_le : ∀ j, deg j ≤ δ := by
    intro j
    exact Nat.le_succ_of_le (Finset.le_sup (Finset.mem_univ j))
  have hrange : Set.range F = (T : Set _) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact j.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hspanT : Ideal.span (T : Set _) = I := by
    have hTeq' : Ideal.span vals = Ideal.span (T : Set _) := by
      simpa only [Ideal.span] using hTeq
    exact hTeq'.symm.trans hspanvals
  have hspan : Ideal.span (Set.range F) =
      (projectiveVanishingIdeal e.emb.ker).toIdeal := by
    rw [hrange, hspanT]
  let E : EmbeddingEquations k e δ :=
    { ι := ι, deg := deg, F := F, homogeneous := hdeg_hom, deg_le := hdeg_le,
      deg_pos := hdeg_pos, δ_pos := Nat.succ_pos _,
      -- `spans : IsVanishingLocus e F`: unfold the predicate to the equation `hspan`.
      spans := by simpa [I, IsVanishingLocus] using hspan }
  exact ⟨δ, ⟨E⟩⟩

private lemma projective_coordinate_nonzero {k : Type u} [Field k] {N : ℕ}
    (y : ProjectiveSpace N k) :
    ∃ i, ¬ IsZeroAt (projectiveSpaceCoordinate k N i) y := by
  obtain ⟨i, hi⟩ := projective_coordinate_cover y
  refine ⟨i, ?_⟩
  exact AlgebraicGeometry.Proj.not_isZeroAt_twistSection_of_mem_basicOpen
      (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).2
        (MvPolynomial.isHomogeneous_X k i)) y hi

private def mmsetup_candidate_coord {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {C : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (e : ProjectiveEmbedding k X N) (f : C ⟶ X) :
    Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u) :=
  fun i => sectionPullbackAlong f
    (sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i))

private theorem mmsetup_candidate_hcoord {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {C : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (e : ProjectiveEmbedding k X N) (f : C ⟶ X)
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    IsHomogeneousCoordinateTuple e f (mmsetup_candidate_coord e f) := by
  have hP : ∀ c : C, ∃ i, ¬ IsZeroAt (mmsetup_candidate_coord e f i) c := by
    intro c
    obtain ⟨i, hi⟩ := projective_coordinate_nonzero (e.emb.base (f.base c))
    refine ⟨i, ?_⟩
    letI : (e.oX 1).IsLineBundle := by
      unfold ProjectiveEmbedding.oX
      infer_instance
    apply not_isZeroAt_sectionPullbackAlong f (e.oX 1)
      (sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i)) c
    apply not_isZeroAt_sectionPullbackAlong e.emb (projectiveSpaceTwist k N 1)
      (projectiveSpaceCoordinate k N i) (f.base c)
    exact hi
  letI : e.emb.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨e.over⟩
  let φ : C ⟶ ProjectiveSpace N k := f ≫ e.emb
  letI : φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  let M : C.Modules := seedLineBundle e f
  let θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj
      (projectiveSpaceTwist k N 1) ≅ M :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f e.emb).app
      (projectiveSpaceTwist k N 1) |>.symm
  have hθ : ∀ i, θ.hom.app ⊤
      (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i)) =
        mmsetup_candidate_coord e f i := by
    intro i
    change (((AlgebraicGeometry.Scheme.Modules.pullbackComp f e.emb).app
        (projectiveSpaceTwist k N 1)).inv.app ⊤
      (sectionPullbackAlong φ (projectiveSpaceCoordinate k N i))) =
      sectionPullbackAlong f (sectionPullbackAlong e.emb
        (projectiveSpaceCoordinate k N i))
    exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv f e.emb
      (M := projectiveSpaceTwist k N 1) (projectiveSpaceCoordinate k N i)
  exact ⟨hP, (projectiveSpace_hom_ext_of_sections φ M
    (mmsetup_candidate_coord e f) hP θ hθ).symm⟩

theorem MMSetup.nonempty {K : Type u} [Field K] {X : SmoothProjectiveVariety K}
    {C : SmoothProjectiveCurve K} (f : C.toScheme ⟶ X.toScheme)
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] :
    Nonempty (MMSetup f) := by
  obtain ⟨δ, ⟨E⟩⟩ := embeddingEquations_of_proper X.embedding
    (projectiveVanishingIdeal_proper (X := X))
  refine ⟨⟨δ, E, mmsetup_candidate_coord X.embedding f, ?_⟩⟩
  exact mmsetup_candidate_hcoord X.embedding f

end
