import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAtlasChartIntegral

/-! # A locally weighted-polynomial relative Proj over an integral base is integral

Statement: `X` an integral scheme, `S` a graded quasicoherent `O_X`-algebra which is locally the weighted
polynomial algebra in a nonempty finite set `σ` of variables (positive weights `w`). Then `Proj_X S` is an
integral scheme.

Proof:
1. Charts. Let 𝒜 be the atlas (`hS : Nonempty (WeightedPolynomialAtlas …)`), with affine charts U_i covering X
   and graded ring isomorphisms φ_i : S(U_i) ≃+* R_i[x_σ] (R_i = Γ(X, U_i), weighted grading w). Let
   W_i := image of `projChart U_i : Proj S(U_i) → Proj_X S` (an open immersion) = π⁻¹(U_i)
   (`proj_preimage_eq_opensRange`); the W_i with U_i ≠ ∅ cover Proj_X S (π z lies in some U_i, `covers`).
2. Each chart is integral. `WeightedPolynomialAtlas.projIso` (`Proj.map` of φ_i, both directions) gives
   Proj S(U_i) ≅ Proj R_i[x_σ]. R_i is a domain (X integral, U_i a nonempty open: `IsIntegral.component_integral`),
   so R_i[x_σ] is a domain, and Proj of a graded domain having a nonzero homogeneous element of positive degree
   (x_{i₀}, degree w i₀ > 0) is integral (`Proj.isIntegral_of_isDomain`, WeightedProjectiveSpaceIsIntegral.lean:
   irreducible by `ProjGradedDomainIrreducible.lean`, reduced since every stalk `HomogeneousLocalization.AtPrime`
   embeds in the localisation of a domain). Transport: `WeightedPolynomialAtlas.proj_isIntegral`, then
   `IsIntegral.of_isIso` along `(projChart U_i).isoOpensRange` gives `IsIntegral W_i`.
3. Proj_X S is reduced: `IsReduced.of_openCover` with the chart cover, each W_i being integral.
4. Proj_X S is irreducible (`PreirreducibleSpace.of_isOpenCover` + nonempty). Pairwise intersections: X is
   irreducible so U_i ∩ U_j ∋ z; the chart structure map Proj S(U_i) → U_i is surjective
   (`WeightedPolynomialAtlas.projToOpen_surjective`: over D_+(x_{i₀}) it is Spec of R_i → (R_i[x_σ]_{x_{i₀}})₀,
   which has a retraction x_{i₀} ↦ 1, x_k ↦ 0), so some p ∈ Proj S(U_i) lies over z and
   `projChart U_i p ∈ W_i ∩ W_j` (`projChart_hom`: π ∘ projChart = ι ∘ projToOpen). Nonempty: X ≠ ∅ and the same
   surjectivity.
5. `isIntegral_of_irreducibleSpace_of_isReduced`.
Shared chart-level facts live in `WeightedPolynomialAtlasChartIntegral.lean`.

Source: Stacks 01OA, 01NE (`D_+(f) = Spec A_(f)`), 00HQ (faithfully flat ⇒ surjective on Spec; replaced here by
an explicit retraction). Used for the integrality of `Y_k^GG` (Lemma 2.2 of the paper)
and of the ruled surface `P(O ⊕ L)` (Corollary 4.3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.relativeProj_isIntegral_of_isLocallyWeightedPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X] (S : X.GradedQCAlgebra)
    {σ : Type u} [Finite σ] [Nonempty σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hS : S.IsLocallyWeightedPolynomial w hw) :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.relativeProj S).left := by
  classical
  obtain ⟨𝒜⟩ := hS
  change AlgebraicGeometry.IsIntegral S.toGradedAffineAlgebra.relativeProj.left
  -- indices: the nonempty atlas charts
  let ι : Type u := { i : 𝒜.I // ((𝒜.chart i).toOpens : Set X).Nonempty }
  let W : ι → S.toGradedAffineAlgebra.relativeProj.left.Opens :=
    fun i => (S.toGradedAffineAlgebra.projChart (𝒜.chart i.1)).opensRange
  have hWmem : ∀ (i : ι) (z : S.toGradedAffineAlgebra.relativeProj.left),
      z ∈ W i ↔ S.toGradedAffineAlgebra.relativeProj.hom z ∈ (𝒜.chart i.1).toOpens := by
    intro i z
    change z ∈ (S.toGradedAffineAlgebra.projChart (𝒜.chart i.1)).opensRange ↔ _
    rw [← S.toGradedAffineAlgebra.proj_preimage_eq_opensRange]
    exact Iff.rfl
  -- a point of the chart `Proj S(U_i)` over any point of `U_i`
  have hlift : ∀ (i : 𝒜.I) (z : X), z ∈ (𝒜.chart i).toOpens →
      ∃ p : AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i)),
        S.toGradedAffineAlgebra.relativeProj.hom (S.toGradedAffineAlgebra.projChart (𝒜.chart i) p) = z := by
    intro i z hz
    obtain ⟨p, hp⟩ := 𝒜.projToOpen_surjective hw i ⟨z, hz⟩
    refine ⟨p, ?_⟩
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, S.toGradedAffineAlgebra.projChart_hom,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
    change ((S.toGradedAffineAlgebra.projToOpen (𝒜.chart i)).base p).1 = z
    rw [hp]
  -- the charts cover
  have hW : TopologicalSpace.IsOpenCover W := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro z _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := 𝒜.exists_chart_mem (S.toGradedAffineAlgebra.relativeProj.hom z)
    exact ⟨⟨i, ⟨_, hi⟩⟩, (hWmem ⟨i, ⟨_, hi⟩⟩ z).mpr hi⟩
  -- each chart is integral
  have hint : ∀ i : ι, AlgebraicGeometry.IsIntegral (W i).toScheme := by
    intro i
    have : Nonempty (𝒜.chart i.1).toOpens := i.2.to_subtype
    have : IsDomain Γ(X, (𝒜.chart i.1).toOpens) := AlgebraicGeometry.IsIntegral.component_integral _
    have : AlgebraicGeometry.IsIntegral
        (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading (𝒜.chart i.1))) :=
      𝒜.proj_isIntegral hw i.1
    exact AlgebraicGeometry.IsIntegral.of_isIso
      (S.toGradedAffineAlgebra.projChart (𝒜.chart i.1)).isoOpensRange.hom
  -- reduced
  have hred : AlgebraicGeometry.IsReduced S.toGradedAffineAlgebra.relativeProj.left :=
    @AlgebraicGeometry.IsReduced.of_openCover _
      (S.toGradedAffineAlgebra.relativeProj.left.openCoverOfIsOpenCover W hW)
      (fun i => by
        have := hint i
        exact inferInstanceAs (AlgebraicGeometry.IsReduced (W i).toScheme))
  -- irreducible: pairwise intersections are nonempty
  have hn : Pairwise (Function.onFun (fun a b => ¬ Disjoint a b) W) := by
    intro i j _ hdisj
    obtain ⟨x, hx⟩ := i.2
    obtain ⟨y, hy⟩ := j.2
    obtain ⟨z, -, hzi, hzj⟩ :=
      (PreirreducibleSpace.isPreirreducible_univ (X := X)) (𝒜.chart i.1).toOpens (𝒜.chart j.1).toOpens
        (𝒜.chart i.1).toOpens.isOpen (𝒜.chart j.1).toOpens.isOpen ⟨x, trivial, hx⟩ ⟨y, trivial, hy⟩
    obtain ⟨p, hp⟩ := hlift i.1 z hzi
    have hz : S.toGradedAffineAlgebra.projChart (𝒜.chart i.1) p ∈ W i ⊓ W j := by
      refine ⟨⟨p, rfl⟩, (hWmem j _).mpr ?_⟩
      rw [hp]
      exact hzj
    exact hdisj.le_bot hz
  have hpre : PreirreducibleSpace S.toGradedAffineAlgebra.relativeProj.left :=
    PreirreducibleSpace.of_isOpenCover hn hW fun i => by
      have := hint i
      exact inferInstanceAs (PreirreducibleSpace (W i).toScheme)
  have hne : Nonempty S.toGradedAffineAlgebra.relativeProj.left := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨i, hi⟩ := 𝒜.exists_chart_mem x
    obtain ⟨p, -⟩ := hlift i x hi
    exact ⟨S.toGradedAffineAlgebra.projChart (𝒜.chart i) p⟩
  have : IrreducibleSpace S.toGradedAffineAlgebra.relativeProj.left := ⟨hne⟩
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

end
