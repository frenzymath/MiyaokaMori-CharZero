import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1_CanonicalMap
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.GammaStarSectionRingLocalization
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # The canonical morphism to Proj is an open immersion with dense image

**Stacks 01Q1 / 01Q0 for the glued canonical morphism `f : X → Proj Γ_*(X, L)`.**

* `isOpenImmersion_canonicalProjMap` (Stacks 01Q1): if `X` is quasi-compact and quasi-separated and
  the affine `X_s` cover `X`, then `f` is an open immersion. Proof (Stacks 01Q1 verbatim): on an affine
  `X_s` the chart is `X_s ≅ Spec Γ(X_s, O) → Spec Γ_*(X,L)_{(s)} ≅ D₊(s)`, and the middle map is an
  isomorphism because `Γ_*(X,L)_{(s)} → Γ(X_s, O)` is bijective (Stacks 01PW,
  `awayToSections_bijective`). So `f` is an open immersion on each member of an open cover of `X`;
  it is injective on points because `f⁻¹(D₊(s)) = X_s` and the chart is injective; hence `f` is an
  open immersion (`IsOpenImmersion.of_openCover_source`).
* `dense_range_canonicalProjMap` (Stacks 01Q0): the image of `f` is dense. Proof: every nonempty
  open of `Proj` contains a nonempty `D₊(y)` with `y` homogeneous of positive degree (basic opens
  form a basis, homogeneous components, and `Proj.affineOpenCover`); if `X_y = ∅` then `y_m|_{X_y} = 0`
  trivially, so by 01PW(1) (`exists_mul_pow_eq_zero_of_res_eq_zero`) `y` is nilpotent and
  `D₊(y) = ∅`, a contradiction; so `X_y = f⁻¹(D₊(y)) ≠ ∅` and `D₊(y)` meets the image.

Source: Stacks 01Q1 (`properties-lemma-ample-immersion-into-proj`), Stacks 01Q0
(`properties-lemma-map-into-proj-quasi-compact`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]

/-! ## The charts on affine `X_s` are open immersions -/

/-- On an affine `X_s` (with `X` quasi-compact and quasi-separated) the chart
`X_s → Spec Γ_*(X,L)_{(s)} ⊆ Proj Γ_*(X, L)` is an open immersion (Stacks 01Q1, "`f` induces an
isomorphism `X_{s_i} → D₊(s_i)`"). -/
theorem isOpenImmersion_projCoverChart [CompactSpace X] [QuasiSeparatedSpace X]
    (i : ProjCoverIndex L) (hi : AlgebraicGeometry.IsAffineOpen (projCoverOpens L i)) :
    AlgebraicGeometry.IsOpenImmersion (projCoverChart L i) := by
  obtain ⟨d, s, hd⟩ := i
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  have h1 : IsIso ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s).toSpecΓ := by
    rw [← hi.isoSpec_hom]; infer_instance
  have h2 : IsIso (CommRingCat.ofHom (awayToSections L hs (projCoverOpens_le L ⟨d, s, hd⟩))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (awayToSections_bijective L s)
  unfold projCoverChart projChart
  infer_instance

/-- The canonical map is injective on points: two points with the same image lie in a common `X_s`
(since `f⁻¹(D₊(s)) = X_s`), where `f` is the chart, an open immersion. -/
theorem canonicalProjMap_injective [CompactSpace X] [QuasiSeparatedSpace X]
    (hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s)
    (hcov' : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ∧
        AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s)) :
    Function.Injective (canonicalProjMap L hcov) := by
  intro p q hpq
  obtain ⟨d, hd, s, hp, haff⟩ := hcov' p
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  have hpre := canonicalProjMap_preimage_basicOpen L hcov hs hd
  rw [gammaStarComponent_gammaStarOf] at hpre
  have hq : q ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := by
    rw [← hpre]
    change canonicalProjMap L hcov q ∈ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)
    rw [← hpq]
    have : p ∈ canonicalProjMap L hcov ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) := by rw [hpre]; exact hp
    exact this
  let i : ProjCoverIndex L := ⟨d, s, hd⟩
  have hinj := (AlgebraicGeometry.Scheme.Hom.isOpenEmbedding (projCoverChart L i)
    (H := isOpenImmersion_projCoverChart L i haff)).injective
  have h1 := congrArg (fun g => g (⟨p, hp⟩ : (projCoverOpens L i).toScheme)) (ι_canonicalProjMap L hcov i)
  have h2 := congrArg (fun g => g (⟨q, hq⟩ : (projCoverOpens L i).toScheme)) (ι_canonicalProjMap L hcov i)
  have h3 : projCoverChart L i ⟨p, hp⟩ = projCoverChart L i ⟨q, hq⟩ := by
    rw [← h1, ← h2]
    exact hpq
  exact congrArg Subtype.val (hinj h3)

/-- **Stacks 01Q1**: if `X` is quasi-compact and quasi-separated and the affine `X_s` cover `X`
(e.g. `L` ample), the canonical morphism `X → Proj Γ_*(X, L)` is an open immersion. -/
theorem isOpenImmersion_canonicalProjMap [CompactSpace X] [QuasiSeparatedSpace X]
    (hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s)
    (hcov' : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ∧
        AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s)) :
    AlgebraicGeometry.IsOpenImmersion (canonicalProjMap L hcov) := by
  -- the affine sub-cover
  let ι' := {i : ProjCoverIndex L // AlgebraicGeometry.IsAffineOpen (projCoverOpens L i)}
  have hU : TopologicalSpace.IsOpenCover (fun i : ι' => projCoverOpens L i.1) := by
    refine eq_top_iff.mpr fun p _ => ?_
    obtain ⟨d, hd, s, hp, haff⟩ := hcov' p
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨d, s, hd⟩, haff⟩, hp⟩
  refine AlgebraicGeometry.IsOpenImmersion.of_openCover_source _
    (X.openCoverOfIsOpenCover (fun i : ι' => projCoverOpens L i.1) hU)
    (canonicalProjMap_injective L hcov hcov') fun i => ?_
  show AlgebraicGeometry.IsOpenImmersion ((projCoverOpens L i.1).ι ≫ canonicalProjMap L hcov)
  rw [ι_canonicalProjMap]
  exact isOpenImmersion_projCoverChart L i.1 i.2

/-! ## Density -/

/-- Sections over the empty open are zero (`1 = 0` in `Γ(X, ⊥)`). -/
theorem eq_zero_of_eq_bot (M : X.Modules) {W : X.Opens} (hW : W = ⊥) (v : Γ(M, W)) : v = 0 := by
  subst hW
  have h : (1 : Γ(X, ⊥)) = 0 := Subsingleton.elim _ _
  calc v = (1 : Γ(X, ⊥)) • v := (one_smul _ v).symm
    _ = (0 : Γ(X, ⊥)) • v := by rw [h]
    _ = 0 := zero_smul _ v

/-- **`D₊(y) ≠ ∅ ⟹ X_y ≠ ∅`** (`X` quasi-compact): if `X_y = ∅` then `y` is nilpotent by 01PW(1). -/
theorem exists_mem_nonvanishingLocus_of_mem_basicOpen [CompactSpace X]
    {y : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m)
    {q : AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)}
    (hq : q ∈ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) y) :
    ∃ p : X, p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y m) := by
  by_contra hcon
  have hbot : (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y m) = ⊥ :=
    le_bot_iff.mp fun p hp => (hcon ⟨p, hp⟩).elim
  -- `y_m|_{X_y} = 0`, so `y · y^k = 0` for some `k`
  obtain ⟨k, hk⟩ := exists_mul_pow_eq_zero_of_res_eq_zero L
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y m) hy (eq_zero_of_eq_bot _ hbot _)
  rw [gammaStarOf_gammaStarComponent L hy, ← pow_succ'] at hk
  have h1 := AlgebraicGeometry.Proj.basicOpen_pow (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) y
    (k + 1) k.succ_pos
  rw [hk, AlgebraicGeometry.Proj.basicOpen_zero] at h1
  rw [← h1] at hq
  exact hq

/-- Every point of `Proj 𝒜` lies in some `D₊(h)` with `h` homogeneous of positive degree
(`Proj.affineOpenCover`). -/
theorem Proj.exists_mem_basicOpen_pos {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (q : AlgebraicGeometry.Proj 𝒜) :
    ∃ (e : ℕ) (h : A), 0 < e ∧ h ∈ 𝒜 e ∧ q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 h := by
  obtain ⟨p, hp⟩ := (AlgebraicGeometry.Proj.affineOpenCover 𝒜).covers q
  refine ⟨(AlgebraicGeometry.Proj.affineOpenCover 𝒜).idx q |>.1, _,
    ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).idx q).1.2, ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).idx q).2.2,
    ?_⟩
  rw [← AlgebraicGeometry.Proj.opensRange_awayι 𝒜 _ ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).idx q).2.2
    ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).idx q).1.2]
  exact ⟨p, hp⟩

/-- Every nonempty open of `Proj 𝒜` contains a nonempty `D₊(y)` with `y` homogeneous of positive
degree. -/
theorem Proj.exists_basicOpen_pos_subset {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {O : Set (AlgebraicGeometry.Proj 𝒜)} (hO : IsOpen O)
    {q : AlgebraicGeometry.Proj 𝒜} (hq : q ∈ O) :
    ∃ (e : ℕ) (y : A), 0 < e ∧ y ∈ 𝒜 e ∧ q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 y ∧
      (AlgebraicGeometry.Proj.basicOpen 𝒜 y : Set (AlgebraicGeometry.Proj 𝒜)) ⊆ O := by
  classical
  obtain ⟨_, ⟨r, rfl⟩, hqr, hrO⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hq hO
  -- a homogeneous component of `r` not vanishing at `q`
  have hqr' : q ∈ ⨆ i : ℕ, ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 i r) := by
    rw [← ProjectiveSpectrum.basicOpen_eq_union_of_projection]
    exact hqr
  obtain ⟨i, hqi⟩ := TopologicalSpace.Opens.mem_iSup.mp hqr'
  obtain ⟨e, h, he, hh, hqh⟩ := Proj.exists_mem_basicOpen_pos 𝒜 q
  refine ⟨e + i, h * GradedRing.proj 𝒜 i r, Nat.add_pos_left he i,
    SetLike.mul_mem_graded hh (DirectSum.decompose 𝒜 r i).2, ?_, ?_⟩
  · rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact ⟨hqh, hqi⟩
  · intro z hz
    apply hrO
    have hz' : z ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (h * GradedRing.proj 𝒜 i r) := hz
    rw [AlgebraicGeometry.Proj.basicOpen_mul] at hz'
    have h2 : z ∈ ProjectiveSpectrum.basicOpen 𝒜 r := by
      rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hz'.2⟩
    exact h2

/-- **Stacks 01Q0**: the canonical morphism has dense image (`X` quasi-compact). -/
theorem dense_range_canonicalProjMap [CompactSpace X]
    (hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
      p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s) :
    Dense (Set.range (canonicalProjMap L hcov).base) := by
  refine dense_iff_inter_open.mpr fun O hO ⟨q, hq⟩ => ?_
  obtain ⟨e, y, he, hy, hqy, hyO⟩ := Proj.exists_basicOpen_pos_subset
    (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) hO hq
  obtain ⟨p, hp⟩ := exists_mem_nonvanishingLocus_of_mem_basicOpen L hy hqy
  refine ⟨canonicalProjMap L hcov p, hyO ?_, ⟨p, rfl⟩⟩
  have h1 : p ∈ canonicalProjMap L hcov ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) y := by
    rw [canonicalProjMap_preimage_basicOpen L hcov hy he]
    exact hp
  exact h1

end AlgebraicGeometry.Scheme.Modules

end
