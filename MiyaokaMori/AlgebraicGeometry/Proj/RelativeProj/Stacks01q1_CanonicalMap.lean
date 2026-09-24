import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1_CanonicalMapCharts

/-! # The canonical morphism `X → Proj Γ_*(X, L)`

**Stacks 01PZ (`properties-lemma-map-into-proj`): the canonical morphism `X → Proj Γ_*(X, L)`.**

Let `L` be a line bundle on `X` such that the `X_s` (`s ∈ Γ(X, L^{⊗d})`, `d > 0`) cover `X` (this is
the covering half of ampleness, Stacks 01PS). Gluing the charts
`projChart : X_s → D₊(s) ⊆ Proj Γ_*(X, L)` (module `Stacks01q1_CanonicalMapCharts`) along the open
cover `{X_s}` (`Scheme.OpenCover.glueMorphisms`; the charts agree on `X_s ∩ X_t = X_{st}` by
`projChart_mul_left`) gives `canonicalProjMap L hcov : X ⟶ Proj Γ_*(X, L)` with

* `canonicalProjMap_preimage_basicOpen`: `f⁻¹(D₊(x)) = X_x` for every homogeneous `x` of positive
  degree (01PZ (1));
* `canonicalProjMap_appLE_awayToSection`: on `U ≤ X_x`, the pullback of `a/x^n ∈ Γ(D₊(x), O)` is
  the function `a · x^{-n}` (`awayToSections`), i.e. the unique `φ` with `φ · x^n = a` (01PZ (2));
* `isCanonicalProjMap'_canonicalProjMap`: `f` satisfies the characterization
  `IsCanonicalProjMap'` (verbatim the body of `IsAmple.IsCanonicalProjMap` in `Stacks01q1.lean`);
* `eq_canonicalProjMap_of_isCanonicalProjMap'`: **uniqueness** — any `g` satisfying the
  characterization equals `f`. Proof: on each `X_s` both `g` and `f` land in the affine open
  `D₊(s) = Spec Γ_*(X,L)_{(s)}`, so they are determined by the ring maps
  `Γ_*(X,L)_{(s)} → Γ(X_s, O)` (`ext_of_isAffine`), and (2) forces this ring map to be
  `a/s^n ↦ a · s^{-n}` for both (`awayToSections_mk_unique`).

Source: Stacks 01PZ; the uniqueness is the sentence "the morphism `f` is characterized by …" made
precise as in `IsAmple.IsCanonicalProjMap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]

/-! ## The cover by the `X_s` -/

/-- Index set of the cover: pairs `(d, s)` with `s ∈ Γ(X, L^{⊗d})`, `d > 0`. -/
abbrev ProjCoverIndex : Type u :=
  Σ' (d : ℕ) (_ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)), 0 < d

/-- The open `X_s` of the index `(d, s)`. -/
abbrev projCoverOpens (i : ProjCoverIndex L) : X.Opens :=
  (AlgebraicGeometry.Scheme.Modules.tensorPow L i.1).nonvanishingLocus i.2.1

/-- `X_s ≤ X_{(gammaStarOf s)_d}` (the two spellings of the same open). -/
theorem projCoverOpens_le (i : ProjCoverIndex L) :
    projCoverOpens L i ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L i.1).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L i.1 i.2.1) i.1) := by
  rw [gammaStarComponent_gammaStarOf]

variable (hcov : ∀ p : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
  p ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s)

include hcov in
theorem isOpenCover_projCoverOpens : TopologicalSpace.IsOpenCover (projCoverOpens L) := by
  refine eq_top_iff.mpr fun p _ => ?_
  obtain ⟨d, hd, s, hp⟩ := hcov p
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨d, s, hd⟩, hp⟩

/-- The open cover `{X_s}` of `X`. -/
def projCover : X.OpenCover :=
  X.openCoverOfIsOpenCover (projCoverOpens L) (isOpenCover_projCoverOpens L hcov)

/-- The chart of the index `i`. -/
def projCoverChart (i : ProjCoverIndex L) :
    (projCoverOpens L i).toScheme ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) :=
  projChart L (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L i.1 i.2.1) i.2.2 (projCoverOpens_le L i)

/-- The charts agree on overlaps `X_s ⊓ X_t = X_{st}`. -/
theorem projCoverChart_compat (i j : ProjCoverIndex L) :
    pullback.fst (projCoverOpens L i).ι (projCoverOpens L j).ι ≫ projCoverChart L i =
      pullback.snd (projCoverOpens L i).ι (projCoverOpens L j).ι ≫ projCoverChart L j := by
  rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf (projCoverOpens L i)
    (projCoverOpens L j)).isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  unfold projCoverChart
  rw [projChart_homOfLE, projChart_homOfLE]
  obtain ⟨d, s, hd⟩ := i
  obtain ⟨e, t, he⟩ := j
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  have ht := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e t
  have hy1 : AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s *
      AlgebraicGeometry.Scheme.Modules.gammaStarOf L e t ∈
      AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (d + e) := SetLike.mul_mem_graded hs ht
  have hy2 : AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s *
      AlgebraicGeometry.Scheme.Modules.gammaStarOf L e t ∈
      AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (e + d) := by
    rw [mul_comm]; exact SetLike.mul_mem_graded ht hs
  have hW : projCoverOpens L ⟨d, s, hd⟩ ⊓ projCoverOpens L ⟨e, t, he⟩ ≤
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (d + e)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s *
            AlgebraicGeometry.Scheme.Modules.gammaStarOf L e t) (d + e)) := by
    rw [nonvanishingLocus_mul L hs ht, gammaStarComponent_gammaStarOf, gammaStarComponent_gammaStarOf]
  have hW' : projCoverOpens L ⟨d, s, hd⟩ ⊓ projCoverOpens L ⟨e, t, he⟩ ≤
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (e + d)).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s *
            AlgebraicGeometry.Scheme.Modules.gammaStarOf L e t) (e + d)) := by
    rw [← nonvanishingLocus_gammaStarComponent_congr L hy1 hy2]; exact hW
  rw [projChart_mul_left L hs hd ht rfl hW, projChart_mul_left L ht he hs (mul_comm _ _) hW']
  rfl

/-- **The canonical morphism `X → Proj Γ_*(X, L)` of Stacks 01PZ**, glued from the charts. -/
def canonicalProjMap : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) :=
  (projCover L hcov).glueMorphisms (projCoverChart L) (projCoverChart_compat L)

/-- On `X_s` the canonical map is the chart. -/
theorem ι_canonicalProjMap (i : ProjCoverIndex L) :
    (projCoverOpens L i).ι ≫ canonicalProjMap L hcov = projCoverChart L i :=
  (projCover L hcov).ι_glueMorphisms (projCoverChart L) (projCoverChart_compat L) i

/-- Transport of the chart along an equality of elements. -/
theorem projChart_congr_elem {x x' : AlgebraicGeometry.Scheme.Modules.gammaStar L} (hxx' : x = x') {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m)
    (hx' : x' ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (hm : 0 < m) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))
    (hU' : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x' m)) :
    projChart L hx hm hU = projChart L hx' hm hU' := by
  subst hxx'; rfl

/-- On any `U ≤ X_x` (`x` homogeneous of positive degree) the canonical map is the chart of `x`. -/
theorem ι_comp_canonicalProjMap {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (hm : 0 < m) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m)) :
    U.ι ≫ canonicalProjMap L hcov = projChart L hx hm hU := by
  let i : ProjCoverIndex L := ⟨m, AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m, hm⟩
  have h1 : U ≤ projCoverOpens L i := hU
  rw [← X.homOfLE_ι h1, Category.assoc, ι_canonicalProjMap, projCoverChart, projChart_homOfLE]
  exact projChart_congr_elem L (gammaStarOf_gammaStarComponent L hx) _ _ _ _ _

/-! ## The two characterizing properties -/

/-- **`f⁻¹(D₊(x)) = X_x`** (Stacks 01PZ (1)). -/
theorem canonicalProjMap_preimage_basicOpen {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (hm : 0 < m) :
    canonicalProjMap L hcov ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨e, he, t, hpt⟩ := hcov p
    let j : ProjCoverIndex L := ⟨e, t, he⟩
    have h1 := congrArg (fun g => g (⟨p, hpt⟩ : (projCoverOpens L j).toScheme)) (ι_canonicalProjMap L hcov j)
    have hp' : (⟨p, hpt⟩ : (projCoverOpens L j).toScheme) ∈ projCoverChart L j ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x := by
      change projCoverChart L j ⟨p, hpt⟩ ∈
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x
      rw [← h1]
      exact hp
    unfold projCoverChart at hp'
    rw [projChart_preimage_basicOpen L _ _ _ hx hm] at hp'
    exact hp'
  · intro p hp
    have h1 := congrArg (fun g => g (⟨p, hp⟩ : ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m)).toScheme))
      (ι_comp_canonicalProjMap L hcov hx hm le_rfl)
    rw [AlgebraicGeometry.Scheme.Hom.mem_preimage]
    have h2 : canonicalProjMap L hcov p = projChart L hx hm le_rfl ⟨p, hp⟩ := h1
    rw [h2]
    exact projChart_apply_mem_basicOpen L hx hm le_rfl _

/-- **The pullback of `a/x^n` along `f` is `a · x^{-n}`** (Stacks 01PZ (2)). -/
theorem canonicalProjMap_appLE_awayToSection {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (hm : 0 < m) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))
    (e : U ≤ canonicalProjMap L hcov ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x)
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) :
    ((canonicalProjMap L hcov).appLE
        (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) U e).hom
        ((AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x).hom z) =
      awayToSections L hx hU z := by
  set V := AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x
  have e' : ⊤ ≤ (U.ι ≫ canonicalProjMap L hcov) ⁻¹ᵁ V := by
    intro q _
    exact e q.2
  have h1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE U.ι (canonicalProjMap L hcov) V U ⊤ e
    U.ι_preimage_self.ge
  have h2 : (U.ι ≫ canonicalProjMap L hcov).appLE V ⊤ e' = (projChart L hx hm hU).appLE V ⊤
      (by rw [← ι_comp_canonicalProjMap L hcov hx hm hU]; exact e') := by
    congr 1
    exact ι_comp_canonicalProjMap L hcov hx hm hU
  have h3 := congrArg (fun φ => φ.hom ((AlgebraicGeometry.Proj.awayToSection _ x).hom z)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE_top_eq_topIso_inv, h2,
    projChart_appLE_awayToSection] at h3
  have h4 := congrArg U.topIso.hom.hom h3
  rw [Iso.inv_hom_id_apply (C := CommRingCat), Iso.inv_hom_id_apply (C := CommRingCat)] at h4
  exact h4

/-! ## The characterization and uniqueness -/

/-- The body of `AlgebraicGeometry.IsAmple.IsCanonicalProjMap` (`Stacks01q1.lean`), verbatim, for a
morphism `f : X ⟶ Proj Γ_*(X, L)`: (1) `f⁻¹(D₊(s)) = X_s`; (2) the pullback `φ` of `a/s^n` satisfies
`φ · s^n = a`. -/
def IsCanonicalProjMap'
    (f : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)) : Prop :=
  ∀ (d : ℕ) (_ : 0 < d) (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤)),
    f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ∧
    ∀ (n : ℕ) (a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d), ⊤)),
      let V := AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)
      let φ : Γ(X, f ⁻¹ᵁ V) := (f.app V).hom
        ((AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).hom
          (HomogeneousLocalization.Away.mk (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s) n
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf L (n • d) a)
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L (n • d) a)))
      φ • ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).presheaf.map
          (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op).hom
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
            (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s ^ n) (n • d)) =
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).presheaf.map
          (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op).hom a

/-- **The glued morphism satisfies the characterization** (Stacks 01PZ). -/
theorem isCanonicalProjMap'_canonicalProjMap : IsCanonicalProjMap' L (canonicalProjMap L hcov) := by
  intro d hd s
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  have h1 := canonicalProjMap_preimage_basicOpen L hcov hs hd
  rw [gammaStarComponent_gammaStarOf] at h1
  refine ⟨h1, fun n a => ?_⟩
  dsimp only
  set W := canonicalProjMap L hcov ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
    (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)
    with hW
  have hU : W ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) d) := by
    rw [gammaStarComponent_gammaStarOf]; exact h1.le
  rw [AlgebraicGeometry.Scheme.Hom.app_eq_appLE, canonicalProjMap_appLE_awayToSection L hcov hs hd hU le_rfl]
  have h2 := awayToSections_mk_smul L hs hU n (AlgebraicGeometry.Scheme.Modules.gammaStarOf L (n • d) a)
    (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L (n • d) a)
  rw [gammaStarComponent_gammaStarOf] at h2
  exact h2

/-- `Away.mk` only depends on the element, not on the membership proof. -/
theorem Away.mk_congr_elem {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {x : A} {d : ℕ} (hx : x ∈ 𝒜 d) (n : ℕ) {a b : A} (hab : a = b)
    (ha : a ∈ 𝒜 (n • d)) (hb : b ∈ 𝒜 (n • d)) :
    HomogeneousLocalization.Away.mk 𝒜 hx n a ha = HomogeneousLocalization.Away.mk 𝒜 hx n b hb := by
  subst hab; rfl

/-- **Uniqueness of the ring map on charts**: a morphism satisfying the characterization pulls
`a/s^n` back to `awayToSections (a/s^n)` on `X_s`. -/
theorem IsCanonicalProjMap'.appLE_awayToSection
    {g : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)}
    (hg : IsCanonicalProjMap' L g) (d : ℕ) (hd : 0 < d)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L d, ⊤))
    (e : (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s ≤ g ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s))
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)) :
    (g.appLE (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s))
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s) e).hom
        ((AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).hom z) =
      awayToSections L (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s)
        (projCoverOpens_le L ⟨d, s, hd⟩) z := by
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  obtain ⟨n, a', ha', rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hs z
  rw [Away.mk_congr_elem _ hs n (gammaStarOf_gammaStarComponent L ha').symm ha'
    (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L (n • d) _)]
  symm
  apply awayToSections_mk_unique
  rw [gammaStarComponent_gammaStarOf]
  have h2 := (hg d hd s).2 n (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a' (n • d))
  dsimp only at h2
  have h3 := congrArg ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n • d)).res e) h2
  rw [res_smul, res_res, res_res] at h3
  exact h3

/-- **Uniqueness of the canonical morphism** (Stacks 01PZ): any `g` satisfying the
characterization equals the glued morphism. -/
theorem eq_canonicalProjMap_of_isCanonicalProjMap'
    {g : X ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)}
    (hg : IsCanonicalProjMap' L g) : g = canonicalProjMap L hcov := by
  refine (projCover L hcov).hom_ext g (canonicalProjMap L hcov) fun i => ?_
  obtain ⟨d, s, hd⟩ := i
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L d s
  have h1 : g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s := (hg d hd s).1
  change (projCoverOpens L ⟨d, s, hd⟩).ι ≫ g = (projCoverOpens L ⟨d, s, hd⟩).ι ≫ canonicalProjMap L hcov
  rw [ι_canonicalProjMap L hcov ⟨d, s, hd⟩]
  -- both morphisms land in the affine open `V = D₊(s)`
  have hrg : Set.range ((projCoverOpens L ⟨d, s, hd⟩).ι ≫ g) ⊆ Set.range
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact (h1.ge q.2 : _)
  have hrχ : Set.range (projCoverChart L ⟨d, s, hd⟩) ⊆ Set.range
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact projChart_apply_mem_basicOpen L hs hd _ q
  have fg := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrg
  have fχ := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrχ
  rw [← fg, ← fχ]
  congr 1
  have : AlgebraicGeometry.IsAffine (AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).toScheme :=
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) _ hs hd
  apply AlgebraicGeometry.ext_of_isAffine
  refine CommRingCat.hom_ext (RingHom.ext fun w => ?_)
  -- write `w = topIso.inv (awayToSection z)`
  obtain ⟨z, hz⟩ : ∃ z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s),
      w = (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).topIso.inv.hom
        ((AlgebraicGeometry.Proj.awayToSection _ _).hom z) := by
    refine ⟨(AlgebraicGeometry.Proj.basicOpenIsoAway (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) _
      hs hd).inv.hom ((AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).topIso.hom.hom w), ?_⟩
    rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom _ _ hs hd, Iso.inv_hom_id_apply (C := CommRingCat),
      Iso.hom_inv_id_apply (C := CommRingCat)]
  rw [hz]
  -- `k.appTop (topIso.inv y) = (k ≫ V.ι).appLE V ⊤ _ y`
  have key : ∀ (k : ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s).toScheme ⟶
        (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).toScheme)
      (h : ((AlgebraicGeometry.Scheme.Modules.tensorPow L d).nonvanishingLocus s).toScheme ⟶
        AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L))
      (hk : k ≫ (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).ι = h)
      (e : ⊤ ≤ h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s))
      (y : Γ(AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L),
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s))),
      k.appTop.hom ((AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).topIso.inv.hom y) =
        (h.appLE (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)) ⊤ e).hom y := by
    intro k h hk e y
    subst hk
    have h' := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE k
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)).ι _ ⊤ ⊤
      (AlgebraicGeometry.Scheme.Opens.ι_preimage_self _).ge (TopologicalSpace.Opens.map_top _).ge
    rw [AlgebraicGeometry.Scheme.Opens.ι_appLE_top_eq_topIso_inv,
      AlgebraicGeometry.Scheme.Hom.appLE_top_top'] at h'
    have h'' := congrArg (fun φ => φ.hom y) h'
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h''
    exact h''
  have e₁ : ⊤ ≤ ((projCoverOpens L ⟨d, s, hd⟩).ι ≫ g) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) :=
    fun q _ => (h1.ge q.2 : _)
  have e₂ : ⊤ ≤ projCoverChart L ⟨d, s, hd⟩ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s) :=
    fun q _ => projChart_apply_mem_basicOpen L hs hd _ q
  rw [key _ _ fg e₁, key _ _ fχ e₂]
  -- left: `g`; right: the chart
  have hl := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (projCoverOpens L ⟨d, s, hd⟩).ι g
    (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L d s)) _ ⊤ h1.ge
    (AlgebraicGeometry.Scheme.Opens.ι_preimage_self _).ge
  have hl' := congrArg (fun φ => φ.hom ((AlgebraicGeometry.Proj.awayToSection _ _).hom z)) hl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hl'
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE_top_eq_topIso_inv,
    IsCanonicalProjMap'.appLE_awayToSection L hg d hd s h1.ge] at hl'
  have hr := projChart_appLE_awayToSection L hs hd (projCoverOpens_le L ⟨d, s, hd⟩) e₂ z
  exact hl'.symm.trans hr.symm

end AlgebraicGeometry.Scheme.Modules

end
