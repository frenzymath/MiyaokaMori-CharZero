import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.GammaStarAwayRingHom
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01q1_FrameChartBasicOpen

/-! # The charts of the canonical morphism to `Proj Γ_*(X, L)`

**The charts `X_x → D₊(x) ⊆ Proj Γ_*(X, L)` of Stacks 01PZ.**

For a homogeneous `x ∈ Γ_*(X, L)_m` of positive degree and an open `U ≤ X_{x_m}`, the chart is

  `chart L hx hm hU : U ⟶ Proj 𝒜 := U.toSpecΓ ≫ Spec.map (awayToSections L hx hU) ≫ Proj.awayι 𝒜 x`,

i.e. `U → Spec Γ(U, O_X) → Spec Γ_*(X, L)_{(x)} ≅ D₊(x) ⊆ Proj 𝒜` (Stacks 01PZ: "the morphism
`X_s → D₊(s) = Spec S_{(s)}` corresponding to the ring map `S_{(s)} → Γ(X_s, O_X)`").

Facts proved here:
* `chart_homOfLE`: restricting the chart to `U' ≤ U` gives the chart of `U'`;
* `chart_mul_left`: on `U' ≤ X_{(xt)}` the chart of `x` equals the chart of `x * t` (the two charts
  are compatible on overlaps: `X_x ∩ X_t = X_{xt}`, and `Spec Γ_*(X,L)_{(x)} ⊇ Spec Γ_*(X,L)_{(xt)}` via
  `awayMap`, `Proj.SpecMap_awayMap_awayι`);
* `chart_appLE_awayToSection`: the pullback of the function `a/x^n ∈ Γ(D₊(x), O)` along the chart
  is `awayToSections (a/x^n)` (transported to `Γ(U, ⊤)`) — this is the characterization (2) of the
  canonical map in `IsAmple.IsCanonicalProjMap`;
* `chart_preimage_basicOpen`: `chart⁻¹(D₊(y)) = U ∩ X_y` for homogeneous `y` of positive degree
  (Stacks 01PZ: `f⁻¹(D₊(s)) = X_s`), computed through `Proj.awayι_preimage_basicOpen`
  (`awayι⁻¹ D₊(y) = D(y^m / x^e)`) and the chart description `U ⊓ X_σ = D(coord(σ))`
  (`IsFrame.inf_nonvanishingLocus_eq_basicOpen`).

Source: Stacks 01PZ (`properties-lemma-map-into-proj`), construction of the map `X_s → D₊(s)` and the
statements `f⁻¹(D₊(s)) = X_s`, `Γ(D₊(s), O) = S_{(s)} → Γ(X_s, O_X)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-! ## Generic `appLE` helpers -/

/-- `f.appLE ⊤ ⊤ _ = f.appTop`. -/
theorem Scheme.Hom.appLE_top_top' {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  (f.app_eq_appLE (U := ⊤)).symm

/-- `U.ι.appLE U ⊤ _` is `U.topIso.inv` (the two morphisms `op U ⟶ op (U.ι ''ᵁ ⊤)` in the thin
category `Opens X` agree). -/
theorem Scheme.Opens.ι_appLE_top_eq_topIso_inv {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
    (e : ⊤ ≤ U.ι ⁻¹ᵁ U) :
    U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
  congr 1

/-- The pullback of `a/x^n ∈ Γ(D₊(x), O)` along `awayι : Spec (A_x)₀ → Proj A` is `a/x^n` itself
(through `ΓSpecIso`). -/
theorem Proj.awayι_appLE_awayToSection {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {x : A} {m : ℕ} (hx : x ∈ 𝒜 m) (hm : 0 < m)
    (e : ⊤ ≤ AlgebraicGeometry.Proj.awayι 𝒜 x hx hm ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 x)
    (z : HomogeneousLocalization.Away 𝒜 x) :
    ((AlgebraicGeometry.Proj.awayι 𝒜 x hx hm).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 x) ⊤ e).hom
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 x).hom z) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 x))).inv.hom z := by
  set V := AlgebraicGeometry.Proj.basicOpen 𝒜 x
  have h2 : (AlgebraicGeometry.Proj.awayι 𝒜 x hx hm).appLE V ⊤ e =
      V.ι.appLE V ⊤ V.ι_preimage_self.ge ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).inv.appLE ⊤ ⊤
          (TopologicalSpace.Opens.map_top _).ge :=
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).inv V.ι V ⊤ ⊤ V.ι_preimage_self.ge
      (TopologicalSpace.Opens.map_top _).ge).symm
  rw [h2, AlgebraicGeometry.Scheme.Opens.ι_appLE_top_eq_topIso_inv,
    AlgebraicGeometry.Scheme.Hom.appLE_top_top']
  have h3 : (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).hom.appTop =
      (AlgebraicGeometry.Scheme.ΓSpecIso _).hom ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 x ≫
        V.topIso.inv := by
    have h := AlgebraicGeometry.Proj.basicOpenToSpec_app_top 𝒜 x
    rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_hom 𝒜 x hx hm] at h
    exact h
  -- `awayToSection ≫ topIso.inv = ΓSpecIso.inv ≫ hom.appTop`
  have h4 : AlgebraicGeometry.Proj.awayToSection 𝒜 x ≫ V.topIso.inv =
      (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).hom.appTop := by
    rw [h3]
    exact (Iso.inv_hom_id_assoc _ _).symm
  have h5 : (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).hom.appTop ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).inv.appTop = 𝟙 _ := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, Iso.inv_hom_id,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  have h6 := congrArg (fun φ => φ.hom z) (h4 =≫
    (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 x hx hm).inv.appTop)
  simp only [Category.assoc, h5, Category.comp_id, CommRingCat.hom_comp, RingHom.comp_apply] at h6
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact h6

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]

/-! ## The charts -/

section

variable {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
  (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m) (hm : 0 < m) {U : X.Opens}
  (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m))

/-- **The chart of Stacks 01PZ**: `U → Spec Γ(U, O) → Spec Γ_*(X, L)_{(x)} = D₊(x) ⊆ Proj Γ_*(X, L)`. -/
def projChart : U.toScheme ⟶ AlgebraicGeometry.Proj (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections L hx hU)) ≫
    AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x hx hm

/-- The chart does not depend on the degree witness. -/
theorem projChart_congr {m' : ℕ} (hx' : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m')
    (hm' : 0 < m') (hU' : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m').nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m')) :
    projChart L hx hm hU = projChart L hx' hm' hU' := rfl

/-- Restricting the chart to `U' ≤ U` gives the chart of `U'`. -/
theorem projChart_homOfLE {U' : X.Opens} (h : U' ≤ U) :
    X.homOfLE h ≫ projChart L hx hm hU = projChart L hx hm (h.trans hU) := by
  unfold projChart
  rw [← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  congr 3
  ext z
  exact awayToSections_res L hx hU h z

/-- The chart of `x` on `U' ≤ X_{xt}` is the chart of `x * t`. -/
theorem projChart_mul_left {t : AlgebraicGeometry.Scheme.Modules.gammaStar L} {e : ℕ}
    (ht : t ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L e)
    {y : AlgebraicGeometry.Scheme.Modules.gammaStar L} (hy : y = x * t) {U' : X.Opens}
    (hU' : U' ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + e)).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y (m + e)))
    (hU'x : U' ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m)) :
    projChart L hx hm hU'x =
      projChart L (hy ▸ SetLike.mul_mem_graded hx ht) (hm.trans_le (m.le_add_right e)) hU' := by
  unfold projChart
  rw [← AlgebraicGeometry.Proj.SpecMap_awayMap_awayι
    (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) hx hm ht hy, ← Spec.map_comp_assoc]
  congr 3
  ext z
  exact (awayToSections_awayMap L hx ht hy hU' hU'x z).symm

/-- **The pullback of `a/x^n` along the chart** (characterization (2) of the canonical map). -/
theorem projChart_appLE_awayToSection
    (e : ⊤ ≤ projChart L hx hm hU ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x)
    (z : HomogeneousLocalization.Away (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) :
    ((projChart L hx hm hU).appLE
        (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) ⊤ e).hom
        ((AlgebraicGeometry.Proj.awayToSection (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x).hom z) =
      U.topIso.inv.hom (awayToSections L hx hU z) := by
  have hV : ⊤ ≤ AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x hx hm ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x := by
    intro p _
    change _ ∈ AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x
    rw [← AlgebraicGeometry.Proj.opensRange_awayι _ x hx hm]
    exact ⟨p, rfl⟩
  have h2 : (projChart L hx hm hU).appLE
      (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) ⊤ e =
      (AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x hx hm).appLE
          (AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x) ⊤ hV ≫
        (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections L hx hU))).appLE ⊤ ⊤
          (TopologicalSpace.Opens.map_top _).ge :=
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
      (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections L hx hU)))
      (AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x hx hm)
      _ ⊤ ⊤ hV (TopologicalSpace.Opens.map_top _).ge).symm
  rw [h2, AlgebraicGeometry.Scheme.Hom.appLE_top_top', CommRingCat.hom_comp, RingHom.comp_apply,
    AlgebraicGeometry.Proj.awayι_appLE_awayToSection]
  have h3 : (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections L hx hU))).appTop =
      (Spec.map (CommRingCat.ofHom (awayToSections L hx hU))).appTop ≫ U.toSpecΓ.appTop :=
    rfl
  rw [h3, CommRingCat.hom_comp, RingHom.comp_apply]
  have h4 := congrArg (fun φ => φ.hom z)
    (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (awayToSections L hx hU)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4
  rw [← h4, AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

/-- The chart lands in `D₊(x)`. -/
theorem projChart_apply_mem_basicOpen (p : U.toScheme) :
    projChart L hx hm hU p ∈ AlgebraicGeometry.Proj.basicOpen
      (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) x := by
  rw [← AlgebraicGeometry.Proj.opensRange_awayι _ x hx hm]
  exact ⟨(U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections L hx hU))) p, rfl⟩

/-- `Spec.map φ ⁻¹ᵁ D(r) = D(φ r)`. -/
theorem SpecMap_preimage_primeSpectrum_basicOpen {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    Spec.map φ ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (φ.hom r) := by
  rw [← AlgebraicGeometry.basicOpen_eq_of_affine, AlgebraicGeometry.Scheme.preimage_basicOpen,
    ← AlgebraicGeometry.basicOpen_eq_of_affine]
  congr 1
  have h := congrArg (fun ψ => ψ.hom r) (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

/-- **`chart⁻¹(D₊(y)) = U ⊓ X_y`** for homogeneous `y` of positive degree `e` (Stacks 01PZ,
`f⁻¹(D₊(s)) = X_s`). -/
theorem projChart_preimage_basicOpen {y : AlgebraicGeometry.Scheme.Modules.gammaStar L} {e : ℕ}
    (hy : y ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L e) (he : 0 < e) :
    projChart L hx hm hU ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L) y =
      U.ι ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L y e) := by
  unfold projChart
  rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Hom.comp_preimage,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen _ hx hm hy he,
    SpecMap_preimage_primeSpectrum_basicOpen, AlgebraicGeometry.Scheme.Opens.toSpecΓ_preimage_basicOpen]
  -- `X.basicOpen (ψ (y^m / x^e)) = U ⊓ X_{y^m}` and `X_{y^m} = X_y`
  have hfr := isFrame_res_pow L hx hU e
  show U.ι ⁻¹ᵁ X.basicOpen (hfr.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensorPow L (e • m)).res le_top
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L (y ^ m) (e • m)))) = _
  rw [← IsFrame.inf_nonvanishingLocus_eq_basicOpen _ _ hfr,
    nonvanishingLocus_gammaStarComponent_congr L
      (show y ^ m ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (e • m) by
        rw [smul_eq_mul, mul_comm, ← smul_eq_mul]; exact SetLike.pow_mem_graded m hy)
      (SetLike.pow_mem_graded m hy),
    nonvanishingLocus_pow L hy hm]
  apply TopologicalSpace.Opens.ext
  ext p
  exact ⟨fun h => h.2, fun h => ⟨p.2, h⟩⟩

end

end AlgebraicGeometry.Scheme.Modules

end
