import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByCoeff

/-! # The universal based jet `J ×_k D_r ⟶ Z`

The universal based jet of `J = J_r^s(Z/C)` is glued from the charts: on `pr⁻¹J_U` it is
`toSpecΓ ≫ Spec (universalJetSections U) ≫ (π⁻¹U).fromSpec`. This module proves

* `universalJet_piece_restrict`, `universalJet_glue_compat`: the pieces are compatible with restriction to a
  basic open `V ⊆ U` (coefficientwise: `universalJetSections_restrict`), hence on all pairwise intersections
  (`affinePreimageCover.glue_compat`, the cover `{pr⁻¹J_U}` being the preimage cover of `pr ≫ (J ⟶ C)`);
* `universalJet`, `ι_universalJet`;
* `universalJet_comp_hom`: `universalJet ≫ Z.hom = pr ≫ (J ⟶ C)` (the jet lies over `C`), checked on each
  `pr⁻¹J_U` where both sides factor through `Spec Γ(C, U)` with comodule maps
  `π^♯ ≫ universalJetSections U = coefficientMap ≫ chartSections ≫ pr^♯` (`universalJetSections_algebraMap`);
* `universalJet_appLE`: `universalJet^♯ = universalJetSections U` on the chart;
* `jetConstantTerm_comp_universalJet`: `ct ≫ universalJet = (J ⟶ C) ≫ s` (the jet is based at `s`), checked on
  each `J_U` where both sides factor through `Spec Γ(Z, π⁻¹U)` with comodule maps
  `universalJetSections U ≫ ct^♯ = ε_U ≫ coefficientMap ≫ chartSections` (`jetConstantTerm_appLE_universalJetSections`).

References: §2 of the paper (the based relative jet scheme); Ein–Mustață, Prop. 2.2 (the universal jet).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
-- `U.1` for `U : C.AffineZariskiSite` and the cover index `𝒰.I₀` make `rw` motives fail to typecheck under the
-- strict transparency check (Mathlib disables it around `AffineZariskiSite` / locally directed covers too).
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open relativeJetScheme.Charts

noncomputable section

section UniversalJet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- `pr⁻¹J_U` is the preimage of `U` under `pr ≫ (J ⟶ C)`. -/
theorem relativeJetScheme.proj_preimage_chartOpen (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U =
      (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1 := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, relativeJetScheme.hom_preimage_chartOpen]

/-- The piece of the universal jet on `pr⁻¹J_U`. -/
noncomputable def relativeJetScheme.universalJetPiece (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U).toScheme ⟶ Z.left :=
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
      relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
    (U.2.preimage Z.hom).fromSpec

/-- The pieces of the universal jet are compatible with restriction to a basic open `V ⊆ U`:
both sides are `toSpecΓ ≫ Spec.map (-) ≫ (π⁻¹U).fromSpec`, and the comodule maps agree by
`universalJetSections_restrict`. -/
theorem relativeJetScheme.universalJet_piece_restrict {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).homOfLE
        (AlgebraicGeometry.Scheme.affinePreimageCover.le_of_hom
          (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
            (relativeJetScheme (k := k) Z s hs r).hom)
          (fun U : C.AffineZariskiSite =>
            jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
              relativeJetScheme.chartOpen (k := k) Z s hs r U)
          (relativeJetScheme.proj_preimage_chartOpen (k := k) Z s hs r) f) ≫
        relativeJetScheme.universalJetPiece (k := k) Z s hs r U =
      relativeJetScheme.universalJetPiece (k := k) Z s hs r V := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hZ : Z.hom ⁻¹ᵁ V.1 ≤ Z.hom ⁻¹ᵁ U.1 :=
    (TopologicalSpace.Opens.map Z.hom.base).monotone
      (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le)
  unfold relativeJetScheme.universalJetPiece
  rw [← CategoryTheory.Category.assoc, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    ← AlgebraicGeometry.IsAffineOpen.map_fromSpec (U.2.preimage Z.hom) (V.2.preimage Z.hom)
      (CategoryTheory.homOfLE hZ).op,
    CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc (AlgebraicGeometry.Spec.map _),
    ← AlgebraicGeometry.Spec.map_comp, ← CategoryTheory.Category.assoc (AlgebraicGeometry.Spec.map _),
    ← AlgebraicGeometry.Spec.map_comp]
  congr 3
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact relativeJetScheme.universalJetSections_restrict (k := k) Z s hs r f b

/-- The gluing condition for `universalJet`: the morphisms given by `universalJetSections` on the `pr⁻¹J_U` agree
on `pr⁻¹J_U ∩ pr⁻¹J_U'`. Proof: `{pr⁻¹J_U}` is the preimage cover under `pr ≫ (J → C)` of the affine opens of
`C`, which is locally directed (`affinePreimageCover.glue_compat`), so it suffices to check compatibility with
restriction to basic opens `V ⊆ U` (`universalJet_piece_restrict`). -/
theorem relativeJetScheme.universalJet_glue_compat :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    ∀ U U' : C.AffineZariskiSite,
      CategoryTheory.Limits.pullback.fst
          (((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover _
            (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).f U)
          (((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover _
            (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).f U') ≫
        ((jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
        (U.2.preimage Z.hom).fromSpec) =
      CategoryTheory.Limits.pullback.snd
          (((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover _
            (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).f U)
          (((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover _
            (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).f U') ≫
        ((jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U').toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U')) ≫
        (U'.2.preimage Z.hom).fromSpec) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact AlgebraicGeometry.Scheme.affinePreimageCover.glue_compat
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
      (relativeJetScheme (k := k) Z s hs r).hom)
    (fun U : C.AffineZariskiSite =>
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (relativeJetScheme.proj_preimage_chartOpen (k := k) Z s hs r)
    (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)
    (relativeJetScheme.universalJetPiece (k := k) Z s hs r)
    (fun f => relativeJetScheme.universalJet_piece_restrict (k := k) Z s hs r f)

/-- The universal based jet `J ×_k D_r → Z`: on the open cover `{pr⁻¹J_U}` it is given by `universalJetSections`
as a morphism into the affine open `π⁻¹U = Spec B_U`, and these are glued (compatibility on overlaps is
`universalJet_glue_compat`). -/

noncomputable def relativeJetScheme.universalJet :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⟶ Z.left :=
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover
      (fun U : C.AffineZariskiSite =>
        jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).glueMorphisms
    (fun U =>
      (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
        (U.2.preimage Z.hom).fromSpec)
    (relativeJetScheme.universalJet_glue_compat (k := k) Z s hs r)

/-- The universal jet restricted to `pr⁻¹J_U` is the piece `toSpecΓ ≫ Spec (universalJetSections U) ≫ fromSpec`. -/
theorem relativeJetScheme.ι_universalJet (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U).ι ≫
      relativeJetScheme.universalJet (k := k) Z s hs r =
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
      (U.2.preimage Z.hom).fromSpec := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
    ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover
      (fun U : C.AffineZariskiSite =>
        jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U)
      (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)) _ _ U

/-- `universalJet ≫ Z.hom = pr ≫ (J ⟶ C)` on the chart `pr⁻¹J_U`: both sides factor through `Spec Γ(C, U)`,
with comodule maps `π^♯ ≫ universalJetSections U` and `coefficientMap ≫ chartSections ≫ pr^♯`
(`universalJetSections_algebraMap`). -/
theorem relativeJetScheme.ι_universalJet_comp_hom (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U).ι ≫
      relativeJetScheme.universalJet (k := k) Z s hs r ≫ Z.hom =
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U).ι ≫
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        (relativeJetScheme (k := k) Z s hs r).hom := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  rw [← CategoryTheory.Category.assoc, relativeJetScheme.ι_universalJet,
    ← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι_assoc (jetThickeningProj (k := k) r _)
      (U := relativeJetScheme.chartOpen (k := k) Z s hs r U) le_rfl,
    relativeJetScheme.chartOpen_ι_eq]
  simp only [CategoryTheory.Category.assoc]
  rw [relativeJetScheme.chart_comp_hom, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    ← AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec Z.hom U.2 (U.2.preimage Z.hom) le_rfl]
  congr 1
  rw [← AlgebraicGeometry.Spec.map_comp_assoc, ← AlgebraicGeometry.Spec.map_comp_assoc,
    ← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app, AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  exact relativeJetScheme.universalJetSections_algebraMap (k := k) Z s hs r U a

/-- The universal jet lies over `C`: `universalJet ≫ Z.hom = pr ≫ (J ⟶ C)`. -/
theorem relativeJetScheme.universalJet_comp_hom :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    relativeJetScheme.universalJet (k := k) Z s hs r ≫ Z.hom =
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        (relativeJetScheme (k := k) Z s hs r).hom := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover
    (fun U : C.AffineZariskiSite =>
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r)).hom_ext _ _
    (fun U => relativeJetScheme.ι_universalJet_comp_hom (k := k) Z s hs r U)

/-- `pr⁻¹J_U ≤ universalJet⁻¹(π⁻¹U)`. -/
theorem relativeJetScheme.universalJet_preimage_le (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U ≤
      relativeJetScheme.universalJet (k := k) Z s hs r ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  rw [relativeJetScheme.proj_preimage_chartOpen, ← relativeJetScheme.universalJet_comp_hom,
    AlgebraicGeometry.Scheme.Hom.comp_preimage]

/-- `universalJet^♯` on the chart `U` is `universalJetSections U`. -/
theorem relativeJetScheme.universalJet_appLE_chartOpen (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (relativeJetScheme.universalJet (k := k) Z s hs r).appLE (Z.hom ⁻¹ᵁ U.1)
        (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.universalJet_preimage_le (k := k) Z s hs r U) =
      CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact AlgebraicGeometry.Scheme.Hom.appLE_eq_of_ι_comp_fromSpec _ (U.2.preimage Z.hom) _ _
    (relativeJetScheme.ι_universalJet (k := k) Z s hs r U) _

/-- `ct ≫ universalJet = (J ⟶ C) ≫ s` on the chart `J_U`: both sides factor through `Spec Γ(Z, π⁻¹U)`,
with comodule maps `universalJetSections U ≫ ct^♯` and `ε_U ≫ coefficientMap ≫ chartSections`
(`jetConstantTerm_appLE_universalJetSections`). -/
theorem relativeJetScheme.ι_jetConstantTerm_comp_universalJet (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (relativeJetScheme.chartOpen (k := k) Z s hs r U).ι ≫
      jetConstantTerm (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        relativeJetScheme.universalJet (k := k) Z s hs r =
    (relativeJetScheme.chartOpen (k := k) Z s hs r U).ι ≫ (relativeJetScheme (k := k) Z s hs r).hom ≫ s := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  rw [← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι_assoc (jetConstantTerm (k := k) r _)
      (jetConstantTerm_le (k := k) r _ (relativeJetScheme.chartOpen (k := k) Z s hs r U)),
    relativeJetScheme.ι_universalJet, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    relativeJetScheme.chartOpen_ι_eq]
  simp only [CategoryTheory.Category.assoc]
  rw [← CategoryTheory.Category.assoc (relativeJetScheme.chart (k := k) Z s hs r U),
    relativeJetScheme.chart_comp_hom, CategoryTheory.Category.assoc,
    ← AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec s (U.2.preimage Z.hom) U.2
      (relativeJetScheme.section_preimage_le Z s hs U.1)]
  congr 1
  rw [← AlgebraicGeometry.Spec.map_comp_assoc, ← AlgebraicGeometry.Spec.map_comp_assoc,
    ← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  exact relativeJetScheme.jetConstantTerm_appLE_universalJetSections (k := k) Z s hs r U b

/-- The universal jet is based at `s`: `ct ≫ universalJet = (J ⟶ C) ≫ s`. -/
theorem relativeJetScheme.jetConstantTerm_comp_universalJet_eq :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetConstantTerm (k := k) r (relativeJetScheme (k := k) Z s hs r).left ≫
        relativeJetScheme.universalJet (k := k) Z s hs r =
      (relativeJetScheme (k := k) Z s hs r).hom ≫ s := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact ((relativeJetScheme (k := k) Z s hs r).left.openCoverOfIsOpenCover
    (fun U : C.AffineZariskiSite => relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (relativeJetScheme.chartOpen_isOpenCover (k := k) Z s hs r)).hom_ext _ _
    (fun U => relativeJetScheme.ι_jetConstantTerm_comp_universalJet (k := k) Z s hs r U)

end UniversalJet

end
