import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickeningSections
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBySchemeLemmas
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # Charts of the relative based jet scheme

The chart data of the glued based jet scheme `J = J_r^s(Z/C)`:
the image `J_U` of the chart `Spec J_r(B_U, ε_U) ⟶ J` (`chartOpen`), the identification of the chart ring with
`Γ(J, J_U)` (`chartSections`), the comodule map of the universal based jet on the chart (`universalJetSections`),
and the lemmas relating them to the gluing data:

* `chart_comp_map`: the chart of a basic open `V ⊆ U` is the chart of `U` precomposed with `Spec` of the
  transition map `J_r(B_U, ε_U) → J_r(B_V, ε_V)` (`colimit.w`);
* `chart_comp_hom`: chart `≫` structure map `J ⟶ C` is `Spec (Γ(C,U) → J_r(B_U,ε_U)) ≫ U.fromSpec` (`ι_toBase`);
* `hom_preimage_chartOpen`: `J_U` is the preimage of `U` (`toBase_preimage_eq_opensRange_ι`);
* `chartOpen_toSpecΓ_SpecMap_chartSections`, `chartSections_comp_map`, `hom_appLE_chartOpen`: the characterisation
  and naturality of `chartSections`, and `(J ⟶ C)^♯` on `J_U` in terms of the coefficient map.

Source: §2 of the paper (the based relative jet scheme); Ein–Mustață Prop. 2.2 and Lemma 2.3 in relative form.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The image (an open set) of the chart `Spec J_r(B_U, ε_U) ↪ J`. -/

noncomputable def relativeJetScheme.chartOpen {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (U : C.AffineZariskiSite) : (relativeJetScheme (k := k) Z s hs r).left.Opens :=
  ((relativeJetScheme.gluingData Z s hs r).cover.f U).opensRange

/-- Chart ring `→ Γ(J, chart image)`: the open immersion gives `Spec F_U ≅ image`; take global sections. -/

noncomputable def relativeJetScheme.chartSections {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (U : C.AffineZariskiSite) :
    relativeJetScheme.chartRing Z s hs r U.1 ⟶
      Γ((relativeJetScheme (k := k) Z s hs r).left, relativeJetScheme.chartOpen (k := k) Z s hs r U) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫
    ((relativeJetScheme.gluingData Z s hs r).cover.f U).isoOpensRange.inv.appTop ≫
    (relativeJetScheme.chartOpen (k := k) Z s hs r U).topIso.hom

/-- The comorphism of the universal based jet on the chart `U`: `B_U → F_U[t]/(t^{r+1})` (the algebraic universal
jet) `→ Γ(J, J_U)[t]/(t^{r+1}) → Γ(J ×_k D_r, pr⁻¹ J_U)`. -/

noncomputable def relativeJetScheme.universalJetSections {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    Γ(Z.left, Z.hom ⁻¹ᵁ U.1) →+*
      Γ(jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left,
        jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U) :=
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  ((jetThickening.sectionsHom (k := k) r (relativeJetScheme (k := k) Z s hs r).left
      (relativeJetScheme.chartOpen (k := k) Z s hs r U)).comp
    (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (relativeJetScheme.chartSections (k := k) Z s hs r U).hom)).comp
    (BasedJetAlgebra.universalJet (relativeJetScheme.augmentation Z s hs U.1) r).toRingHom

/-- The chart images `{J_U}` cover `J` (the cover of the gluing data). -/

theorem relativeJetScheme.chartOpen_isOpenCover {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    TopologicalSpace.IsOpenCover (fun U : C.AffineZariskiSite =>
      relativeJetScheme.chartOpen (k := k) Z s hs r U) :=
  (relativeJetScheme.gluingData Z s hs r).cover.isOpenCover_opensRange

/-- A proof obligation of `universalJet`: `{pr⁻¹ J_U}` covers `J ×_k D_r` (preimage of `chartOpen_isOpenCover`
along `pr`). -/

theorem relativeJetScheme.universalJet_isOpenCover {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    TopologicalSpace.IsOpenCover (fun U : C.AffineZariskiSite =>
      jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U) :=
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  (relativeJetScheme.chartOpen_isOpenCover (k := k) Z s hs r).comap
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left).base.1

/-! ## The charts and the gluing data -/

section ChartLemmas

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- The chart `Spec J_r(B_U, ε_U) ⟶ J` of `U`, typed as a morphism out of `Spec` of the chart ring
(definitionally `(gluingData Z s hs r).cover.f U`; the explicit source lets instance search see the ring). -/
abbrev relativeJetScheme.chart (U : C.AffineZariskiSite) :
    AlgebraicGeometry.Spec (relativeJetScheme.chartRing Z s hs r U.1) ⟶ (relativeJetScheme (k := k) Z s hs r).left :=
  (relativeJetScheme.gluingData Z s hs r).cover.f U

namespace relativeJetScheme.Charts

/-- The chart is an open immersion, stated for `chart` (source `Spec` of the chart ring) so that instance search
finds it (`relativeJetScheme.chart_isOpenImmersion` is keyed on the source `d.functor.obj U`, which is only
definitionally `Spec …`). A *scoped* instance: it is inert unless `relativeJetScheme.Charts` is opened, so it
does not change instance search anywhere else. -/
scoped instance chart_isOpenImmersion (U : C.AffineZariskiSite) :
    AlgebraicGeometry.IsOpenImmersion (relativeJetScheme.chart (k := k) Z s hs r U) :=
  relativeJetScheme.chart_isOpenImmersion Z s hs r U

end relativeJetScheme.Charts

open relativeJetScheme.Charts

/-- The chart of a basic open `V ⊆ U` is the chart of `U` precomposed with `Spec` of the transition map
(`colimit.w` for the gluing diagram). -/
theorem relativeJetScheme.chart_comp_map {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    AlgebraicGeometry.Spec.map ((relativeJetScheme.chartFunctor Z s hs r).map f.op) ≫
        relativeJetScheme.chart (k := k) Z s hs r U =
      relativeJetScheme.chart (k := k) Z s hs r V := by
  haveI : ((relativeJetScheme.gluingData Z s hs r).functor ⋙ AlgebraicGeometry.Scheme.forget).IsLocallyDirected :=
    AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  exact CategoryTheory.Limits.colimit.w (relativeJetScheme.gluingData Z s hs r).functor f

/-- The structure map of `J` is the gluing's `toBase`. -/
theorem relativeJetScheme.hom_eq :
    (relativeJetScheme (k := k) Z s hs r).hom = (relativeJetScheme.gluingData Z s hs r).toBase := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Chart `≫` structure map `= Spec (coefficient map) ≫ U.fromSpec` (`ι_toBase` of the relative gluing). -/
theorem relativeJetScheme.chart_comp_hom (U : C.AffineZariskiSite) :
    relativeJetScheme.chart (k := k) Z s hs r U ≫ (relativeJetScheme (k := k) Z s hs r).hom =
      AlgebraicGeometry.Spec.map ((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)) ≫
        U.2.fromSpec := by
  have h := AlgebraicGeometry.Scheme.Cover.RelativeGluingData.ι_toBase
    (relativeJetScheme.gluingData Z s hs r) U
  rw [relativeJetScheme.hom_eq]
  refine h.trans ?_
  show (AlgebraicGeometry.Spec.map ((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)) ≫
      (AlgebraicGeometry.Scheme.AffineZariskiSite.restrictIsoSpec C).inv.app U) ≫ U.1.ι = _
  rw [AlgebraicGeometry.Scheme.AffineZariskiSite.restrictIsoSpec_inv_app, CategoryTheory.Category.assoc,
    AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι]

/-- The chart image is the preimage of `U`: `J_r^s(Z/C)` is glued relatively from `{Spec J_r(B_U, ε_U)}_U` along the
affine opens of `C`, and the `U`-th piece is exactly `toBase⁻¹(U)`
(Mathlib `Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`).
(Same statement as `relativeJetScheme.preimage_eq_chartOpen` of `OfBasedJetChartSections`, which lives
downstream of this module.) -/
theorem relativeJetScheme.hom_preimage_chartOpen (U : C.AffineZariskiSite) :
    (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1 = relativeJetScheme.chartOpen (k := k) Z s hs r U := by
  have h := AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι
    (relativeJetScheme.gluingData Z s hs r) U
  have hU : ((AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover C).f U).opensRange = U.1 :=
    AlgebraicGeometry.Scheme.Opens.opensRange_ι U.1
  rw [hU] at h
  exact h

/-- `J_V ⊆ J_U` for a basic open `V ⊆ U`. -/
theorem relativeJetScheme.chartOpen_mono {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    relativeJetScheme.chartOpen (k := k) Z s hs r V ≤ relativeJetScheme.chartOpen (k := k) Z s hs r U := by
  rw [← relativeJetScheme.hom_preimage_chartOpen, ← relativeJetScheme.hom_preimage_chartOpen]
  exact (TopologicalSpace.Opens.map _).monotone
    (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le)

/-- `chartSections` is the general `chartSec` of the chart. -/
theorem relativeJetScheme.chartSections_eq (U : C.AffineZariskiSite) :
    relativeJetScheme.chartSections (k := k) Z s hs r U =
      AlgebraicGeometry.Scheme.chartSec (relativeJetScheme.chart (k := k) Z s hs r U) := rfl

/-- Characterisation of `chartSections`: `J_U.toSpecΓ ≫ Spec.map (chartSections U) = (chart U).isoOpensRange.inv`. -/
theorem relativeJetScheme.chartOpen_toSpecΓ_SpecMap_chartSections (U : C.AffineZariskiSite) :
    (relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.chartSections (k := k) Z s hs r U) =
      (relativeJetScheme.chart (k := k) Z s hs r U).isoOpensRange.inv :=
  AlgebraicGeometry.Scheme.opensRange_toSpecΓ_SpecMap_chartSec (relativeJetScheme.chart (k := k) Z s hs r U)

/-- `J_U.ι = J_U.toSpecΓ ≫ Spec.map (chartSections U) ≫ chart U`. -/
theorem relativeJetScheme.chartOpen_ι_eq (U : C.AffineZariskiSite) :
    (relativeJetScheme.chartOpen (k := k) Z s hs r U).ι =
      (relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.chartSections (k := k) Z s hs r U) ≫
        relativeJetScheme.chart (k := k) Z s hs r U :=
  (AlgebraicGeometry.Scheme.opensRange_toSpecΓ_SpecMap_chartSec_comp
    (relativeJetScheme.chart (k := k) Z s hs r U)).symm

/-- Naturality of `chartSections`: restricting from `J_U` to `J_V` is the transition map followed by
`chartSections V`. -/
theorem relativeJetScheme.chartSections_comp_map {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    relativeJetScheme.chartSections (k := k) Z s hs r U ≫
        (relativeJetScheme (k := k) Z s hs r).left.presheaf.map
          (CategoryTheory.homOfLE (relativeJetScheme.chartOpen_mono (k := k) Z s hs r f)).op =
      (relativeJetScheme.chartFunctor Z s hs r).map f.op ≫
        relativeJetScheme.chartSections (k := k) Z s hs r V :=
  AlgebraicGeometry.Scheme.chartSec_comp_map (relativeJetScheme.chart (k := k) Z s hs r U)
    (relativeJetScheme.chart (k := k) Z s hs r V) _ (relativeJetScheme.chart_comp_map (k := k) Z s hs r f) _

/-- Pointwise form of `chartSections_comp_map`. -/
theorem relativeJetScheme.chartSections_map_apply {U V : C.AffineZariskiSite} (f : V ⟶ U)
    (x : relativeJetScheme.chartRing Z s hs r U.1) :
    ((relativeJetScheme (k := k) Z s hs r).left.presheaf.map
        (CategoryTheory.homOfLE (relativeJetScheme.chartOpen_mono (k := k) Z s hs r f)).op).hom
      ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom x) =
    (relativeJetScheme.chartSections (k := k) Z s hs r V).hom
      (((relativeJetScheme.chartFunctor Z s hs r).map f.op).hom x) :=
  congrArg (fun φ : relativeJetScheme.chartRing Z s hs r U.1 ⟶
      Γ((relativeJetScheme (k := k) Z s hs r).left, relativeJetScheme.chartOpen (k := k) Z s hs r V) =>
      φ.hom x) (relativeJetScheme.chartSections_comp_map (k := k) Z s hs r f)

set_option backward.isDefEq.respectTransparency false in
/-- `(J ⟶ C)^♯` on the chart `J_U` is the coefficient map followed by `chartSections`. -/
theorem relativeJetScheme.hom_appLE_chartOpen (U : C.AffineZariskiSite) :
    (relativeJetScheme (k := k) Z s hs r).hom.appLE U.1 (relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.hom_preimage_chartOpen (k := k) Z s hs r U).ge =
      (relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U) ≫
        relativeJetScheme.chartSections (k := k) Z s hs r U := by
  apply AlgebraicGeometry.Scheme.Opens.SpecMap_ext
  rw [AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE,
    ← CategoryTheory.Category.assoc, relativeJetScheme.chartOpen_toSpecΓ_SpecMap_chartSections,
    ← CategoryTheory.cancel_mono U.2.fromSpec, CategoryTheory.Category.assoc,
    AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    CategoryTheory.Category.assoc, ← relativeJetScheme.chart_comp_hom (k := k) Z s hs r U,
    ← CategoryTheory.Category.assoc,
    AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp]
  rfl

/-- Pointwise form of `hom_appLE_chartOpen`. -/
theorem relativeJetScheme.hom_appLE_chartOpen_apply (U : C.AffineZariskiSite) (a : Γ(C, U.1)) :
    ((relativeJetScheme (k := k) Z s hs r).hom.appLE U.1 (relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.hom_preimage_chartOpen (k := k) Z s hs r U).ge).hom a =
      (relativeJetScheme.chartSections (k := k) Z s hs r U).hom
        (((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)).hom a) :=
  congrArg (fun φ : Γ(C, U.1) ⟶
      Γ((relativeJetScheme (k := k) Z s hs r).left, relativeJetScheme.chartOpen (k := k) Z s hs r U) =>
      φ.hom a) (relativeJetScheme.hom_appLE_chartOpen (k := k) Z s hs r U)

end ChartLemmas

end
