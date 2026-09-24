import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackComponents
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackTwistToPushforwardInvApply

/-! # Naturality of the Veronese chart isomorphisms

The components `twistDiagramComponentIso Ψ U` built from the degree-rescaling
comparison morphisms `chartTwistHom U` (`VeroneseTwistPullbackComponents`) commute with the transition maps of the two
gluing diagrams. Proved pointwise; see the docstring of `twistDiagramComponentIso_natural` for the complete argument and the
list of pointwise formulas established here.

Source: Stacks 0B5J, 01MX (θ), 01NP (transition maps); Lemma 2.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m)

/-- `((f ≫ g).app W) s = (g.app W) ((f.app W) s)` (definitional; stated generically so that the kernel checks it on
variables, not on the large concrete composites). -/
theorem Modules_comp_app_hom_apply {Y : AlgebraicGeometry.Scheme.{u}} {M N K : Y.Modules} (f : M ⟶ N) (g : N ⟶ K)
    (W : Y.Opens) (s : Γ(M, W)) : ((f ≫ g).app W).hom s = (g.app W).hom ((f.app W).hom s) := rfl

/-- `(c_* φ).app W = φ.app (c⁻¹ W)` on elements (definitional, generic). -/
theorem Modules_pushforward_map_app_hom_apply {Y Z : AlgebraicGeometry.Scheme.{u}} (c : Z ⟶ Y) {N₁ N₂ : Z.Modules}
    (φ : N₁ ⟶ N₂) (W : Y.Opens) (s : Γ((AlgebraicGeometry.Scheme.Modules.pushforward c).obj N₁, W)) :
    (((AlgebraicGeometry.Scheme.Modules.pushforward c).map φ).app W).hom s = (φ.app (c ⁻¹ᵁ W)).hom s := rfl

/-- `((X ≪≫ c_*.mapIso (Y ≪≫ Z)).hom.app W) s = (Z.hom.app (c⁻¹W)) ((Y.hom.app (c⁻¹W)) ((X.hom.app W) s))`
(definitional, generic: the shape of `twistDiagramComponentIso`). -/
theorem Modules_isoTrans_mapIso_app_hom_apply {Y Z : AlgebraicGeometry.Scheme.{u}} (c : Z ⟶ Y) {M₁ : Y.Modules}
    {N₁ N₂ N₃ : Z.Modules} (X : M₁ ≅ (AlgebraicGeometry.Scheme.Modules.pushforward c).obj N₁) (Y' : N₁ ≅ N₂)
    (Z' : N₂ ≅ N₃) (W : Y.Opens) (s : Γ(M₁, W)) :
    (((X ≪≫ (AlgebraicGeometry.Scheme.Modules.pushforward c).mapIso (Y' ≪≫ Z')).hom.app W).hom s) =
      (Z'.hom.app (c ⁻¹ᵁ W)).hom ((Y'.hom.app (c ⁻¹ᵁ W)).hom ((X.hom.app W).hom s)) := rfl

/-- The point `(Proj.map toVeronese_U) (veroneseHom_U y) = (chartIso U).inv y` of `Proj A'(U)` lies in the chart preimage
`c'_U⁻¹ ψ.hom⁻¹ W` whenever `y ∈ c_U⁻¹ W` (chart square `projChart_comp_leftIso_hom` and `chartIso.inv_hom_id`). -/
theorem comap_toVeronese_veroneseHom_mem (U : X.AffineZariskiSite)
    (W : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (y : (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens)) :
    ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1) ∈
      (S.veronese m).toGradedAffineAlgebra.projChart U ⁻¹ᵁ ((leftIso S m hm).hom ⁻¹ᵁ W) := by
  have h1 := congrArg (fun g : AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens) ⟶
      (AlgebraicGeometry.Scheme.relativeProj S).left => g.base ((chartIso S m hm U).inv.base y.1))
    (projChart_comp_leftIso_hom S m hm U)
  have h2 := congrArg (fun g : AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) ⟶
      AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) => g.base y.1) (chartIso S m hm U).inv_hom_id
  change ((S.veronese m).toGradedAffineAlgebra.projChart U ≫ (leftIso S m hm).hom).base
    ((chartIso S m hm U).inv.base y.1) = ((chartIso S m hm U).hom ≫ S.toGradedAffineAlgebra.projChart U).base
    ((chartIso S m hm U).inv.base y.1) at h1
  change (chartIso S m hm U).hom.base ((chartIso S m hm U).inv.base y.1) = y.1 at h2
  show ((S.veronese m).toGradedAffineAlgebra.projChart U ≫ (leftIso S m hm).hom).base
    ((chartIso S m hm U).inv.base y.1) ∈ W
  rw [h1]
  show (S.toGradedAffineAlgebra.projChart U).base ((chartIso S m hm U).hom.base ((chartIso S m hm U).inv.base y.1)) ∈ W
  rw [h2]
  exact y.2

/-- `twistChartPushIso` is a re-indexing on sections (definitional). -/
theorem twistChartPushIso_hom_app_apply (U : X.AffineZariskiSite) (n : ℤ)
    (W : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ((S.veronese m).sectionsGrading U.toOpens) n
      ((S.veronese m).toGradedAffineAlgebra.projChart U ⁻¹ᵁ ((leftIso S m hm).hom ⁻¹ᵁ W) :
        (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens))
    (z : ((chartIso S m hm U).hom ⁻¹ᵁ (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W) :
      (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens))
    (hz : z.1 ∈ ((S.veronese m).toGradedAffineAlgebra.projChart U ⁻¹ᵁ ((leftIso S m hm).hom ⁻¹ᵁ W) :
      (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ((S.veronese m).sectionsGrading U.toOpens) n
        ((chartIso S m hm U).hom ⁻¹ᵁ (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W) :
          (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens) from
      (((twistChartPushIso S m hm U n).hom.app W).hom s)).1 z = s.1 ⟨z.1, hz⟩ :=
  rfl

/-- `chartTwistPushIsoVeronese` on sections: a re-indexing followed by `θ_{ofVeronese}⁻¹`, pointwise the fibre map along
`toVeronese` (`Proj.inv_twistToPushforward_app_apply`). -/
theorem chartTwistPushIsoVeronese_hom_app_apply (U : X.AffineZariskiSite) (n : ℤ)
    (W' : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens)
    (s' : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ((S.veronese m).sectionsGrading U.toOpens) n
      ((chartIso S m hm U).hom ⁻¹ᵁ W' : (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens))
    (q : ((AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom ⁻¹ᵁ W' :
      (AlgebraicGeometry.Proj (veroneseGrading (S.sectionsGrading U.toOpens) m)).Opens))
    (hq : ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens) q.1 ∈
      ((chartIso S m hm U).hom ⁻¹ᵁ W' : (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens)) :
    haveI := q.1.isPrime
    haveI := (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens) q.1).isPrime
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (veroneseGrading (S.sectionsGrading U.toOpens) m) n
        ((AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom ⁻¹ᵁ W') from
      (((chartTwistPushIsoVeronese S m hm U n).hom.app W').hom s')).1 q =
      Localization.localRingHom
        (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
          q.1).asHomogeneousIdeal.toIdeal q.1.asHomogeneousIdeal.toIdeal
        (toVeronese S m hm U.toOpens : (S.veronese m).sectionsRing U.toOpens →+*
          veroneseSubring (S.sectionsGrading U.toOpens) m) rfl
        (s'.1 ⟨ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens) q.1,
          hq⟩) := by
  haveI := isIso_twistToPushforward_ofVeronese S m hm U.toOpens n
  exact AlgebraicGeometry.Proj.inv_twistToPushforward_app_apply (ofVeronese S m hm U.toOpens)
    (toVeronese S m hm U.toOpens) (irrelevant_le_map_ofVeronese S m hm U.toOpens)
    (irrelevant_le_map_toVeronese S m hm U.toOpens) (toVeronese_comp_ofVeronese S m hm U.toOpens)
    (ofVeronese_comp_toVeronese S m hm U.toOpens) n
    ((AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom ⁻¹ᵁ W')
    ((((AlgebraicGeometry.Scheme.Modules.pushforwardCongr (chartIso_hom S m hm U)).hom.app
        (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) n) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp
        (AlgebraicGeometry.Proj.map (ofVeronese S m hm U.toOpens) (irrelevant_le_map_ofVeronese S m hm U.toOpens))
        (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).inv.app
        (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U.toOpens) n)).app W').hom s') q

/-- `(Proj.map toVeronese_U) (veroneseHom_U y) = (chartIso U).inv y ∈ (chartIso U).hom⁻¹ W'` for `y ∈ W'`. -/
theorem comap_toVeronese_veroneseHom_mem_chartIso (U : X.AffineZariskiSite)
    (W' : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens) (y : W') :
    ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1) ∈
      ((chartIso S m hm U).hom ⁻¹ᵁ W' : (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens) := by
  have h2 := congrArg (fun g : AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) ⟶
      AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) => g.base y.1) (chartIso S m hm U).inv_hom_id
  change (chartIso S m hm U).hom.base ((chartIso S m hm U).inv.base y.1) = y.1 at h2
  show (chartIso S m hm U).hom.base ((chartIso S m hm U).inv.base y.1) ∈ W'
  rw [h2]
  exact y.2

/-- **Pointwise formula for the component** `twistDiagramComponentIso Ψ U` when `(Ψ U).hom = chartTwistHom U`:
for a section `s` of `ψ.hom_* c'_U_* O_{A'(U)}(1)` over `W` and `y ∈ c_U⁻¹ W`,
`(component s)(y) = ι_U-fibre map (toVeronese_U-fibre map (s ((Proj.map toVeronese_U) (veroneseHom_U y))))`
(`twistChartPushIso_hom_app_apply`, `chartTwistPushIsoVeronese_hom_app_apply`, `Proj.veroneseTwistHom_app_apply`). -/
theorem twistDiagramComponentIso_hom_app_apply
    (Ψ : ∀ U : X.AffineZariskiSite,
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ≅
      AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ))
    (hΨ : ∀ U, (Ψ U).hom = chartTwistHom S m hm U) (U : X.AffineZariskiSite)
    (W : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ((S.veronese m).sectionsGrading U.toOpens) 1
      ((S.veronese m).toGradedAffineAlgebra.projChart U ⁻¹ᵁ ((leftIso S m hm).hom ⁻¹ᵁ W) :
        (AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens)).Opens))
    (y : (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens)) :
    haveI := y.1.isPrime
    haveI := ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).isPrime
    haveI := (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).isPrime
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.sectionsGrading U.toOpens) (m : ℤ)
        (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens) from
      (((twistDiagramComponentIso S m hm Ψ U).hom.app W).hom s)).1 y =
      AlgebraicGeometry.Proj.veroneseFiberMap
        (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm) y.1
        (Localization.localRingHom
          (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
            ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).asHomogeneousIdeal.toIdeal
          ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).asHomogeneousIdeal.toIdeal
          (toVeronese S m hm U.toOpens : (S.veronese m).sectionsRing U.toOpens →+*
            veroneseSubring (S.sectionsGrading U.toOpens) m) rfl
          (s.1 ⟨ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
            ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1),
            comap_toVeronese_veroneseHom_mem S m hm U W y⟩)) := by
  haveI := y.1.isPrime
  haveI := ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).isPrime
  haveI := (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
    ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).isPrime
  have g1 := Modules_isoTrans_mapIso_app_hom_apply (S.toGradedAffineAlgebra.projChart U) (twistChartPushIso S m hm U 1)
    (chartTwistPushIsoVeronese S m hm U 1) (Ψ U) W s
  have g2 := congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ⟶
      AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ) =>
    ((φ.app (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W)).hom
      (((chartTwistPushIsoVeronese S m hm U 1).hom.app (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W)).hom
        (((twistChartPushIso S m hm U 1).hom.app W).hom s)) :
      Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ)), W))) (hΨ U)
  refine (congrArg (fun t : Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ)), W) =>
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.sectionsGrading U.toOpens) (m : ℤ)
        (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens) from
      t).1 y) (g1.trans g2)).trans ?_
  refine (AlgebraicGeometry.Proj.veroneseTwistHom_app_apply
    (AlgebraicGeometry.Proj.veroneseIso_hom_base_veroneseHom_base (S.sectionsGrading U.toOpens) m hm)
    (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm)
    (AlgebraicGeometry.Proj.veroneseIso_hom_isVeroneseSectionCompatible (S.sectionsGrading U.toOpens) m hm)
    1 (m : ℤ) (one_mul _).symm (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W)
    (((chartTwistPushIsoVeronese S m hm U 1).hom.app (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W)).hom
      (((twistChartPushIso S m hm U 1).hom.app W).hom s)) y).trans ?_
  have h4 := chartTwistPushIsoVeronese_hom_app_apply S m hm U 1 (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W)
    (((twistChartPushIso S m hm U 1).hom.app W).hom s)
    ⟨(AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1,
      AlgebraicGeometry.Proj.subset_preimage_preimage
        (AlgebraicGeometry.Proj.veroneseIso_hom_base_veroneseHom_base (S.sectionsGrading U.toOpens) m hm)
        (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W) y.2⟩
    (comap_toVeronese_veroneseHom_mem_chartIso S m hm U (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W) y)
  have h5 := twistChartPushIso_hom_app_apply S m hm U 1 W s
    ⟨ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1),
      comap_toVeronese_veroneseHom_mem_chartIso S m hm U (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W) y⟩
    (comap_toVeronese_veroneseHom_mem S m hm U W y)
  exact congrArg (AlgebraicGeometry.Proj.veroneseFiberMap
    (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm) y.1)
    (h4.trans (congrArg (Localization.localRingHom
      (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).asHomogeneousIdeal.toIdeal
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).asHomogeneousIdeal.toIdeal
      (toVeronese S m hm U.toOpens : (S.veronese m).sectionsRing U.toOpens →+*
        veroneseSubring (S.sectionsGrading U.toOpens) m) rfl) h5))


/-- The chart point `(Proj.map ρ) y = ρ⁻¹ y` of `Proj A(V)` lies in `c_V⁻¹ W` when `y ∈ c_U⁻¹ W` (`map_projChart`). -/
theorem comap_restrictGraded_mem (T : X.GradedQCAlgebra) {U V : X.AffineZariskiSite} (h : U ≤ V)
    (W : (AlgebraicGeometry.Scheme.relativeProj T).left.Opens)
    (y : (T.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (T.sectionsGrading U.toOpens)).Opens)) :
    ProjectiveSpectrum.comap (T.toGradedAffineAlgebra.restrictGraded h) (T.toGradedAffineAlgebra.restrict_irrelevant_le h)
        y.1 ∈
      (T.toGradedAffineAlgebra.projChart V ⁻¹ᵁ W : (AlgebraicGeometry.Proj (T.sectionsGrading V.toOpens)).Opens) := by
  have h1 := congrArg (fun g : AlgebraicGeometry.Proj (T.sectionsGrading U.toOpens) ⟶
      (AlgebraicGeometry.Scheme.relativeProj T).left => g.base y.1) (T.toGradedAffineAlgebra.map_projChart h)
  change ((AlgebraicGeometry.Proj.map (T.toGradedAffineAlgebra.restrictGraded h)
      (T.toGradedAffineAlgebra.restrict_irrelevant_le h) ≫ T.toGradedAffineAlgebra.projChart V).base y.1 =
    (T.toGradedAffineAlgebra.projChart U).base y.1) at h1
  show (AlgebraicGeometry.Proj.map (T.toGradedAffineAlgebra.restrictGraded h)
      (T.toGradedAffineAlgebra.restrict_irrelevant_le h) ≫ T.toGradedAffineAlgebra.projChart V).base y.1 ∈ W
  rw [h1]
  exact y.2

/-- Pointwise formula for the transition maps of the gluing diagram (`Proj.twistPushTransition_app_apply`). -/
theorem twistTransition_app_apply (T : X.GradedQCAlgebra) (n : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V)
    (W : (AlgebraicGeometry.Scheme.relativeProj T).left.Opens)
    (σ : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (T.sectionsGrading V.toOpens) n
      (T.toGradedAffineAlgebra.projChart V ⁻¹ᵁ W : (AlgebraicGeometry.Proj (T.sectionsGrading V.toOpens)).Opens))
    (y : (T.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (T.sectionsGrading U.toOpens)).Opens)) :
    haveI := y.1.isPrime
    haveI := (ProjectiveSpectrum.comap (T.toGradedAffineAlgebra.restrictGraded h)
      (T.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1).isPrime
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (T.sectionsGrading U.toOpens) n
        (T.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (T.sectionsGrading U.toOpens)).Opens) from
      ((T.toGradedAffineAlgebra.twistTransition n h).app W).hom σ).1 y =
      Localization.localRingHom
        (ProjectiveSpectrum.comap (T.toGradedAffineAlgebra.restrictGraded h)
          (T.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1).asHomogeneousIdeal.toIdeal
        y.1.asHomogeneousIdeal.toIdeal (RingHomClass.toRingHom (T.toGradedAffineAlgebra.restrictGraded h))
        rfl (σ.1 ⟨ProjectiveSpectrum.comap (T.toGradedAffineAlgebra.restrictGraded h)
          (T.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1, comap_restrictGraded_mem T h W y⟩) :=
  AlgebraicGeometry.Proj.twistPushTransition_app_apply (T.toGradedAffineAlgebra.restrictGraded h)
    (T.toGradedAffineAlgebra.restrict_irrelevant_le h) n (T.toGradedAffineAlgebra.projChart V)
    (T.toGradedAffineAlgebra.projChart U) (T.toGradedAffineAlgebra.map_projChart h) W σ y
    (comap_restrictGraded_mem T h W y)

/-- The graded restriction `ρ^{(m)} := toVeronese_U ∘ ρ' ∘ ofVeronese_V : B(V) → B(U)` of `chartIso_naturality`. -/
abbrev veroneseRestrict {U V : X.AffineZariskiSite} (h : U ≤ V) :
    veroneseGrading (S.sectionsGrading V.toOpens) m →+*ᵍ veroneseGrading (S.sectionsGrading U.toOpens) m :=
  ((toVeronese S m hm U.toOpens).comp
    ((S.veronese m).toGradedAffineAlgebra.restrictGraded h :
      (S.veronese m).sectionsGrading V.toOpens →+*ᵍ (S.veronese m).sectionsGrading U.toOpens)).comp
    (ofVeronese S m hm V.toOpens)

theorem irrelevant_le_map_veroneseRestrict {U V : X.AffineZariskiSite} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading U.toOpens) m) ≤
      (HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading V.toOpens) m)).map (veroneseRestrict S m hm h) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_ofVeronese S m hm V.toOpens)
    (HomogeneousIdeal.irrelevant_le_map_comp ((S.veronese m).toGradedAffineAlgebra.restrict_irrelevant_le h)
      (irrelevant_le_map_toVeronese S m hm U.toOpens))

/-- `toVeronese_U ∘ ρ' = ρ^{(m)} ∘ toVeronese_V` on `A'(V)` (`ofVeronese_toVeronese`). -/
theorem toVeronese_restrictGraded_apply {U V : X.AffineZariskiSite} (h : U ≤ V)
    (z : (S.veronese m).sectionsRing V.toOpens) :
    toVeronese S m hm U.toOpens ((S.veronese m).toGradedAffineAlgebra.restrictGraded h z) =
      veroneseRestrict S m hm h (toVeronese S m hm V.toOpens z) := by
  change _ = toVeronese S m hm U.toOpens ((S.veronese m).toGradedAffineAlgebra.restrictGraded h
    (ofVeronese S m hm V.toOpens (toVeronese S m hm V.toOpens z)))
  rw [ofVeronese_toVeronese]

/-- `ι_U ∘ toVeronese_U ∘ ρ' = ρ ∘ ι_V ∘ toVeronese_V` on `A'(V)` (`toVeronese_restrict_ofVeronese`). -/
theorem subtype_toVeronese_restrictGraded_apply {U V : X.AffineZariskiSite} (h : U ≤ V)
    (z : (S.veronese m).sectionsRing V.toOpens) :
    ((toVeronese S m hm U.toOpens ((S.veronese m).toGradedAffineAlgebra.restrictGraded h z) :
        veroneseSubring (S.sectionsGrading U.toOpens) m) : S.sectionsRing U.toOpens) =
      S.toGradedAffineAlgebra.restrictGraded h
        ((toVeronese S m hm V.toOpens z : veroneseSubring (S.sectionsGrading V.toOpens) m) :
          S.sectionsRing V.toOpens) := by
  have := toVeronese_restrict_ofVeronese S m hm h (toVeronese S m hm V.toOpens z)
  rw [ofVeronese_toVeronese] at this
  exact this

/-- The two chart points of `Proj A'(V)` agree: `ρ'⁻¹ (toVeronese_U⁻¹ (veroneseHom_U y)) =
toVeronese_V⁻¹ (veroneseHom_V (ρ⁻¹ y))` (`Proj.veroneseHom_naturality` and `toVeronese_restrictGraded_apply`). -/
theorem comap_point_eq {U V : X.AffineZariskiSite} (h : U ≤ V)
    (y : AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)) :
    ProjectiveSpectrum.comap ((S.veronese m).toGradedAffineAlgebra.restrictGraded h)
        ((S.veronese m).toGradedAffineAlgebra.restrict_irrelevant_le h)
        (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
          ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y)) =
      ProjectiveSpectrum.comap (toVeronese S m hm V.toOpens) (irrelevant_le_map_toVeronese S m hm V.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm).base
          (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
            (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y)) := by
  let resS : S.sectionsGrading V.toOpens →+*ᵍ S.sectionsGrading U.toOpens := S.toGradedAffineAlgebra.restrictGraded h
  have hS : HomogeneousIdeal.irrelevant (S.sectionsGrading U.toOpens) ≤
      (HomogeneousIdeal.irrelevant (S.sectionsGrading V.toOpens)).map resS :=
    S.toGradedAffineAlgebra.restrict_irrelevant_le h
  have key := AlgebraicGeometry.Proj.veroneseHom_naturality (S.sectionsGrading V.toOpens) (S.sectionsGrading U.toOpens)
    m hm resS hS (veroneseRestrict S m hm h) (irrelevant_le_map_veroneseRestrict S m hm h)
    (fun x => toVeronese_restrict_ofVeronese S m hm h x)
  have hpt := congrArg (fun g : AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) ⟶
    AlgebraicGeometry.Proj (veroneseGrading (S.sectionsGrading V.toOpens) m) => g.base y) key
  change (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm).base
      (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y) =
    ProjectiveSpectrum.comap (veroneseRestrict S m hm h) (irrelevant_le_map_veroneseRestrict S m hm h)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y) at hpt
  rw [hpt]
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective (Ideal.ext fun z => ?_))
  exact Iff.of_eq (congrArg (fun w : veroneseSubring (S.sectionsGrading U.toOpens) m =>
    w ∈ ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y).asHomogeneousIdeal.toIdeal)
    (toVeronese_restrictGraded_apply S m hm h z))



/-- Transport lemma for two chains of three fibre maps with the same composite ring homomorphism (pointwise)
(`Localization.localRingHom_unique`). -/
theorem localRingHom_chain_eq {R R₂ R₃ R₂' R₃' T : Type u} [CommRing R] [CommRing R₂] [CommRing R₃]
    [CommRing R₂'] [CommRing R₃'] [CommRing T]
    (P : Ideal R) [P.IsPrime] (Q₂ : Ideal R₂) [Q₂.IsPrime] (Q₃ : Ideal R₃) [Q₃.IsPrime]
    (Q₂' : Ideal R₂') [Q₂'.IsPrime] (Q₃' : Ideal R₃') [Q₃'.IsPrime] (J : Ideal T) [J.IsPrime]
    (f₁ : R →+* R₂) (f₂ : R₂ →+* R₃) (f₃ : R₃ →+* T) (g₁ : R →+* R₂') (g₂ : R₂' →+* R₃') (g₃ : R₃' →+* T)
    (h₁ : P = Q₂.comap f₁) (h₂ : Q₂ = Q₃.comap f₂) (h₃ : Q₃ = J.comap f₃)
    (h₁' : P = Q₂'.comap g₁) (h₂' : Q₂' = Q₃'.comap g₂) (h₃' : Q₃' = J.comap g₃)
    (hfg : ∀ r, f₃ (f₂ (f₁ r)) = g₃ (g₂ (g₁ r))) (z : Localization.AtPrime P) :
    Localization.localRingHom Q₃ J f₃ h₃ (Localization.localRingHom Q₂ Q₃ f₂ h₂ (Localization.localRingHom P Q₂ f₁ h₁ z)) =
      Localization.localRingHom Q₃' J g₃ h₃' (Localization.localRingHom Q₂' Q₃' g₂ h₂'
        (Localization.localRingHom P Q₂' g₁ h₁' z)) := by
  have hcomp : (Localization.localRingHom Q₃ J f₃ h₃).comp ((Localization.localRingHom Q₂ Q₃ f₂ h₂).comp
      (Localization.localRingHom P Q₂ f₁ h₁)) =
    (Localization.localRingHom Q₃' J g₃ h₃').comp ((Localization.localRingHom Q₂' Q₃' g₂ h₂').comp
      (Localization.localRingHom P Q₂' g₁ h₁')) :=
    IsLocalization.ringHom_ext P.primeCompl (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map, hfg])
  exact DFunLike.congr_fun hcomp z

/-- `localRingHom_chain_eq` for a point-indexed family, with the two starting points identified. -/
theorem localRingHom_chain_eq' {σ' A' : Type u} [CommRing A'] [SetLike σ' A'] [AddSubgroupClass σ' A']
    {𝒜' : ℕ → σ'} [GradedRing 𝒜'] {V' : Set (ProjectiveSpectrum 𝒜')}
    (s : ∀ x : V', MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜' x.1)
    (x₁ x₂ : ProjectiveSpectrum 𝒜') (hx : x₁ = x₂) (m₁ : x₁ ∈ V') (m₂ : x₂ ∈ V')
    {R₂ R₃ R₂' R₃' T : Type u} [CommRing R₂] [CommRing R₃] [CommRing R₂'] [CommRing R₃'] [CommRing T]
    (Q₂ : Ideal R₂) [Q₂.IsPrime] (Q₃ : Ideal R₃) [Q₃.IsPrime]
    (Q₂' : Ideal R₂') [Q₂'.IsPrime] (Q₃' : Ideal R₃') [Q₃'.IsPrime] (J : Ideal T) [J.IsPrime]
    (f₁ : A' →+* R₂) (f₂ : R₂ →+* R₃) (f₃ : R₃ →+* T) (g₁ : A' →+* R₂') (g₂ : R₂' →+* R₃') (g₃ : R₃' →+* T)
    (h₁ : x₁.asHomogeneousIdeal.toIdeal = Q₂.comap f₁) (h₂ : Q₂ = Q₃.comap f₂) (h₃ : Q₃ = J.comap f₃)
    (h₁' : x₂.asHomogeneousIdeal.toIdeal = Q₂'.comap g₁) (h₂' : Q₂' = Q₃'.comap g₂) (h₃' : Q₃' = J.comap g₃)
    (hfg : ∀ r, f₃ (f₂ (f₁ r)) = g₃ (g₂ (g₁ r))) :
    Localization.localRingHom Q₃ J f₃ h₃ (Localization.localRingHom Q₂ Q₃ f₂ h₂
      (Localization.localRingHom x₁.asHomogeneousIdeal.toIdeal Q₂ f₁ h₁ (s ⟨x₁, m₁⟩))) =
    Localization.localRingHom Q₃' J g₃ h₃' (Localization.localRingHom Q₂' Q₃' g₂ h₂'
      (Localization.localRingHom x₂.asHomogeneousIdeal.toIdeal Q₂' g₁ h₁' (s ⟨x₂, m₂⟩))) := by
  subst hx
  exact localRingHom_chain_eq _ Q₂ Q₃ Q₂' Q₃' J f₁ f₂ f₃ g₁ g₂ g₃ h₁ h₂ h₃ h₁' h₂' h₃' hfg _



/-- **Naturality of the components.** Proved exactly along the route below; the pointwise formulas are the lemmas of this module.
The components `twistDiagramComponentIso Ψ U` built from **the** degree-rescaling isomorphisms `Ψ_U` (any family whose
`hom` is `chartTwistHom U`, hypothesis `hΨ`) commute with the transition maps `twistTransition` of the two gluing
diagrams (the left one pushed forward along `ψ.hom = (leftIso S m hm).hom`).

Source: Stacks 0B5J (the identification `O_{Proj S}(nd) ↔ O_{Proj S^{(d)}}(n)` is compatible with restriction to
`D_+(f)`, hence natural), Stacks 01MX (θ), 01NP (transition maps); Lemma 2.2 of the paper.

Notation. `S' := S.veronese m`; for affine `U`: `A(U) := S.sectionsGrading U`, `A'(U) := S'.sectionsGrading U`,
`B(U) := veroneseGrading (A(U)) m`; `c_U`, `c'_U` the charts (`projChart`); `e_U := chartIso S m hm U`,
`e_U.hom = o_U ≫ v_U.hom` with `o_U := Proj.map (ofVeronese_U)`, `v_U := Proj.veroneseIso (A(U)) m hm`,
`vH_U := veroneseHom (A(U)) m hm` (so `v_U.hom = inv vH_U`); for `U ≤ V`: `ρ := S.restrictGraded h : A(V) → A(U)`,
`ρ' : A'(V) → A'(U)`, `r := Proj.map ρ`, `r' := Proj.map ρ'`, `ρ^{(m)} := toVeronese_U ∘ ρ' ∘ ofVeronese_V : B(V) → B(U)`,
`q := Proj.map ρ^{(m)}`; `ι_U : B(U) → A(U)` the inclusion; `to_U := toVeronese_U : A'(U) → B(U)`.

Proof. Both sides are morphisms of sheaves of modules on `Proj_X S` between pushforwards along the charts; check them on
sections over an open `W` (`Modules.hom_ext`, `AddCommGrpCat.hom_ext`), then pointwise (`Subtype.ext`, `funext`): a section
`s` of the source is a function on `c'_V⁻¹ ψ.hom⁻¹ W ⊆ Proj A'(V)`; a point of the target chart is `y ∈ c_U⁻¹ W ⊆ Proj A(U)`.
Pointwise formulas of the pieces:
(a) `pushforwardComp` components are the identity on sections (`pushforwardComp_hom_app_app`), `pushforwardCongr`
    components are restriction along `eqToHom` (`pushforwardCongr_hom_app_app`), i.e. re-indexing of a function
    (`presheaf_map_apply`); `(pushforward c).map g` on sections over `W` is `g` on sections over `c⁻¹ W`
    (`pushforward_map_app`).
(b) `twistTransition = Proj.twistPushTransition`, pointwise `s ↦ (y ↦ localRingHom_ρ (s (comap ρ y)))`
    (`twistPushTransition_app_apply`, `ProjTwistPushTransition`); likewise for `ρ'`.
(c) `chartTwistPushIsoVeronese U 1` is, on sections, `pushforwardCongr`/`pushforwardComp` re-indexing followed by
    `(v_U.hom)_* (inv θ_{o_U})` where `θ_{o_U} = Proj.twistToPushforward ofVeronese_U` is pointwise `localRingHom_{ofVeronese}`
    (`twistToPushforward_app_apply`, `ProjTwistToPushforwardApply`). The inverse is pointwise
    `σ ↦ (𝔮 ↦ localRingHom_{to_U} (σ (comap to_U 𝔮)))`: apply the injective `θ_{o_U}` to both sides and use
    `Localization.localRingHom_comp` with `ofVeronese ∘ toVeronese = id` (`ofVeronese_comp_toVeronese`), and
    `comap ofVeronese (comap toVeronese 𝔮) = 𝔮`.
(d) `Ψ_U` is pointwise `localRingHom_{ι_U}` at `vH_U y` (`Proj.veroneseTwistHom_app_apply`, via `hΨ`).
Hence, for `s` and `y` as above,
  LHS `= localRingHom_{ι_U} (localRingHom_{to_U} (localRingHom_{ρ'} (s p)))` with `p := comap ρ' (comap to_U (vH_U y))`,
  RHS `= localRingHom_ρ (localRingHom_{ι_V} (localRingHom_{to_V} (s p')))` with `p' := comap to_V (vH_V (comap ρ y))`.
The points agree: `vH_V (comap ρ y) = comap ρ^{(m)} (vH_U y)` is the naturality of `veroneseHom`
(`Proj.veroneseHom_naturality`, ProjVeroneseIso.lean, proved; as morphisms `r ≫ vH_V = vH_U ≫ q`, evaluated on points),
and `comap to_V (comap ρ^{(m)} 𝔮) = comap ρ' (comap to_U 𝔮)` because `ρ^{(m)} ∘ to_V = to_U ∘ ρ'` as ring homomorphisms
(`ρ^{(m)} ∘ to_V = to_U ∘ ρ' ∘ ofVeronese_V ∘ to_V = to_U ∘ ρ'` by `ofVeronese_toVeronese`; `Ideal.comap_comap`).
The ring homomorphisms agree: `ι_U ∘ to_U ∘ ρ' = ρ ∘ ι_V ∘ to_V : A'(V) → A(U)` — apply `toVeronese_restrict_ofVeronese`
(ProjVeroneseIso.lean) to `ofVeronese_V (to_V x)` and use `ofVeronese_toVeronese`. Then both sides are
`localRingHom_{ι_U ∘ to_U ∘ ρ'} (s p)` by `Localization.localRingHom_comp` (twice on each side), transported along the
equality of points and of ring homomorphisms (`subst`, as in `twistPushTransition_comp`'s `localRingHom_family_comp`).

Edge cases: `U = V` (`h = le_refl`) — both transition maps are `𝟙` (`twistTransition_id`) and the square is trivial;
`W = ∅` or charts empty — no points, both sides are the unique map; `m = 1` — `B(U) = A(U)` relabelled.

Formalization notes: (i) is `Proj.inv_twistToPushforward_app_apply` (module VeroneseTwistPullbackTwistToPushforwardInvApply);
(ii) is `twistDiagramComponentIso_hom_app_apply` below, built from the **generic** definitional lemmas
`Modules_isoTrans_mapIso_app_hom_apply`, `Modules_comp_app_hom_apply`, `Modules_pushforward_map_app_hom_apply` (stated for
variable morphisms so that the kernel never unfolds the concrete composites — a `show`/`rw` on the concrete term took > 40 s),
`twistChartPushIso_hom_app_apply` (rfl) and `chartTwistPushIsoVeronese_hom_app_apply`; (iii) is `localRingHom_chain_eq'`
(`IsLocalization.ringHom_ext`). -/
theorem twistDiagramComponentIso_natural
    (Ψ : ∀ U : X.AffineZariskiSite,
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ≅
      AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ))
    (hΨ : ∀ U, (Ψ U).hom = chartTwistHom S m hm U)
    {U V : X.AffineZariskiSite} (h : U ≤ V) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso S m hm).hom).map
        ((S.veronese m).toGradedAffineAlgebra.twistTransition 1 h) ≫
      (twistDiagramComponentIso S m hm Ψ U).hom =
    (twistDiagramComponentIso S m hm Ψ V).hom ≫ S.toGradedAffineAlgebra.twistTransition (m : ℤ) h := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun W => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine Subtype.ext (funext fun y => ?_)
  have gL := Modules_comp_app_hom_apply
    ((AlgebraicGeometry.Scheme.Modules.pushforward (leftIso S m hm).hom).map
      ((S.veronese m).toGradedAffineAlgebra.twistTransition 1 h)) (twistDiagramComponentIso S m hm Ψ U).hom W s
  have gL2 := congrArg (fun r => ((twistDiagramComponentIso S m hm Ψ U).hom.app W).hom r)
    (Modules_pushforward_map_app_hom_apply (leftIso S m hm).hom
      ((S.veronese m).toGradedAffineAlgebra.twistTransition 1 h) W s)
  have gR := Modules_comp_app_hom_apply (twistDiagramComponentIso S m hm Ψ V).hom
    (S.toGradedAffineAlgebra.twistTransition (m : ℤ) h) W s
  refine (congrArg (fun t : Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart U)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ)), W) =>
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.sectionsGrading U.toOpens) (m : ℤ)
        (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens) from
      t).1 y) (gL.trans gL2)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t : Γ((AlgebraicGeometry.Scheme.Modules.pushforward
      (S.toGradedAffineAlgebra.projChart U)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ)), W) =>
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.sectionsGrading U.toOpens) (m : ℤ)
        (S.toGradedAffineAlgebra.projChart U ⁻¹ᵁ W : (AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens)).Opens) from
      t).1 y) gR).symm
  haveI := y.1.isPrime
  haveI := ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).isPrime
  haveI := (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
    ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).isPrime
  -- the four pointwise formulas
  have hA := twistDiagramComponentIso_hom_app_apply S m hm Ψ hΨ U W
    ((((S.veronese m).toGradedAffineAlgebra.twistTransition 1 h).app ((leftIso S m hm).hom ⁻¹ᵁ W)).hom s) y
  have hB := twistTransition_app_apply (S.veronese m) 1 h ((leftIso S m hm).hom ⁻¹ᵁ W) s
    ⟨ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1),
      comap_toVeronese_veroneseHom_mem S m hm U W y⟩
  have hC := twistTransition_app_apply S (m : ℤ) h W (((twistDiagramComponentIso S m hm Ψ V).hom.app W).hom s) y
  have hD := twistDiagramComponentIso_hom_app_apply S m hm Ψ hΨ V W s
    ⟨ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
      (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1, comap_restrictGraded_mem S h W y⟩
  refine hA.trans (Eq.trans ?_ (hC.trans (congrArg _ hD)).symm)
  refine (congrArg (AlgebraicGeometry.Proj.veroneseFiberMap
    (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm) y.1)
    (congrArg (Localization.localRingHom
      (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).asHomogeneousIdeal.toIdeal
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).asHomogeneousIdeal.toIdeal
      (toVeronese S m hm U.toOpens : (S.veronese m).sectionsRing U.toOpens →+*
        veroneseSubring (S.sectionsGrading U.toOpens) m) rfl) hB)).trans ?_
  haveI := y.1.isPrime
  haveI := ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).isPrime
  haveI := (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
    ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).isPrime
  haveI := (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
    (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1).isPrime
  haveI := ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm).base
    (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
      (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1)).isPrime
  exact localRingHom_chain_eq' s.1
    (ProjectiveSpectrum.comap ((S.veronese m).toGradedAffineAlgebra.restrictGraded h)
      ((S.veronese m).toGradedAffineAlgebra.restrict_irrelevant_le h)
      (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)))
    (ProjectiveSpectrum.comap (toVeronese S m hm V.toOpens) (irrelevant_le_map_toVeronese S m hm V.toOpens)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm).base
        (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
          (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1)))
    (comap_point_eq S m hm h y.1)
    (comap_restrictGraded_mem (S.veronese m) h ((leftIso S m hm).hom ⁻¹ᵁ W)
      ⟨ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
        ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1),
        comap_toVeronese_veroneseHom_mem S m hm U W y⟩)
    (comap_toVeronese_veroneseHom_mem S m hm V W
      ⟨ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1, comap_restrictGraded_mem S h W y⟩)
    (ProjectiveSpectrum.comap (toVeronese S m hm U.toOpens) (irrelevant_le_map_toVeronese S m hm U.toOpens)
      ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1)).asHomogeneousIdeal.toIdeal
    ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm).base y.1).asHomogeneousIdeal.toIdeal
    ((AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm).base
      (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1)).asHomogeneousIdeal.toIdeal
    (ProjectiveSpectrum.comap (S.toGradedAffineAlgebra.restrictGraded h)
      (S.toGradedAffineAlgebra.restrict_irrelevant_le h) y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal
    (RingHomClass.toRingHom ((S.veronese m).toGradedAffineAlgebra.restrictGraded h))
    (toVeronese S m hm U.toOpens : (S.veronese m).sectionsRing U.toOpens →+*
      veroneseSubring (S.sectionsGrading U.toOpens) m)
    (AlgebraicGeometry.Proj.veroneseSubringHom (S.sectionsGrading U.toOpens) m)
    (toVeronese S m hm V.toOpens : (S.veronese m).sectionsRing V.toOpens →+*
      veroneseSubring (S.sectionsGrading V.toOpens) m)
    (AlgebraicGeometry.Proj.veroneseSubringHom (S.sectionsGrading V.toOpens) m)
    (RingHomClass.toRingHom (S.toGradedAffineAlgebra.restrictGraded h))
    rfl rfl (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading U.toOpens) m hm y.1)
    rfl (AlgebraicGeometry.Proj.veroneseHom_isVeroneseContraction (S.sectionsGrading V.toOpens) m hm _) rfl
    (subtype_toVeronese_restrictGraded_apply S m hm h)

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso

end
