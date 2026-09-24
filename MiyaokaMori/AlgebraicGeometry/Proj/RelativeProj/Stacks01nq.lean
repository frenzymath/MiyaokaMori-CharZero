import MiyaokaMori.Prelude
-- The next two imports are not used in this file itself but are re-exported to downstream modules.
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # The relative Proj over an affine open is Proj (Stacks 01NQ)

Stacks 01NQ: over an affine open `U ⊆ X` the relative Proj is `Proj(S(U))`, i.e. `π⁻¹(U) ≅ Proj(S(U))`, and for
`U ⊆ U'` this is compatible with `Proj(S(U)) → Proj(S(U'))`. Used for the local structure of `Y_k^GG`
(Lemma 2.2 of the paper).

`affineIso` is obtained from the pullback square `GradedAffineAlgebra.projChart_isPullback` (`RelativeProj.lean`),
in the same way as `relativeSpec.affineIso`. For `affineIso_restrict`, composing with the monomorphism
`(affineIso U′).inv ≫ ι` reduces to `projMap_projChart` (`Proj.map res ≫ projChart U′ = projChart U`), which is
checked piecewise with `OpenCover.hom_ext` on the open cover `{Proj S(W) → Proj S(U) : W = D_{U′}(f) ⊆ U}` of
`Proj S(U)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `π⁻¹(U) ≅ Proj A(U)`: `projChart_isPullback` gives the pullback square `Proj A(U) → U`,
   `Proj A(U) → Proj_X S`, `U.ι`, `π`, hence `Proj A(U) ≅ pullback π U.ι ≅ π⁻¹(U)`
   (`IsPullback.isoPullback`, `pullbackRestrictIsoRestrict`); take the inverse. -/

noncomputable def AlgebraicGeometry.Scheme.relativeProj.affineIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).toScheme ≅
      AlgebraicGeometry.Proj (S.sectionsGrading U.1) :=
  (AlgebraicGeometry.pullbackRestrictIsoRestrict
      (AlgebraicGeometry.Scheme.relativeProj S).hom U.1).symm ≪≫
    (S.toGradedAffineAlgebra.projChart_isPullback ⟨U.1, U.2⟩).flip.isoPullback.symm

/-- The inverse of `affineIso` followed by the open immersion `π⁻¹U ↪ Proj_X S` is the chart `projChart`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).inv ≫
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1).ι =
      S.toGradedAffineAlgebra.projChart ⟨U.1, U.2⟩ := by
  exact (CategoryTheory.Category.assoc _ _ _).trans
    ((congrArg _ (AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_ι _ _)).trans
      (CategoryTheory.IsPullback.isoPullback_hom_fst _))

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `Proj.map` depends only on the graded homomorphism (the irrelevant-ideal condition is a proposition, so proof
irrelevance applies). -/
private theorem proj_map_congr {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst e; rfl

/-- `map_projChart`, written with `Proj.map (A.restrictGraded h)` (of type `Proj (A.grading W) ⟶ Proj (A.grading U)`
rather than `A.projFunctor.obj W ⟶ A.projFunctor.obj U`; the two are only definitionally equal, which `rw` and
instance search do not see through). -/
theorem projMap_restrictGraded_projChart (A : X.GradedAffineAlgebra) {W U : X.AffineZariskiSite}
    (h : W ≤ U) :
    AlgebraicGeometry.Proj.map (A.restrictGraded h) (A.restrict_irrelevant_le h) ≫ A.projChart U
      = A.projChart W :=
  A.map_projChart h

/-- The chart transition `Proj S(W) → Proj S(U)` (`W ≤ U` a basic open) is an open immersion: both charts are
open immersions and `projMap_restrictGraded_projChart` writes it as a factor of one (`IsOpenImmersion.of_comp`). -/
theorem projMap_restrictGraded_isOpenImmersion (A : X.GradedAffineAlgebra)
    {W U : X.AffineZariskiSite} (h : W ≤ U) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Proj.map (A.restrictGraded h) (A.restrict_irrelevant_le h)) := by
  have : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Proj.map (A.restrictGraded h) (A.restrict_irrelevant_le h) ≫
        A.projChart U) := by
    rw [projMap_restrictGraded_projChart A h]; infer_instance
  exact AlgebraicGeometry.IsOpenImmersion.of_comp _ (A.projChart U)

/-- Covering: every point `x` of `Proj S(U)` lies in the image of some `Proj S(W) → Proj S(U)`, where
`W = D_{U′}(f) ⊆ U` is a basic open of both `U′` and `U` (`IsAffineOpen.exists_basicOpen_le` + `basicOpen_res`);
then use `π⁻¹W` = image of the chart `W` (`proj_preimage_eq_opensRange`) and injectivity of the chart `U`. -/
theorem exists_projMap_restrictGraded_eq (A : X.GradedAffineAlgebra) (U U' : X.affineOpens)
    (hUU' : U.1 ≤ U'.1) (x : AlgebraicGeometry.Proj (A.grading (affineSite U))) :
    ∃ (W : X.AffineZariskiSite) (hWU : W ≤ affineSite U) (_ : W ≤ affineSite U')
      (y : AlgebraicGeometry.Proj (A.grading W)),
      AlgebraicGeometry.Proj.map (A.restrictGraded hWU) (A.restrict_irrelevant_le hWU) y = x := by
  have hpU : A.projChart (affineSite U) x ∈ A.relativeProj.hom ⁻¹ᵁ (affineSite U).toOpens := by
    rw [A.proj_preimage_eq_opensRange (affineSite U)]
    exact ⟨x, rfl⟩
  have hπp : A.relativeProj.hom (A.projChart (affineSite U) x) ∈ U.1 := hpU
  obtain ⟨f, hfU, hpf⟩ := U'.2.exists_basicOpen_le (V := U.1)
    ⟨A.relativeProj.hom (A.projChart (affineSite U) x), hπp⟩ (hUU' hπp)
  let W : X.AffineZariskiSite := (affineSite U').basicOpen f
  have hWU' : W ≤ affineSite U' := AffineZariskiSite.basicOpen_le _ f
  have hWU : W ≤ affineSite U := by
    refine ⟨X.presheaf.map (homOfLE hUU').op f, ?_⟩
    show X.basicOpen (X.presheaf.map (homOfLE hUU').op f) = X.basicOpen f
    rw [X.basicOpen_res f (homOfLE hUU').op]
    exact inf_eq_right.mpr hfU
  have hpW : A.projChart (affineSite U) x ∈ A.relativeProj.hom ⁻¹ᵁ W.toOpens := hpf
  rw [A.proj_preimage_eq_opensRange W] at hpW
  obtain ⟨y, hy⟩ := hpW
  refine ⟨W, hWU, hWU', y, ?_⟩
  apply (A.projChart (affineSite U)).isOpenEmbedding.injective
  have h2 : (AlgebraicGeometry.Proj.map (A.restrictGraded hWU) (A.restrict_irrelevant_le hWU) ≫
      A.projChart (affineSite U)) y = A.projChart (affineSite U) x := by
    rw [projMap_restrictGraded_projChart A hWU]; exact hy
  exact (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _).symm.trans h2

variable (S : X.GradedQCAlgebra)

/-- Transitivity of restriction (a general inclusion `U ⊆ U′` followed by a basic open `W ≤ U`):
`res_{W←U} ∘ res_{U←U′} = res_{W←U′}`. `restrictGraded` and `sectionsRestrict` are definitionally equal (both are
`sectionsRestrictHom`), so this is `sectionsRestrictHom_trans`. -/
theorem restrictGraded_comp_sectionsRestrict {W : X.AffineZariskiSite} {U U' : X.affineOpens}
    (hWU : W ≤ affineSite U) (hWU' : W ≤ affineSite U') (hUU' : U.1 ≤ U'.1) :
    (S.toGradedAffineAlgebra.restrictGraded hWU).comp (S.sectionsRestrict hUU')
      = S.toGradedAffineAlgebra.restrictGraded hWU' := by
  refine GradedRingHom.ext fun a => ?_
  have hWUo : W.toOpens ≤ U.1 := AffineZariskiSite.toOpens_mono hWU
  have hWU'o : W.toOpens ≤ U'.1 := AffineZariskiSite.toOpens_mono hWU'
  have h := congrArg (fun φ : S.sectionsRing U'.1 →+* S.sectionsRing W.toOpens => φ a)
    (S.sectionsRestrictHom_trans hWUo hUU' hWU'o)
  exact h.symm

/-- Piecewise: on a basic open `W ≤ U, W ≤ U′`, `Proj.map res_{W←U} ≫ Proj.map res_{U←U′} = Proj.map res_{W←U′}`
(`Proj.map_comp` + transitivity of restriction). -/
theorem projMap_restrictGraded_projMap_sectionsRestrict {W : X.AffineZariskiSite}
    {U U' : X.affineOpens} (hWU : W ≤ affineSite U) (hWU' : W ≤ affineSite U')
    (hUU' : U.1 ≤ U'.1) :
    AlgebraicGeometry.Proj.map (S.toGradedAffineAlgebra.restrictGraded hWU)
        (S.toGradedAffineAlgebra.restrict_irrelevant_le hWU) ≫
      AlgebraicGeometry.Proj.map (S.sectionsRestrict hUU')
        (S.sectionsRestrict_irrelevant U.2 U'.2 hUU')
      = AlgebraicGeometry.Proj.map (S.toGradedAffineAlgebra.restrictGraded hWU')
        (S.toGradedAffineAlgebra.restrict_irrelevant_le hWU') :=
  (AlgebraicGeometry.Proj.map_comp (S.sectionsRestrict hUU')
      (S.toGradedAffineAlgebra.restrictGraded hWU)
      (S.sectionsRestrict_irrelevant U.2 U'.2 hUU')
      (S.toGradedAffineAlgebra.restrict_irrelevant_le hWU)).symm.trans
    (proj_map_congr
      (AlgebraicGeometry.Scheme.relativeProj.restrictGraded_comp_sectionsRestrict S hWU hWU' hUU') _ _)

/-- **The core of Stacks 01NQ**: for a general inclusion of affine opens `U ⊆ U′`, `Proj.map (res)` followed by
the chart `U′` is the chart `U`.
Proof: compare piecewise (`OpenCover.hom_ext`) on the open cover `{Proj S(W) → Proj S(U)}` of `Proj S(U)` (`W` a
basic open of both `U` and `U′`, `exists_projMap_restrictGraded_eq`); on each piece both sides equal `projChart W`
(`projMap_restrictGraded_projChart` twice + the piecewise lemma). -/
theorem projMap_projChart (U U' : X.affineOpens) (hUU' : U.1 ≤ U'.1) :
    AlgebraicGeometry.Proj.map (S.sectionsRestrict hUU')
        (S.sectionsRestrict_irrelevant U.2 U'.2 hUU') ≫
        S.toGradedAffineAlgebra.projChart (affineSite U') =
      S.toGradedAffineAlgebra.projChart (affineSite U) := by
  set A := S.toGradedAffineAlgebra with hA
  choose W hWU hWU' y hy using exists_projMap_restrictGraded_eq A U U' hUU'
  let 𝒰 : (AlgebraicGeometry.Proj (A.grading (affineSite U))).OpenCover :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers
      (AlgebraicGeometry.Proj (A.grading (affineSite U)))
      (fun x => AlgebraicGeometry.Proj (A.grading (W x)))
      (fun x => AlgebraicGeometry.Proj.map (A.restrictGraded (hWU x)) (A.restrict_irrelevant_le (hWU x)))
      (fun x => ⟨x, y x, hy x⟩)
      (fun x => projMap_restrictGraded_isOpenImmersion A (hWU x))
  refine 𝒰.hom_ext _ _ fun x => ?_
  show AlgebraicGeometry.Proj.map (A.restrictGraded (hWU x)) (A.restrict_irrelevant_le (hWU x)) ≫
      (AlgebraicGeometry.Proj.map (S.sectionsRestrict hUU')
        (S.sectionsRestrict_irrelevant U.2 U'.2 hUU') ≫ A.projChart (affineSite U')) =
    AlgebraicGeometry.Proj.map (A.restrictGraded (hWU x)) (A.restrict_irrelevant_le (hWU x)) ≫
      A.projChart (affineSite U)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ A.projChart (affineSite U'))
    (AlgebraicGeometry.Scheme.relativeProj.projMap_restrictGraded_projMap_sectionsRestrict S
      (hWU x) (hWU' x) hUU')) ?_
  exact (projMap_restrictGraded_projChart A (hWU' x)).trans
    (projMap_restrictGraded_projChart A (hWU x)).symm

end AlgebraicGeometry.Scheme.relativeProj

/-- Compatibility with restriction (the second half of Stacks 01NQ). The chart transition `map_projChart` is only
available for the order of `AffineZariskiSite` (`U = D_V(f)` a basic open of `V`); for a general inclusion of
affine opens `U ⊆ U'` one writes `U` as a union of basic opens of `U'` (`IsAffineOpen.exists_basicOpen_le`) and
compares piecewise using the functoriality of `Proj.map`. Concretely, `affineIso_inv_ι` composes both sides with
the monomorphism `projChart U′` and reduces to `projMap_projChart` (the open-cover argument above). -/
theorem AlgebraicGeometry.Scheme.relativeProj.affineIso_restrict {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U U' : X.affineOpens) (hUU' : U.1 ≤ U'.1) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S U).inv ≫
        (AlgebraicGeometry.Scheme.relativeProj S).left.homOfLE
          ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono hUU') ≫
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S U').hom =
      AlgebraicGeometry.Proj.map (S.sectionsRestrict hUU') (S.sectionsRestrict_irrelevant U.2 U'.2 hUU') := by
  refine (cancel_mono ((AlgebraicGeometry.Scheme.relativeProj.affineIso S U').inv ≫
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U'.1).ι)).mp ?_
  simp only [Category.assoc, Iso.hom_inv_id_assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
  rw [AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U,
    AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S U']
  exact (AlgebraicGeometry.Scheme.relativeProj.projMap_projChart S U U' hUU').symm

end
