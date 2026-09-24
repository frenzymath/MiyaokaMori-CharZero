import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.RingTheory.GradedRing.ReesAwayAffineBlowup
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSectionsGradedEquiv
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceGradedRingIsos
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og

/-! # Stacks 0804: the blowup over an affine open

The restriction of the blowup `b : Bl_I X → X` to an affine open `U = Spec A` is the Proj of the Rees
algebra `⊕ Iᵈ`, and it is covered by the spectra of the affine blowup algebras `A[I/a]`, `a ∈ I`.

Source: Stacks 0804; used in the proofs of Stacks 0AGQ and 080E.

Route. `blowup I = relativeProj I.reesAlgebra` (Stacks 01OG); `relativeProj.affineIso` (Stacks 01NQ)
gives `b⁻¹U ≅ Proj (⊕ₙ Γ(U, Iⁿ))`; the graded ring equivalence `⊕ₙ Γ(U, Iⁿ) ≃ ⊕ₙ Jⁿ Xⁿ`, `J = I(U)`
(`exists_reesAlgebra_sectionsRing_equiv`) is transported to `Proj` by `Proj.isoOfGradedRingEquiv`.
The charts `V_a` are the images of the basic opens `D₊(aX)`, `a ∈ J`; `D₊(aX) ≅ Spec (Rees J)_{(aX)}`
is Mathlib's `Proj.basicOpenIsoSpec` and `(Rees J)_{(aX)} ≃ A[J/a]` is
`Ideal.reesAwayEquivAffineBlowup`. The structure-morphism compatibility is `projChart_hom` +
`proj_map_toSpecZero` + `awayι_toSpecZero` + the unit compatibilities of the two ring equivalences;
the covering statement is `Ideal.reesGrading_iSup_basicOpen_eq_top`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Compatibility of the inverse of `isoOfGradedRingEquiv` with the degree-zero structure maps
(Stacks 01MX; `inv = Proj.map (gradedRingHomOfRingEquiv e he)`). -/
@[reassoc]
theorem isoOfGradedRingEquiv_inv_toSpecZero (e : A ≃+* B)
    (he : ∀ i (a : A), a ∈ 𝒜 i ↔ e a ∈ ℬ i) :
    (isoOfGradedRingEquiv e he).inv ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (gradedRingHomOfRingEquiv e he).gradedZeroRingHom) :=
  AlgebraicGeometry.Proj.proj_map_toSpecZero _ _

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The unit `Γ(X, U) → (⊕ₘ Γ(U, Sₘ))₀` of the sections ring on an affine open, with its type spelled
through `sectionsGrading` (it is `S.toGradedAffineAlgebra.unitZero (affineSite U)`; the retyping keeps
the objects `Spec (S.sectionsGrading U 0)` and `Spec Γ(X, U)` syntactically uniform downstream). -/
def GradedQCAlgebra.sectionsUnitZero (S : X.GradedQCAlgebra) (U : X.affineOpens) :
    Γ(X, (U : X.Opens)) →+* S.sectionsGrading (U : X.Opens) 0 :=
  S.toGradedAffineAlgebra.unitZero (affineSite U)

theorem GradedQCAlgebra.coe_sectionsUnitZero (S : X.GradedQCAlgebra) (U : X.affineOpens)
    (r : Γ(X, (U : X.Opens))) :
    (S.sectionsUnitZero U r : S.sectionsRing (U : X.Opens)) = S.sectionsUnitHom (U : X.Opens) r := rfl

/-- The chart `Proj S(U) → U` of the relative Proj, composed with `U ≅ Spec Γ(X, U)`, is
`toSpecZero ≫ Spec (unit)`: `affineIso_inv_ι` + `projChart_hom` + `projToOpen`. -/
theorem relativeProj_affineIso_inv_morphismRestrict_isoSpec (S : X.GradedQCAlgebra)
    (U : X.affineOpens) :
    (relativeProj.affineIso S U).inv ≫ ((relativeProj S).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom =
      Proj.toSpecZero (S.sectionsGrading (U : X.Opens)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.sectionsUnitZero U)) := by
  have h1 : (relativeProj.affineIso S U).inv ≫ ((relativeProj S).hom ∣_ (U : X.Opens)) =
      S.toGradedAffineAlgebra.projToOpen (affineSite U) := by
    apply (cancel_mono (U : X.Opens).ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, relativeProj.affineIso_inv_ι]
    exact S.toGradedAffineAlgebra.projChart_hom (affineSite U)
  rw [← Category.assoc, h1]
  -- spell everything through `affineSite U` so that the objects agree syntactically
  show (Proj.toSpecZero (S.toGradedAffineAlgebra.grading (affineSite U)) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero (affineSite U))) ≫
      (affineSite U).2.isoSpec.inv) ≫ (affineSite U).2.isoSpec.hom =
    Proj.toSpecZero (S.toGradedAffineAlgebra.grading (affineSite U)) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero (affineSite U)))
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (I : X.IdealSheafData) (U : X.affineOpens)

/-- Same as `relativeProj_affineIso_inv_morphismRestrict_isoSpec`, for the blowup
`blowup I = relativeProj I.reesAlgebra`. -/
theorem blowup_affineIso_inv_morphismRestrict_isoSpec :
    (relativeProj.affineIso I.reesAlgebra U).inv ≫ ((blowup I).hom ∣_ (U : X.Opens)) ≫
        U.2.isoSpec.hom =
      Proj.toSpecZero (I.reesAlgebra.sectionsGrading (U : X.Opens)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (I.reesAlgebra.sectionsUnitZero U)) :=
  relativeProj_affineIso_inv_morphismRestrict_isoSpec I.reesAlgebra U

section Chart

variable (e : I.reesAlgebra.sectionsRing (U : X.Opens) ≃+* _root_.reesAlgebra (I.ideal U))
  (he : ∀ (m : ℕ) (x : I.reesAlgebra.sectionsRing (U : X.Opens)),
    x ∈ I.reesAlgebra.sectionsGrading (U : X.Opens) m ↔ e x ∈ Ideal.reesGrading (I.ideal U) m)

/-- `b⁻¹U ≅ Proj (⊕ₙ Jⁿ Xⁿ)`, given the graded ring equivalence `e` of
`exists_reesAlgebra_sectionsRing_equiv` (Stacks 0804, first half). -/
def blowupPreimageIso :
    ((blowup I).hom ⁻¹ᵁ (U : X.Opens)).toScheme ≅ Proj (Ideal.reesGrading (I.ideal U)) :=
  relativeProj.affineIso I.reesAlgebra U ≪≫ Proj.isoOfGradedRingEquiv e he

/-- Under `blowupPreimageIso`, the structure morphism `b|_{b⁻¹U} : b⁻¹U → U ≅ Spec A` is
`toSpecZero ≫ Spec ((Rees J)₀ → A)`. -/
theorem blowupPreimageIso_inv_morphismRestrict_isoSpec :
    (blowupPreimageIso I U e he).inv ≫ ((blowup I).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom =
      Proj.toSpecZero (Ideal.reesGrading (I.ideal U)) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Proj.gradedRingHomOfRingEquiv e he).gradedZeroRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (I.reesAlgebra.sectionsUnitZero U)) := by
  calc (blowupPreimageIso I U e he).inv ≫ ((blowup I).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom
      = (Proj.isoOfGradedRingEquiv e he).inv ≫ ((relativeProj.affineIso I.reesAlgebra U).inv ≫
          ((blowup I).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom) := Category.assoc _ _ _
    _ = (Proj.isoOfGradedRingEquiv e he).inv ≫
          Proj.toSpecZero (I.reesAlgebra.sectionsGrading (U : X.Opens)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (I.reesAlgebra.sectionsUnitZero U)) :=
        congrArg _ (blowup_affineIso_inv_morphismRestrict_isoSpec I U)
    _ = _ := Proj.isoOfGradedRingEquiv_inv_toSpecZero_assoc e he _

/-- The open immersion `Proj (⊕ₙ Jⁿ Xⁿ) ≅ b⁻¹U ↪ Bl_I X`. -/
def blowupChartι : Proj (Ideal.reesGrading (I.ideal U)) ⟶ (blowup I).left :=
  (blowupPreimageIso I U e he).inv ≫ ((blowup I).hom ⁻¹ᵁ (U : X.Opens)).ι

instance : IsOpenImmersion (blowupChartι I U e he) := by
  unfold blowupChartι; infer_instance

theorem blowupChartι_opensRange :
    (blowupChartι I U e he).opensRange = (blowup I).hom ⁻¹ᵁ (U : X.Opens) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Opens.opensRange_ι _)

theorem blowupChartι_image_le (D : (Proj (Ideal.reesGrading (I.ideal U))).Opens) :
    blowupChartι I U e he ''ᵁ D ≤ (blowup I).hom ⁻¹ᵁ (U : X.Opens) :=
  ((blowupChartι I U e he).image_le_opensRange D).trans (blowupChartι_opensRange I U e he).le

@[reassoc]
theorem blowupChartι_isoImage_hom_homOfLE (D : (Proj (Ideal.reesGrading (I.ideal U))).Opens) :
    ((blowupChartι I U e he).isoImage D).hom ≫
        (blowup I).left.homOfLE (blowupChartι_image_le I U e he D) =
      D.ι ≫ (blowupPreimageIso I U e he).inv := by
  rw [← cancel_mono ((blowup I).hom ⁻¹ᵁ (U : X.Opens)).ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.isoImage_hom_ι, Category.assoc]
  rfl

end Chart

/-- **Stacks 0804, first half**: `b⁻¹U ≅ Proj (⊕ₙ I(U)ⁿ)`. -/
theorem blowup_preimage_affine :
    Nonempty (((AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ (U : X.Opens)).toScheme ≅
      AlgebraicGeometry.Proj (Ideal.reesGrading (I.ideal U))) := by
  obtain ⟨e, he, -⟩ := I.exists_reesAlgebra_sectionsRing_equiv U
  exact ⟨blowupPreimageIso I U e he⟩

/-- `Spec (Rees J)_{(aX)} ≅ Spec A[J/a]` from `Ideal.reesAwayEquivAffineBlowup`. -/
def specReesAwayIso (J : Ideal Γ(X, (U : X.Opens))) (a : Γ(X, (U : X.Opens))) (ha : a ∈ J) :
    AlgebraicGeometry.Spec (CommRingCat.of
        (HomogeneousLocalization.Away J.reesGrading (J.reesX a ha))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (Ideal.affineBlowup J a)) where
  hom := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (J.reesAwayEquivAffineBlowup a ha).symm.toRingHom)
  inv := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (J.reesAwayEquivAffineBlowup a ha).toRingHom)
  hom_inv_id := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_id]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_id]
    congr 1
    ext x
    simp

/-- **Stacks 0804, second half**: `b⁻¹(U)` is covered by spectra of affine blowup algebras. For every
`a ∈ I(U)` there is an open `V_a ⊆ b⁻¹(U)` with `V_a ≅ Spec A[I/a]` (`A = Γ(X, U)`,
`A[I/a] = Ideal.affineBlowup ⊆ A_a`), such that under this isomorphism `b|_{V_a}` is the morphism
`Spec A[I/a] → Spec A ≅ U` induced by `A → A[I/a]`; and the `V_a` cover `b⁻¹(U)` (`V_a` is the basic
open `D₊(aX)` of the Proj). -/
theorem blowup_preimage_affine_cover :
    ∃ (V : I.ideal U → (AlgebraicGeometry.Scheme.blowup I).left.Opens)
      (hV : ∀ a, V a ≤ (AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ (U : X.Opens)),
      (∀ a, ∃ e : (V a).toScheme ≅
          AlgebraicGeometry.Spec (CommRingCat.of (Ideal.affineBlowup (I.ideal U) (a : Γ(X, U)))),
        e.inv ≫ (AlgebraicGeometry.Scheme.blowup I).left.homOfLE (hV a) ≫
            ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, U) (Ideal.affineBlowup (I.ideal U) (a : Γ(X, U)))))) ∧
      ⨆ a, V a = (AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ (U : X.Opens) := by
  obtain ⟨e, he, hunit⟩ := I.exists_reesAlgebra_sectionsRing_equiv U
  refine ⟨fun a => blowupChartι I U e he ''ᵁ
      Proj.basicOpen (Ideal.reesGrading (I.ideal U)) ((I.ideal U).reesX a a.2),
    fun a => blowupChartι_image_le I U e he _, fun a => ?_, ?_⟩
  · refine ⟨((blowupChartι I U e he).isoImage _).symm ≪≫
      Proj.basicOpenIsoSpec (Ideal.reesGrading (I.ideal U)) _ ((I.ideal U).reesX_mem a a.2) one_pos ≪≫
      specReesAwayIso U (I.ideal U) a a.2, ?_⟩
    rw [Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc, Category.assoc,
      blowupChartι_isoImage_hom_homOfLE_assoc, Proj.basicOpenIsoSpec_inv_ι_assoc,
      blowupPreimageIso_inv_morphismRestrict_isoSpec, Proj.awayι_toSpecZero_assoc]
    change AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ ≫
      AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ = _
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp,
      ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    have hr : (Proj.gradedRingHomOfRingEquiv e he).gradedZeroRingHom
        (I.reesAlgebra.sectionsUnitZero U r) =
        ⟨algebraMap Γ(X, (U : X.Opens)) (_root_.reesAlgebra (I.ideal U)) r,
          (I.ideal U).algebraMap_mem_reesGrading_zero r⟩ := by
      apply Subtype.ext
      exact hunit r
    rw [hr]
    exact congrArg Subtype.val ((I.ideal U).reesAwayEquivAffineBlowup_fromZeroRingHom a a.2 r)
  · rw [← Scheme.Hom.image_iSup, (I.ideal U).reesGrading_iSup_basicOpen_eq_top,
      Scheme.Hom.image_top_eq_opensRange, blowupChartι_opensRange]

end AlgebraicGeometry.Scheme

end
