import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0804

/-! # The charts of Stacks 0804 meet, and restriction on a chart is injective

Two geometric complements to Stacks 0804 (`blowup_preimage_affine_cover`) needed for
Stacks 0AGS(4) `Γ(Bl_𝔪 Spec A, O) = A` (`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_sections`):

* `Ideal.exists_mem_basicOpen_reesX`: when `A` is a domain, the generic point `(0)` of `Proj (⊕ₙ Jⁿ)`
  (the Rees algebra is a domain, so `⊥` is a relevant homogeneous prime) lies in every `D₊(aX)`,
  `a ∈ J ∖ {0}`;
* `AlgebraicGeometry.Scheme.blowup_preimage_affine_cover_generic`: the cover of Stacks 0804, with the
  additional information that any two charts `V_a`, `V_b` (`a, b ≠ 0`) have a common point (the image of
  the generic point). This cannot be extracted from the existential statement
  `blowup_preimage_affine_cover` (its data is also satisfied by a disjoint union of the charts), so the
  construction `blowupChartι` of `Stacks0804.lean` is rerun here;
* `AlgebraicGeometry.Scheme.presheaf_map_injective_of_iso_spec_of_isDomain`: if `V ≅ Spec R` with `R` a
  domain and `∅ ≠ W ≤ V`, then `Γ(X, V) → Γ(X, W)` is injective (`V` is an integral scheme,
  `map_injective_of_isIntegral`, transported along `V.ι`).

Source: Stacks 0804; Stacks 0AGS proof of (4); Stacks 01OM (sections of an integral scheme restrict
injectively).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Ideal

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- `aX ≠ 0` in the Rees algebra when `a ≠ 0`. -/
theorem reesX_ne_zero {a : A} (ha : a ∈ J) (ha0 : a ≠ 0) : J.reesX a ha ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_reesX, Subalgebra.coe_zero, Polynomial.monomial_eq_zero_iff] at h'
  exact ha0 h'

/-- **The generic point of `Proj (⊕ₙ Jⁿ)`.** `A` a domain, `J` an ideal containing a nonzero element.
The zero ideal of the Rees algebra (a domain inside `A[X]`) is a homogeneous prime not containing the
irrelevant ideal (which contains `a₀X ≠ 0`), i.e. a point `η` of `Proj (⊕ₙ Jⁿ)`, and `η ∈ D₊(aX)` for
every nonzero `a ∈ J` since `aX ≠ 0`. -/
theorem exists_mem_basicOpen_reesX [IsDomain A] {a₀ : A} (ha₀ : a₀ ∈ J) (ha₀0 : a₀ ≠ 0) :
    ∃ η : AlgebraicGeometry.Proj J.reesGrading,
      ∀ (a : A) (ha : a ∈ J), a ≠ 0 → η ∈ AlgebraicGeometry.Proj.basicOpen J.reesGrading (J.reesX a ha) := by
  have hprime : ((⊥ : HomogeneousIdeal J.reesGrading).toIdeal).IsPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  have hirr : ¬ HomogeneousIdeal.irrelevant J.reesGrading ≤ (⊥ : HomogeneousIdeal J.reesGrading) := by
    intro hle
    have hmem : J.reesX a₀ ha₀ ∈ HomogeneousIdeal.irrelevant J.reesGrading := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne J.reesGrading (J.reesX_mem a₀ ha₀) one_ne_zero]
    have h0 : J.reesX a₀ ha₀ ∈ (⊥ : HomogeneousIdeal J.reesGrading) := hle hmem
    rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
    exact J.reesX_ne_zero ha₀ ha₀0 h0
  refine ⟨⟨⊥, hprime, hirr⟩, fun a ha ha0 h => ?_⟩
  change J.reesX a ha ∈ (⊥ : HomogeneousIdeal J.reesGrading) at h
  rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h
  exact J.reesX_ne_zero ha ha0 h

end Ideal

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- **Stacks 0804 with a generic point.** Same statement as `blowup_preimage_affine_cover`
(Stacks 0804), plus: when `Γ(X, U)` is a domain, any two charts `V_a`, `V_b` with `a, b ≠ 0`
have a common point. The proof is that of `blowup_preimage_affine_cover` (the charts are the images
of the basic opens `D₊(aX)` of `Proj (⊕ₙ I(U)ⁿ)` under the open immersion `blowupChartι`), and the
common point is the image of the generic point of `Proj (⊕ₙ I(U)ⁿ)` (`Ideal.exists_mem_basicOpen_reesX`),
which lies in every `D₊(aX)`, `a ≠ 0`. -/
theorem blowup_preimage_affine_cover_generic [IsDomain Γ(X, U)] :
    ∃ (V : I.ideal U → (AlgebraicGeometry.Scheme.blowup I).left.Opens)
      (hV : ∀ a, V a ≤ (AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ (U : X.Opens)),
      (∀ a, ∃ e : (V a).toScheme ≅
          AlgebraicGeometry.Spec (CommRingCat.of (Ideal.affineBlowup (I.ideal U) (a : Γ(X, U)))),
        e.inv ≫ (AlgebraicGeometry.Scheme.blowup I).left.homOfLE (hV a) ≫
            ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ (U : X.Opens)) ≫ U.2.isoSpec.hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, U) (Ideal.affineBlowup (I.ideal U) (a : Γ(X, U)))))) ∧
      ⨆ a, V a = (AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ (U : X.Opens) ∧
      ∀ a b : I.ideal U, (a : Γ(X, U)) ≠ 0 → (b : Γ(X, U)) ≠ 0 →
        ∃ p : ↑(AlgebraicGeometry.Scheme.blowup I).left, p ∈ V a ∧ p ∈ V b := by
  obtain ⟨e, he, hunit⟩ := I.exists_reesAlgebra_sectionsRing_equiv U
  refine ⟨fun a => blowupChartι I U e he ''ᵁ
      Proj.basicOpen (Ideal.reesGrading (I.ideal U)) ((I.ideal U).reesX a a.2),
    fun a => blowupChartι_image_le I U e he _, fun a => ?_, ?_, ?_⟩
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
  · intro a b ha hb
    obtain ⟨η, hη⟩ := (I.ideal U).exists_mem_basicOpen_reesX a.2 ha
    exact ⟨blowupChartι I U e he η, ⟨η, hη a a.2 ha, rfl⟩, ⟨η, hη b b.2 hb, rfl⟩⟩

/-- **Restriction from an integral affine chart is injective.** `V` an open of `X` with `V ≅ Spec R`,
`R` a domain, and `W ≤ V` nonempty. Then `Γ(X, V) → Γ(X, W)` is injective: `V` is an integral scheme
(`isIntegral_of_isOpenImmersion` along the isomorphism), so restriction between nonempty opens of `V`
is injective (`map_injective_of_isIntegral`, Stacks 01OM), and the restriction on `X` is identified with
it through the isomorphisms `V.ι.app` (`Scheme.Hom.naturality`, `isIso_app`). -/
theorem presheaf_map_injective_of_iso_spec_of_isDomain (V W : X.Opens) (h : W ≤ V)
    (R : CommRingCat.{u}) [IsDomain R] (e : V.toScheme ≅ AlgebraicGeometry.Spec R)
    (hW : (W : Set X).Nonempty) :
    Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  obtain ⟨p, hp⟩ := hW
  have : Nonempty V.toScheme := ⟨⟨p, h hp⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion e.hom
  have : Nonempty ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Type u) := ⟨⟨⟨p, h hp⟩, hp⟩⟩
  have : IsIso (V.ι.app V) := V.ι.isIso_app V (by rw [Scheme.Opens.opensRange_ι])
  have hnat := V.ι.naturality (homOfLE h).op
  have hrhs : Function.Injective ((X.presheaf.map (homOfLE h).op ≫ V.ι.app W).hom) := by
    rw [hnat, CommRingCat.hom_comp]
    exact (map_injective_of_isIntegral V.toScheme _).comp
      (ConcreteCategory.bijective_of_isIso (V.ι.app V)).1
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at hrhs
  exact hrhs.of_comp

end AlgebraicGeometry.Scheme

end
