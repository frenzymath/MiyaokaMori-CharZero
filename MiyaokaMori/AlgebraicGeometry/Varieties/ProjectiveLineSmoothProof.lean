import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLinePointCoordinates
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-! # The projective line is smooth of relative dimension one

The standard projective line `P^1_k → Spec k` over any field is smooth of relative dimension `1`.

Proof sketch:
1. On the two standard opens, identify the homogeneous localization with `Polynomial k` and check
   that this identification is compatible with the structure morphism to the base field.
2. Show that `Polynomial k` is standard smooth of relative dimension `1` using the submersive
   presentation with one generator and no relations.
3. Glue with the Zariski locality of smoothness on the source and the cover by the two coordinate
   opens.

Source: Stacks, Constructions (the standard cover of projective space).
-/

/-!
# Relative smoothness of the projective line

The two standard opens of `P^1` are affine lines.  This file supplies the
coordinate-ring calculation and the locality bridge needed to turn that fact
into `SmoothOfRelativeDimension 1` for the canonical structure morphism.
-/

noncomputable section

set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory
open RingHom
open AlgebraicGeometry.Proj AlgebraicGeometry.Scheme
open AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace MiyaokaMori.Paper.S1Intro.ProjectiveLineSmooth

variable {k : Type u} [Field k]

private def affineCoordinates (i j : Fin 2) : Polynomial k :=
  if j = i then 1 else Polynomial.X

private def affineEvaluation (i : Fin 2) : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (affineCoordinates i)

@[simp] private theorem affineEvaluation_X_self (i : Fin 2) :
    affineEvaluation (k := k) i (MvPolynomial.X i) = 1 := by
  simp [affineEvaluation, affineCoordinates]

private def chartToPolynomial (i : Fin 2) : chartRing (k := k) i →+* Polynomial k :=
  (IsLocalization.Away.lift (R := MvPolynomial (Fin 2) k)
    (S := Localization.Away (M := MvPolynomial (Fin 2) k) (MvPolynomial.X i))
    (MvPolynomial.X i)
    (P := Polynomial k) (g := affineEvaluation i)
    (show IsUnit (affineEvaluation (k := k) i (MvPolynomial.X i)) by
      rw [affineEvaluation_X_self]
      exact isUnit_one)).comp
      (algebraMap (chartRing (k := k) i)
        (Localization.Away (M := MvPolynomial (Fin 2) k) (MvPolynomial.X i)))

private theorem chartToPolynomial_mk (i : Fin 2) (n : ℕ) (f : MvPolynomial (Fin 2) k)
    (hf : f ∈ projectiveGrading k 1 (n • 1)) :
    chartToPolynomial i
      (HomogeneousLocalization.Away.mk (projectiveGrading k 1)
        (by
          simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_X k i)) n f hf) =
      affineEvaluation i f := by
  let l := IsLocalization.Away.lift (R := MvPolynomial (Fin 2) k)
    (S := Localization.Away (M := MvPolynomial (Fin 2) k) (MvPolynomial.X i))
    (MvPolynomial.X i)
    (P := Polynomial k) (g := affineEvaluation i)
    (show IsUnit (affineEvaluation (k := k) i (MvPolynomial.X i)) by
      rw [affineEvaluation_X_self]
      exact isUnit_one)
  have h := congrArg l
    (IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X (R := k) i))
      f (⟨MvPolynomial.X i ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X i)))
  simpa only [chartToPolynomial, Localization.Away, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', map_mul, l, IsLocalization.Away.lift_eq,
    map_pow, affineEvaluation_X_self, one_pow, mul_one] using h

@[simp] private theorem chartToPolynomial_coefficient (i : Fin 2) (r : k) :
    chartToPolynomial i (chartCoefficient i r) = Polynomial.C r := by
  change chartToPolynomial i
    (HomogeneousLocalization.Away.mk (projectiveGrading k 1)
      (by
        simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_X k i)) 0
      (MvPolynomial.C r)
      (by
        simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_C (Fin 2) r))) = _
  rw [chartToPolynomial_mk]
  simp [affineEvaluation]

@[simp] private theorem chartToPolynomial_ratio (i j : Fin 2) :
    chartToPolynomial (k := k) i (coordinateRatio (k := k) i j) = affineCoordinates i j := by
  rw [coordinateRatio, chartToPolynomial_mk]
  simp [affineEvaluation, affineCoordinates]

private def polynomialToChart (i : Fin 2) : Polynomial k →+* chartRing (k := k) i :=
  Polynomial.eval₂RingHom (chartCoefficient i) (coordinateRatio i i.rev)

private theorem chartToPolynomial_comp_polynomialToChart (i : Fin 2) :
    (chartToPolynomial (k := k) i).comp (polynomialToChart i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [polynomialToChart]
  · fin_cases i <;> simp [polynomialToChart, affineCoordinates]

private theorem polynomialToChart_comp_affineEvaluation (i : Fin 2) :
    (polynomialToChart (k := k) i).comp (affineEvaluation i) = dehomogenization i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affineEvaluation, polynomialToChart, dehomogenization]
  · intro j
    fin_cases i <;> fin_cases j <;>
      simp [affineEvaluation, affineCoordinates, polynomialToChart, dehomogenization]

private theorem polynomialToChart_surjective (i : Fin 2) :
    Function.Surjective (polynomialToChart (k := k) i) := by
  intro z
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projectiveGrading k 1) (by
      simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_X k i)) z
  refine ⟨affineEvaluation i f, ?_⟩
  change ((polynomialToChart i).comp (affineEvaluation i)) f = _
  rw [polynomialToChart_comp_affineEvaluation]
  exact dehomogenization_of_homogeneous i (by simpa using hf)

private def chartPolynomialEquiv (i : Fin 2) : Polynomial k ≃+* chartRing (k := k) i :=
  RingEquiv.ofBijective (polynomialToChart i)
    ⟨fun p q hpq ↦ by
      have h := congrArg (chartToPolynomial i) hpq
      have hleft (r : Polynomial k) : chartToPolynomial i (polynomialToChart i r) = r :=
        RingHom.congr_fun (chartToPolynomial_comp_polynomialToChart i) r
      simpa only [hleft] using h,
    polynomialToChart_surjective i⟩

private theorem chartPolynomialEquiv_comp_C (i : Fin 2) :
    (chartPolynomialEquiv (k := k) i).toRingHom.comp Polynomial.C = chartCoefficient i := by
  ext r
  simp [chartPolynomialEquiv, polynomialToChart]

private def standardChartIso (i : Fin 2) :
    (Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)).toScheme ≅
      Spec (CommRingCat.of (Polynomial k)) :=
  Proj.basicOpenIsoSpec (projectiveGrading k 1) (MvPolynomial.X i)
    (by
      simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_X k i)) (by decide) ≪≫
      Scheme.Spec.mapIso (chartPolynomialEquiv i).toCommRingCatIso.op

private theorem standardChartIso_over_base (i : Fin 2) :
    (standardChartIso (k := k) i).hom ≫ Spec.map (CommRingCat.ofHom Polynomial.C) =
      (Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)).ι ≫
        (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) := by
  let hdeg : MvPolynomial.X i ∈ projectiveGrading k 1 1 := by
    simpa [projectiveGrading] using (MvPolynomial.isHomogeneous_X k i)
  let hm : 0 < (1 : ℕ) := by decide
  change ((Proj.basicOpenIsoSpec (projectiveGrading k 1) (MvPolynomial.X i)
    hdeg hm).hom ≫ Spec.map (CommRingCat.ofHom (chartPolynomialEquiv i).toRingHom)) ≫ _ = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartPolynomialEquiv_comp_C, ← chartι_over_base]
  change Proj.basicOpenToSpec (projectiveGrading k 1) (MvPolynomial.X i) ≫
      (Proj.basicOpenIsoSpec (projectiveGrading k 1) (MvPolynomial.X i)
        hdeg hm).inv ≫
      (Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)).ι ≫
      (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) = _
  rw [← Proj.basicOpenIsoSpec_hom (projectiveGrading k 1) (MvPolynomial.X i) hdeg hm]
  simp

private def polynomialPresentation (k : Type u) [Field k] :
    Algebra.SubmersivePresentation k (MvPolynomial Unit k) Unit (Fin 0) where
  toGenerators := Algebra.Generators.mvPolynomial k Unit
  relation := Fin.elim0
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Algebra.Generators.ker_mvPolynomial]
  map := Fin.elim0
  map_inj := fun a b h => Fin.elim0 a
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

private theorem polynomial_standardSmooth (k : Type u) [Field k] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial Unit k) :=
    (polynomialPresentation k).isStandardSmoothOfRelativeDimension
      (by simp [Algebra.Presentation.dimension])
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv k Unit)

private theorem affineLine_smooth (k : Type u) [Field k] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap k (Polynomial k))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact polynomial_standardSmooth k

private theorem chart_smooth (i : Fin 2) :
    SmoothOfRelativeDimension 1
      ((Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)).ι ≫
        (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k))) := by
  letI :=
    instHasRingHomPropertySmoothOfRelativeDimensionLocallyIsStandardSmoothOfRelativeDimension 1
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @SmoothOfRelativeDimension 1)]
    exact AlgebraicGeometry.affineLocally_respectsIso
      (P := Locally (IsStandardSmoothOfRelativeDimension 1))
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  rw [← standardChartIso_over_base]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    (standardChartIso i).hom _).mpr (affineLine_smooth k)

private theorem smooth_dim_locality :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) := by
  letI :=
    instHasRingHomPropertySmoothOfRelativeDimensionLocallyIsStandardSmoothOfRelativeDimension 1
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @SmoothOfRelativeDimension 1)]
    exact AlgebraicGeometry.affineLocally_respectsIso
      (P := Locally (IsStandardSmoothOfRelativeDimension 1))
      (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  letI : HasAffineProperty (@SmoothOfRelativeDimension 1)
      (sourceAffineLocally (Locally (IsStandardSmoothOfRelativeDimension 1))) :=
    HasRingHomProperty.HasAffineProperty (@SmoothOfRelativeDimension 1)
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  apply HasAffineProperty.isZariskiLocalAtSource
  intro X Y f _ 𝒰
  letI (i : 𝒰.affineRefinement.openCover.I₀) :
      IsAffine (𝒰.affineRefinement.openCover.X i) := by
    change IsAffine (Spec _)
    infer_instance
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension 1),
    HasRingHomProperty.iff_of_source_openCover 𝒰.affineRefinement.openCover,
    fun i ↦ HasRingHomProperty.iff_of_source_openCover
      (P := @SmoothOfRelativeDimension 1) (f := 𝒰.f i ≫ f) (𝒰.X i).affineCover]
  simp [Scheme.OpenCover.affineRefinement, Sigma.forall]

/-- The canonical projective line is smooth of relative dimension one over its field. -/
theorem projectiveLine_smoothOfRelativeDimension (k : Type u) [Field k] :
    SmoothOfRelativeDimension 1 (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) := smooth_dim_locality
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1)
    (fun i : Fin 2 => Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i))
    (coordinateOpens_cover (k := k))
  intro i
  exact chart_smooth i

end MiyaokaMori.Paper.S1Intro.ProjectiveLineSmooth
