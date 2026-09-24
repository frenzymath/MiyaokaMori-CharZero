import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.HyperplaneGradedHom
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapClosedImmersionOfSurjective
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightNeOne

/-! # The hyperplane of projective space, part 2: `j = Proj.map φ : P^m → P^{m+1}` is a closed
immersion with kernel the ideal sheaf of `x_{m+1} ∈ Γ(O(1))`

Steps 2–3 of the docstring of `projectiveSpace_hyperplane_iso`: `j` is a closed immersion
(`Proj.isClosedImmersion_map`, `φ` surjective in every degree), and `j.ker = Z(x_{m+1})` as ideal sheaves
on `P^{m+1}`. The latter is checked on the affine cover `D_+(x_i)` (`IdealSheafData.ext_of_iSup_eq_top`):
`j.ker(D_+(x_i)) = ker (A_{(x_i)} → B_{(φ x_i)})` (`Scheme.Hom.ker_apply`, `Proj.awayToSection_comp_appLE`)
`= (x_{m+1}/x_i)` (`ker_awayMap_eq`, part 1), while `Z(x_{m+1})(D_+(x_i)) = (x_{m+1}/x_i)` because `x_i` is a
frame of `O(1)` on `D_+(x_i)` and `x_{m+1} = (x_{m+1}/x_i) · x_i` (`idealSheafOfSection_ideal_eq_span_singleton`).
Source: Stacks 01MZ; Hartshorne II Ex. 3.12(a); used for `Y₁^GG = P(E)` in Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
open scoped AlgebraicGeometry HomogeneousIdeal

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry MiyaokaMori.WeightedJets.ProjTwisting AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] (m : ℕ)

/-- `j = Proj.map φ : P^m_K → P^{m+1}_K`, the closed immersion onto the hyperplane `x_{m+1} = 0`. -/
def hyperplaneMap : ProjectiveSpace m K ⟶ ProjectiveSpace (m + 1) K :=
  Proj.map (hyperplaneGradedHom K m) (irrelevant_le_map_hyperplaneGradedHom K m)

/-- Step 2: `j` is a closed immersion (`φ` is surjective in every degree). Not a global instance
(to keep instance search downstream unchanged); supply it locally with `have := isClosedImmersion_hyperplaneMap K m`. -/
theorem isClosedImmersion_hyperplaneMap : IsClosedImmersion (hyperplaneMap K m) :=
  Proj.isClosedImmersion_map _ _ (hyperplaneGradedHom_surjective_degree K m)

/-- The local equation `x_{m+1}/x_i ∈ Γ(P^{m+1}, D_+(x_i))` of the hyperplane. -/
def coordSection (i : Fin (m + 2)) :
    Γ(ProjectiveSpace (m + 1) K, Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)) :=
  (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)).hom (coordFraction K m i)

/-- `x_{m+1}|_{D_+(x_i)} = (x_{m+1}/x_i) • x_i|_{D_+(x_i)}` in `Γ(D_+(x_i), O(1))`. -/
theorem coordSection_smul_frame (i : Fin (m + 2)) :
    coordSection K m i • homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1 (X i) (X_mem_one K m i)
        (Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)) =
      (projectiveSpaceTwist K (m + 1) 1).presheaf.map (homOfLE le_top).op
        (projectiveSpaceCoordinate K (m + 1) (Fin.last (m + 1))) := by
  apply Subtype.ext
  funext x
  change ((coordSection K m i).1 x).val * Localization.mk (X i) 1 = Localization.mk (X (Fin.last (m + 1))) 1
  have hpow : X i ^ 1 ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl := by
    rw [pow_one]; exact x.2
  have h1 : ((coordSection K m i).1 x).val =
      Localization.mk (X (Fin.last (m + 1))) ⟨X i ^ 1, hpow⟩ := by
    have h := ProjectiveSpectrum.Proj.awayToSection_apply (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)
      (coordFraction K m i) x
    refine h.trans ?_
    rw [coordFraction, Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
    rfl
  rw [h1, Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  change 1 * (X (Fin.last (m + 1)) * X i) = X i ^ 1 * 1 * X (Fin.last (m + 1))
  ring

/-- `x_i` is a frame of `O(1)` on `D_+(x_i)`. -/
theorem isFrame_coordinate (i : Fin (m + 2)) :
    IsFrame (projectiveSpaceTwist K (m + 1) 1) (Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i))
      (homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1 (X i) (X_mem_one K m i)
        (Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i))) :=
  isFrame_homogeneousSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) 1 (X i) (X_mem_one K m i) _
    fun y => y.2

/-- On the chart `D_+(x_i)`, `j^♯ : Γ(P^{m+1}, D_+(x_i)) → Γ(P^m, D_+(φ x_i))` is `Away.map φ` under the
chart isomorphisms `awayToSection` (`Proj.awayToSection_comp_appLE`). -/
theorem hyperplaneMap_app_awayToSection (i : Fin (m + 2))
    (z : Away (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)) :
    ((hyperplaneMap K m).app (Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i))).hom
        ((Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)).hom z) =
      (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K m) (hyperplaneGradedHom K m (X i))).hom
        (Away.map (hyperplaneGradedHom K m) (X i) z) := by
  have h := Proj.awayToSection_comp_appLE (hyperplaneGradedHom K m)
    (irrelevant_le_map_hyperplaneGradedHom K m) (X_mem_one K m i)
  have h2 := congrArg (fun g => g.hom z) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [Scheme.Hom.app_eq_appLE]
  exact h2

/-- **`j.ker = Z(x_{m+1})`** (step 3 of `projectiveSpace_hyperplane_iso`): compare on the affine cover
`D_+(x_i)`. -/
theorem hyperplaneMap_ker :
    (hyperplaneMap K m).ker = Scheme.idealSheafOfSection (projectiveSpaceTwist K (m + 1) 1)
      (projectiveSpaceCoordinate K (m + 1) (Fin.last (m + 1))) := by
  have := isClosedImmersion_hyperplaneMap K m
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : Fin (m + 2) => ⟨Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i),
      Proj.isAffineOpen_basicOpen _ (X i) (X_mem_one K m i) one_pos⟩)
    (projectiveSpace_iSup_basicOpen_X K (m + 1)) fun i => ?_
  rw [Scheme.Hom.ker_apply, Scheme.idealSheafOfSection_ideal_eq_span_singleton _ _ _ _
    (isFrame_coordinate K m i _ le_rfl) (coordSection K m i) (coordSection_smul_frame K m i)]
  have hiso : IsIso (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)) := by
    rw [← Proj.basicOpenIsoAway_hom _ (X i) (X_mem_one K m i) one_pos]; infer_instance
  have hbij : Function.Bijective (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hisoB : IsIso (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K m) (hyperplaneGradedHom K m (X i))) := by
    have hφX : hyperplaneGradedHom K m (X i) ∈ AlgebraicGeometry.Proj.projectiveGrading K m 1 :=
      killLast_mem K m (X_mem_one K m i)
    rw [← Proj.basicOpenIsoAway_hom _ _ hφX one_pos]
    infer_instance
  have hinjB : Function.Injective
      (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K m) (hyperplaneGradedHom K m (X i))).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hspan : Ideal.span {coordSection K m i} =
      (RingHom.ker (Away.map (hyperplaneGradedHom K m) (X i))).map
        (Proj.awayToSection (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i)).hom := by
    rw [ker_awayMap_eq, Ideal.map_span, Set.image_singleton]; rfl
  rw [hspan]
  ext y
  obtain ⟨z, rfl⟩ := hbij.2 y
  rw [RingHom.mem_ker, hyperplaneMap_app_awayToSection, Ideal.mem_map_iff_of_surjective _ hbij.2]
  constructor
  · intro h
    exact ⟨z, RingHom.mem_ker.mpr (hinjB (by rw [h, map_zero])), rfl⟩
  · rintro ⟨w, hw, hwz⟩
    rw [hbij.1 hwz] at hw
    rw [RingHom.mem_ker.mp hw, map_zero]

end ProjBundleFiberDegreeOne

end
