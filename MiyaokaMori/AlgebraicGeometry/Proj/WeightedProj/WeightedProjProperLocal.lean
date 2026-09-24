import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-! # Properness of the local weighted Proj model

The structure morphism `weightedProjToSpec : Proj R[x]_w → Spec R` of the weighted polynomial Proj
is proper: it is `Proj.toSpecZero` followed by the isomorphism `Spec (R[x]_w)_0 ≅ Spec R`, and
`R[x]_w` is of finite type over its degree-zero part `(R[x]_w)_0 = R`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.WeightedJets

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section DegreeZero

variable (R : Type u) [CommRing R] {ι : Type v} (w : ι → ℕ+)

/-- A weighted homogeneous polynomial of degree `0` is its constant coefficient. -/
theorem local_weightedDegreeZero_eq_C (p : weightedPolynomialGrading R w 0) :
    MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial ι R)) =
      (p : MvPolynomial ι R) := by
  have hp : (p : MvPolynomial ι R).IsWeightedHomogeneous (fun i => (w i : ℕ)) 0 := p.2
  calc
    MvPolynomial.C (MvPolynomial.constantCoeff (p : MvPolynomial ι R)) =
        MvPolynomial.weightedHomogeneousComponent (fun i => (w i : ℕ)) 0
          (p : MvPolynomial ι R) := by
      simpa only [MvPolynomial.constantCoeff_eq] using
        (MvPolynomial.weightedHomogeneousComponent_zero (p : MvPolynomial ι R)
          (fun i => (w i).ne_zero)).symm
    _ = (p : MvPolynomial ι R) := hp.weightedHomogeneousComponent_same

/-- The degree-zero part of the weighted polynomial ring is the coefficient ring `R`. -/
def local_weightedDegreeZeroEquiv : weightedPolynomialGrading R w 0 ≃+* R where
  toFun p := MvPolynomial.constantCoeff (p : MvPolynomial ι R)
  invFun r := ⟨MvPolynomial.C r,
    MvPolynomial.isWeightedHomogeneous_C (fun i => (w i : ℕ)) r⟩
  left_inv p := Subtype.ext (local_weightedDegreeZero_eq_C R w p)
  right_inv r := MvPolynomial.constantCoeff_C ι r
  map_mul' p q := RingHom.map_mul (MvPolynomial.constantCoeff (R := R) (σ := ι)) p q
  map_add' p q := RingHom.map_add (MvPolynomial.constantCoeff (R := R) (σ := ι)) p q

theorem local_weightedDegreeZeroEquiv_symm_toRingHom :
    (local_weightedDegreeZeroEquiv R w).symm.toRingHom =
      algebraMap R (weightedPolynomialGrading R w 0) := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  rfl

/-- The weighted polynomial ring is of finite type over its degree-zero part. -/
theorem local_weightedPolynomial_finiteType_over_zero [Finite ι] :
    Algebra.FiniteType (weightedPolynomialGrading R w 0) (MvPolynomial ι R) := by
  have hTower : IsScalarTower R (weightedPolynomialGrading R w 0) (MvPolynomial ι R) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := weightedPolynomialGrading R w 0)
      (A := MvPolynomial ι R) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R
    (weightedPolynomialGrading R w 0) (MvPolynomial ι R)

end DegreeZero

section Geometry

variable (R : Type (max u v)) [CommRing R] {ι : Type v} (w : ι → ℕ+)

theorem local_weightedProjToSpec_eq_toSpecZero_comp :
    weightedProjToSpec R w = Proj.toSpecZero (weightedPolynomialGrading R w) ≫
      Spec.map (CommRingCat.ofHom (local_weightedDegreeZeroEquiv R w).symm.toRingHom) := by
  unfold weightedProjToSpec
  rw [local_weightedDegreeZeroEquiv_symm_toRingHom]
  rfl

/-- The structure morphism of the weighted polynomial Proj is proper. -/
theorem local_weightedProjToSpec_isProper [Finite ι] :
    IsProper (weightedProjToSpec R w) := by
  have hfinite : Algebra.FiniteType (weightedPolynomialGrading R w 0) (MvPolynomial ι R) :=
    local_weightedPolynomial_finiteType_over_zero R w
  have hIso : IsIso (CommRingCat.ofHom (local_weightedDegreeZeroEquiv R w).symm.toRingHom) :=
    (local_weightedDegreeZeroEquiv R w).symm.toCommRingCatIso.isIso_hom
  have hproj : IsProper (Proj.toSpecZero (weightedPolynomialGrading R w)) := inferInstance
  have hmap : IsProper
      (Spec.map (CommRingCat.ofHom (local_weightedDegreeZeroEquiv R w).symm.toRingHom)) :=
    inferInstance
  simpa only [weightedProjToSpec, weightedProj,
    local_weightedDegreeZeroEquiv_symm_toRingHom] using
    (inferInstance : IsProper (Proj.toSpecZero (weightedPolynomialGrading R w) ≫
      Spec.map (CommRingCat.ofHom (local_weightedDegreeZeroEquiv R w).symm.toRingHom)))

end Geometry

end MiyaokaMori.WeightedJets

end
