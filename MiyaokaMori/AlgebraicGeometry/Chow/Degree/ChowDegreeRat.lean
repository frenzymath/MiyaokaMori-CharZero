import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme

/-! # Degree of zero-dimensional Chow classes with rational coefficients

The degree `deg : A_0(X)_ℚ →ₗ[ℚ] ℚ` of zero-dimensional Chow classes with rational coefficients
(`X` proper over `K`), obtained by tensoring the degree of zero-cycles with `ℚ`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree `deg : A_0(X)_ℚ →ₗ[ℚ] ℚ` of zero-dimensional Chow classes with rational coefficients,
obtained by tensoring `ChowGroup.degreeOver` with `ℚ`. -/
noncomputable def AlgebraicGeometry.ChowGroupRat.degree {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) :
    AlgebraicGeometry.ChowGroupRat X 0 →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap ∘ₗ
    LinearMap.baseChange ℚ (AlgebraicGeometry.ChowGroup.degreeOver K X hX).toIntLinearMap

@[simp] theorem AlgebraicGeometry.ChowGroupRat.degree_tmul {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (q : ℚ) (c : AlgebraicGeometry.ChowGroup X 0) :
    AlgebraicGeometry.ChowGroupRat.degree X hX (q ⊗ₜ[ℤ] c)
      = q * (AlgebraicGeometry.ChowGroup.degreeOver K X hX c : ℚ) := by
  change (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap
      ((LinearMap.baseChange ℚ
        (AlgebraicGeometry.ChowGroup.degreeOver K X hX).toIntLinearMap)
        (q ⊗ₜ[ℤ] c)) = _
  rw [LinearMap.baseChange_tmul]
  change (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)
      (q ⊗ₜ[ℤ] (AlgebraicGeometry.ChowGroup.degreeOver K X hX).toIntLinearMap c) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [← Int.cast_smul_eq_zsmul ℚ]
  simp only [smul_eq_mul]
  exact mul_comm _ _

end
