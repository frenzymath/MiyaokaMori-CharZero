import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalizationFunctionField

/-! # Function field of the normalization in a finite extension

The normalization `Y'` of an integral scheme `Y` in a finite extension `K` of its function field
is an integral scheme whose generic point maps to the generic point of `Y`; its function field is
`K`, and the function field degree of `Y' → Y` is `[K : K(Y)]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.normalization_functionField {Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Y] (K : Type u) [Field K] [Algebra Y.functionField K]
    [Module.Finite Y.functionField K] :
    let ι := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
      Y.fromSpecStalk (genericPoint Y)
    AlgebraicGeometry.IsIntegral ι.normalization ∧
      ι.fromNormalization.base (genericPoint ι.normalization) = genericPoint Y ∧
      Nonempty (ι.normalization.functionField ≅ CommRingCat.of K) ∧
      functionFieldDegree ι.fromNormalization = Module.finrank Y.functionField K := by
  intro ι
  -- `ι` is by definition `curveExtensionGenericMap Y K`, so `ι.normalization` is
  -- `curveFieldNormalization Y K` and `ι.fromNormalization` is `curveFieldNormalizationMap Y K`.
  let C := AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Y K
  let ν : C ⟶ Y := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Y K
  have hgen : ν.base (genericPoint C) = genericPoint Y := AlgebraicGeometry.Scheme.dominantMap_genericPoint ν
  refine ⟨inferInstanceAs (AlgebraicGeometry.IsIntegral C), hgen, ?_, ?_⟩
  · let _ := AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ν
    exact ⟨(AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldEquiv Y K).toRingEquiv.toCommRingCatIso⟩
  · change functionFieldDegree ν = _
    rw [functionFieldDegree_eq_finrank ν hgen]
    let A1 : Algebra Y.functionField C.functionField := AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ν
    let A2 : Algebra Y.functionField C.functionField :=
      (Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hgen.symm).hom ≫
        ν.residueFieldMap (genericPoint C) ≫ C.functionFieldIsoResidueField.inv).hom.toAlgebra
    have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap ν =
        Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hgen.symm).hom ≫
          ν.residueFieldMap (genericPoint C) ≫ C.functionFieldIsoResidueField.inv := by
      unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      apply (cancel_mono (C.residue (genericPoint C))).1
      simp only [Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
      rw [← Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
      simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
      exact hgen.symm
    have hA : A2 = A1 := by
      apply Algebra.algebra_ext
      intro r
      change ((Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hgen.symm).hom ≫
        ν.residueFieldMap (genericPoint C) ≫ C.functionFieldIsoResidueField.inv).hom r) =
        (AlgebraicGeometry.Scheme.dominantFunctionFieldMap ν).hom r
      exact congrArg (fun q => q.hom r) hmap.symm
    let finrankOf : Algebra Y.functionField C.functionField → ℕ :=
      fun A => letI := A; Module.finrank Y.functionField C.functionField
    change finrankOf A2 = _
    rw [congrArg finrankOf hA]
    let _ := A1
    exact LinearEquiv.finrank_eq
      (AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldEquiv Y K).toLinearEquiv

end
