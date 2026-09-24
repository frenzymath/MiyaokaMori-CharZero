import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegreePullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.StructureMorphismIsOver
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreePullbackFinite
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Degree of a pullback along a finite cover

The degree `e = deg ρ = [K(C̃) : K(C)]` of a finite cover of curves, and the formula
`deg (ρ^* A) = e · deg A`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of a finite cover: `AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree ρ.hom = [K(C̃) : K(C)]`
(this needs `IsDominant`: a finite surjection is dominant). -/

noncomputable def FiniteCover.degree {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (ρ : FiniteCover k C) : ℕ :=
  haveI := ρ.source.isIntegral; haveI := C.isIntegral
  haveI : AlgebraicGeometry.IsDominant ρ.hom := inferInstance
  AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree ρ.hom

/-- A finite cover has strictly positive function-field degree. -/
theorem FiniteCover.degree_pos {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (ρ : FiniteCover k C) :
    0 < ρ.degree := by
  unfold FiniteCover.degree
  exact AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree_pos ρ.hom

private theorem functionFieldDegree_eq_finiteMapFunctionFieldDegree
    {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (ρ : FiniteCover k C) :
    functionFieldDegree ρ.hom = AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree ρ.hom := by
  have hff := functionFieldDegree_eq_finrank ρ.hom ρ.hom_genericPoint
  unfold AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree
  rw [hff]
  let A1 : Algebra C.toScheme.functionField ρ.source.toScheme.functionField :=
    @AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ρ.source.toScheme C.toScheme
      ρ.source.isIntegral C.isIntegral ρ.hom inferInstance
  let A2 : Algebra C.toScheme.functionField ρ.source.toScheme.functionField :=
    ((C.toScheme.functionFieldIsoResidueField.hom ≫
      (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
      ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
      ρ.source.toScheme.functionFieldIsoResidueField.inv).hom.toAlgebra)
  have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap ρ.hom =
      C.toScheme.functionFieldIsoResidueField.hom ≫
        (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
        ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
        ρ.source.toScheme.functionFieldIsoResidueField.inv := by
    unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
    apply (cancel_mono (ρ.source.toScheme.residue (genericPoint ρ.source.toScheme))).1
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
    rw [← Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
    simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
    exact ρ.hom_genericPoint.symm
  have hA : A2 = A1 := by
    apply Algebra.algebra_ext
    intro r
    change ((C.toScheme.functionFieldIsoResidueField.hom ≫
      (C.toScheme.residueFieldCongr ρ.hom_genericPoint.symm).hom ≫
      ρ.hom.residueFieldMap (genericPoint ρ.source.toScheme) ≫
      ρ.source.toScheme.functionFieldIsoResidueField.inv).hom r) =
      (AlgebraicGeometry.Scheme.dominantFunctionFieldMap ρ.hom).hom r
    exact congrArg (fun q => q.hom r) hmap.symm
  change @Module.finrank C.toScheme.functionField ρ.source.toScheme.functionField _ _
      (@Algebra.toModule _ _ _ _ A2) =
    @Module.finrank C.toScheme.functionField ρ.source.toScheme.functionField _ _
      (@Algebra.toModule _ _ _ _ A1)
  rw [hA]

/-- `deg (ρ^* A) = deg ρ · deg A` for a finite cover `ρ` of smooth projective curves. -/
theorem LineBundle.degree_pullback_finiteCover {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (ρ : FiniteCover k C) (A : LineBundle C.toVariety) :
    (LineBundle.pullback (X := ρ.source.toVariety) ρ.hom A).degree = (ρ.degree : ℤ) * A.degree := by
  -- `LineBundle.degree` is characterized by the relation `HasCurveModuleDegree`; the pullback
  -- formula is `curveModuleDegree_pullback_finite` (Stacks 02RH)
  let X : AlgebraicGeometry.Proj.SchemeOver k :=
    ⟨ρ.source.toScheme, ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩
  let Y : AlgebraicGeometry.Proj.SchemeOver k :=
    ⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩
  letI : AlgebraicGeometry.IsIntegral X.scheme := SmoothProjectiveCurve.isIntegral ρ.source
  letI : AlgebraicGeometry.IsIntegral Y.scheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsProper X.toBase :=
    IsProjectiveOver.isProper ρ.source.projective
  letI : AlgebraicGeometry.IsProper Y.toBase :=
    IsProjectiveOver.isProper C.projective
  have hf : ρ.hom ≫ Y.toBase = X.toBase := ρ.isOver
  letI : AlgebraicGeometry.IsFinite ρ.hom := ρ.finite
  letI : AlgebraicGeometry.IsDominant ρ.hom := inferInstance
  have hA := AlgebraicGeometry.VectorBundle.isLocallyFreeRank (C := C) A.toVectorBundle
  rw [A.rank_eq_one] at hA
  exact LineBundle.degree_eq_of_hasCurveModuleDegree _
    (AlgebraicGeometry.Intersection.curveModuleDegree_pullback_finite X Y
      (by rw [ρ.source.dim_one]) (by rw [C.dim_one]) ρ.hom hf A.toModules hA
      (LineBundle.degree_spec A))

end
