import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.ProjectiveLineSmoothProof
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineIrreducible
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothCurveDimension

/-! # The projective line is a smooth projective curve

`P¹_k` is a smooth connected projective curve (the source of the morphism `b : P¹ → X` in the
conclusion of the main theorem). Its dimension is
`AlgebraicGeometry.Scheme.topologicalKrullDim_eq_one_of_smoothOfRelativeDimension`, applied to the structure
morphism `ProjectiveLine k ↘ Spec k`, which is smooth of relative dimension one
(`projectiveLine_smoothOfRelativeDimension`) with nonempty source.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable abbrev ProjectiveLine.asSmoothProjectiveCurve (k : Type u) [Field k] :
    SmoothProjectiveCurve k := by
  letI : IrreducibleSpace (ProjectiveLine k) :=
    AlgebraicGeometry.Proj.ProjectiveLineIrreducible.projectiveLine_irreducible k
  letI : AlgebraicGeometry.SmoothOfRelativeDimension 1
      (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    MiyaokaMori.Paper.S1Intro.ProjectiveLineSmooth.projectiveLine_smoothOfRelativeDimension k
  refine {
    carrier := ProjectiveLine k
    smooth := ?_
    projective := ?_
    connected := ?_
    dim_one := ?_ }
  · change AlgebraicGeometry.Smooth (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    exact AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1
      (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  · refine ⟨1, CategoryTheory.CategoryStruct.id _, inferInstance, ?_⟩
    constructor
    simp
  · infer_instance
  · change topologicalKrullDim (ProjectiveLine k) = 1
    exact AlgebraicGeometry.Scheme.topologicalKrullDim_eq_one_of_smoothOfRelativeDimension
      (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

end
