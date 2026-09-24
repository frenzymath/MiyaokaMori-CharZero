import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveFactorEquationVanishes
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingIdeal
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple

/-! # The equations vanish on the seed section

Since the image of `f` lies in `X ⊂ ℙ^N`, each `F_j` vanishes at the homogeneous coordinate sections
`(f_0, …, f_N)`, so `s` lands in `𝒵` (Definition 2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem seedSection_equations_vanish {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord) (j : E.ι) :
    evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0 := by
  rcases hcoord with ⟨hcoord, hproj⟩
  apply evalHomogeneousAtSections_eq_zero_of_projectivization_factors e f
    (seedLineBundle e f) coord hcoord hproj (E.F j) (E.homogeneous j)
  rw [← E.spans]
  exact Ideal.subset_span ⟨j, rfl⟩

end
