import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # The relative Proj is separated over the base

The structure morphism `Proj_X S → X` of a relative Proj is separated: locally it is
`Proj S(U) → Spec O(U)`, which is separated, and separatedness is local on the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The structure morphism `Proj A(U) ⟶ U` of a chart is separated: it is the composite of
`Proj.toSpecZero` (Mathlib instance `Proj.isSeparated`), a `Spec.map` (an affine morphism) and
`isoSpec.inv` (an isomorphism). -/
instance AlgebraicGeometry.Scheme.GradedAffineAlgebra.projToOpen_isSeparated
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedAffineAlgebra)
    (U : X.AffineZariskiSite) :
    AlgebraicGeometry.IsSeparated (S.projToOpen U) := by
  unfold AlgebraicGeometry.Scheme.GradedAffineAlgebra.projToOpen
  infer_instance

instance AlgebraicGeometry.Scheme.relativeProj_isSeparated {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) :
    AlgebraicGeometry.IsSeparated (AlgebraicGeometry.Scheme.relativeProj S).hom := by
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @AlgebraicGeometry.IsSeparated) (fun U : X.affineOpens => U.1)
    (AlgebraicGeometry.iSup_affineOpens_eq_top X)]
  intro U
  -- `π ∣_ U` and the chart's structure morphism `Proj A(U) ⟶ U` are two pullbacks of the same
  -- cospan `(U.ι, π)`, hence differ by an isomorphism
  have h1 := AlgebraicGeometry.isPullback_morphismRestrict
    (AlgebraicGeometry.Scheme.relativeProj S).hom U.1
  have h2 := S.toGradedAffineAlgebra.projChart_isPullback ⟨U.1, U.2⟩
  have h2' : IsPullback (S.toGradedAffineAlgebra.projToOpen ⟨U.1, U.2⟩)
      (S.toGradedAffineAlgebra.projChart ⟨U.1, U.2⟩) U.1.ι
      (AlgebraicGeometry.Scheme.relativeProj S).hom := by
    -- `Scheme.relativeProj` is an `abbrev` of `GradedAffineAlgebra.relativeProj`, so the two
    -- spellings are reducibly defeq.
    exact h2
  rw [← CategoryTheory.IsPullback.isoIsPullback_hom_fst _ _ h1 h2']
  infer_instance

end
