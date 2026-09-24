import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensorPow

/-! # `pieceIso` carries `framePow` to `sectionPow`

`truncatedJetAlgebra.framePow L U μ m = μ^{⊗m} ∈ Γ(U, (L^{-1})^{⊗m})` (`JetChartTrivialization_Basis`)
and `truncatedJetAlgebra.pieceIso L m : (L^{-1})^{⊗m} ≅ (L^∨)^{⊗m}` (`JetNeighborhoodToTotalSpace`) are both
right-recursive, and `pieceIso (m+1) = pieceIso m ⊗ zpowNegOneIso`; hence `pieceIso μ^{⊗m} = δ^{⊗m}` with
`δ := zpowNegOneIso μ` and `δ^{⊗m} = sectionPow (L^∨) U δ m`. Induction on `m` with `tensorHom_tensorSections`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace truncatedJetAlgebra

open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)
  (U : Ct.toScheme.Opens) (μ : Γ((L.zpow (-1)).toModules, U))

/-- `pieceIso L m (μ^{⊗m}) = (zpowNegOneIso μ)^{⊗m}`. -/
theorem pieceIso_hom_app_framePow : ∀ m : ℕ,
    Hom.app (pieceIso L m).hom U (framePow L U μ m) =
      sectionPow (dual L.toModules) U (Hom.app L.zpowNegOneIso.hom U μ) m
  | 0 => rfl
  | m + 1 => by
    show Hom.app (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Ct.toScheme.Modules)
        (pieceIso L m).hom L.zpowNegOneIso.hom) U
        (tensorSections (piece L m) (L.zpow (-1)).toModules U (framePow L U μ m) μ) =
      tensorSections (monoidalPow (dual L.toModules) m) (dual L.toModules) U
        (sectionPow (dual L.toModules) U (Hom.app L.zpowNegOneIso.hom U μ) m)
        (Hom.app L.zpowNegOneIso.hom U μ)
    refine (tensorHom_tensorSections (pieceIso L m).hom L.zpowNegOneIso.hom U (framePow L U μ m) μ).trans ?_
    exact congrArg (fun z => tensorSections (monoidalPow (dual L.toModules) m) (dual L.toModules) U z
      (Hom.app L.zpowNegOneIso.hom U μ)) (pieceIso_hom_app_framePow m)

end truncatedJetAlgebra

end
