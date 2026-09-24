import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DeterminantLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.DifferentialsAsVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # The canonical bundle

The canonical bundle `ω_X := ⋀^n Ω_{X/k} = det Ω_X` (`n = dim X`) of a smooth projective variety, a
line bundle. Its first Chern class gives the canonical class `K_X` of Theorem 1.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The canonical bundle `ω_X = det Ω_{X/k}` of a smooth projective variety. -/
noncomputable def canonicalBundle {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    LineBundle X.toVariety :=
  (cotangentBundle X).det

/-- The canonical bundle is the top exterior power `⋀^{dim X} Ω_{X/k}` of the cotangent bundle. -/
theorem canonicalBundle_eq_exteriorPower {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Nonempty ((canonicalBundle X).toModules ≅
      AlgebraicGeometry.Scheme.Modules.exteriorPower (cotangentBundle X).toModules X.toVariety.dim) := by
  dsimp [canonicalBundle, AlgebraicGeometry.VectorBundle.det]
  rw [cotangentBundle_rank]
  exact ⟨CategoryTheory.Iso.refl _⟩

end
