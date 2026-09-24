import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # The sheaf of differentials as a vector bundle

For `X` smooth of dimension `n` over `k`, `Ω_{X/k}` is locally free of rank `n` and hence gives a
vector bundle `Ω_X` of rank `n` (the dictionary between locally free sheaves and vector bundles),
as in §1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def cotangentBundle {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    AlgebraicGeometry.VectorBundle X.toVariety where
  toModules := AlgebraicGeometry.Omega (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  rank := X.toVariety.dim
  locallyFree := (IsSmoothOver.isLocallyFree_omega X.toVariety X.smooth).1
  isFiniteType := AlgebraicGeometry.Omega_isFiniteType _
  rankAtStalk_eq := (IsSmoothOver.isLocallyFree_omega X.toVariety X.smooth).2

theorem cotangentBundle_rank {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    (cotangentBundle X).rank = X.toVariety.dim :=
  rfl

theorem cotangentBundle_sheaf {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Nonempty ((cotangentBundle X).toModules ≅
      AlgebraicGeometry.Omega (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :=
  ⟨CategoryTheory.Iso.refl _⟩

end
