import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyLocalDimensionEqDim
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.Stacks02g1

/-! # Smoothness over a field

A `k`-scheme is smooth over `k` if its structure morphism `X ↘ Spec k` is smooth.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `X` is smooth over `k`: the structure morphism `X ↘ Spec k` is smooth. -/
def IsSmoothOver (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : Prop :=
  AlgebraicGeometry.Smooth (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- On a smooth variety, `Ω_{X/k}` is locally free of rank `dim X` at every point; this is what
makes `T_X` a vector bundle of rank `n`. -/

theorem IsSmoothOver.isLocallyFree_omega {k : Type u} [Field k] (X : Variety k)
    (h : IsSmoothOver k X.carrier) :
    SheafOfModules.IsLocallyFree
        (AlgebraicGeometry.Omega (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ∧
      ∀ x : X.carrier, AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (AlgebraicGeometry.Omega (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) x = X.dim := by
  letI : AlgebraicGeometry.Smooth
      (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := h
  refine ⟨AlgebraicGeometry.isLocallyFree_omega_of_smooth _, ?_⟩
  intro x
  rw [AlgebraicGeometry.rankAtStalk_omega_eq_localDimension_of_smooth _ x]
  exact Variety.localDimension_eq_dim X x

end
