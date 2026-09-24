import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankBridge
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.DifferentialsAsVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.VectorBundleDual
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # The tangent bundle

The tangent bundle `T_X := (Ω_{X/k})^∨` of a smooth projective variety `X`, as a vector bundle of
rank `dim X` (the `T_X` of §1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The tangent bundle is the dual `VectorBundle.dual` of the cotangent bundle `cotangentBundle X`
   (`DifferentialsAsVectorBundle`); its underlying sheaf of modules is therefore
   `Scheme.Modules.dual (Omega (X ↘ Spec k))`, and its rank is `X.toVariety.dim`. -/

/- The three `Prop` fields of the `VectorBundle` structure (locally free, finite type, rank at every
   stalk) are stated as separate named theorems so that they can be cited independently. -/

/-- `T_X` is locally free. -/
theorem tangentBundle_toModules_isLocallyFree {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) :
    (AlgebraicGeometry.Scheme.Modules.dual
      (AlgebraicGeometry.Omega
        (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).IsLocallyFree :=
  haveI : AlgebraicGeometry.Smooth
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := X.smooth
  haveI := AlgebraicGeometry.Omega_isFiniteType
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  haveI := AlgebraicGeometry.isLocallyFree_omega_of_smooth
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' _

/-- `T_X` is of finite type. -/
theorem tangentBundle_toModules_isFiniteType {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) :
    (AlgebraicGeometry.Scheme.Modules.dual
      (AlgebraicGeometry.Omega
        (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).IsFiniteType :=
  haveI : AlgebraicGeometry.Smooth
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := X.smooth
  haveI := AlgebraicGeometry.Omega_isFiniteType
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  AlgebraicGeometry.Scheme.Modules.isFiniteType_dual _
    (AlgebraicGeometry.isLocallyFree_omega_of_smooth
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))

/-- The rank of `T_X` at every stalk is `dim X` (from `rank Ω_{X/k} = dim X`, Stacks 02G1). -/
theorem tangentBundle_toModules_rankAtStalk_eq {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) (x : X.toVariety.carrier) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (AlgebraicGeometry.Scheme.Modules.dual
        (AlgebraicGeometry.Omega
          (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) x = X.toVariety.dim :=
  haveI := AlgebraicGeometry.Omega_isFiniteType
    (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  (AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual _ X.toVariety.dim
    (IsSmoothOver.isLocallyFree_omega X.toVariety X.smooth).1
    (IsSmoothOver.isLocallyFree_omega X.toVariety X.smooth).2).2 x

/-- The tangent bundle `T_X = (Ω_{X/k})^∨` of a smooth projective variety, as a vector bundle of
rank `dim X`. -/
noncomputable def tangentBundle {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    AlgebraicGeometry.VectorBundle X.toVariety where
  toModules := AlgebraicGeometry.Scheme.Modules.dual
    (AlgebraicGeometry.Omega (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  rank := X.toVariety.dim
  locallyFree := tangentBundle_toModules_isLocallyFree X
  isFiniteType := tangentBundle_toModules_isFiniteType X
  -- rank Ω_{X/k} = dim X (Stacks 02G1)
  rankAtStalk_eq := tangentBundle_toModules_rankAtStalk_eq X

/-- The rank of the tangent bundle is `dim X`. -/
theorem tangentBundle_rank {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    (tangentBundle X).rank = X.toVariety.dim :=
  rfl

theorem tangentBundle_toModules {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Nonempty ((tangentBundle X).toModules ≅
      AlgebraicGeometry.Scheme.Modules.dual
        (AlgebraicGeometry.Omega (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) :=
  ⟨CategoryTheory.Iso.refl _⟩

/-- The tangent bundle is the dual of the cotangent bundle (by definition). -/
theorem tangentBundle_eq_dual_cotangentBundle {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) :
    tangentBundle X = (cotangentBundle X).dual :=
  rfl

end
