import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6

/-! # Pullback of vector bundles

The pullback `f^*E` of a vector bundle along a morphism (e.g. `f^*T_X` in §1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pullback `f^*E` of a vector bundle along `f`; the rank is unchanged. -/
noncomputable def AlgebraicGeometry.VectorBundle.pullback {k : Type*} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) (E : AlgebraicGeometry.VectorBundle Y) :
    AlgebraicGeometry.VectorBundle X :=
  haveI := E.locallyFree
  haveI := E.isFiniteType
  { toModules := (AlgebraicGeometry.Scheme.Modules.pullback f).obj E.toModules
    rank := E.rank
    locallyFree := (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback f E.toModules).1
    isFiniteType := AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback f E.toModules
    rankAtStalk_eq := fun x =>
      ((AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback f E.toModules).2 x).trans
        (E.rankAtStalk_eq (f.base x)) }

end
