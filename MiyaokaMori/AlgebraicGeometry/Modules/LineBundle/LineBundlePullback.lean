import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # Pullback of line bundles

The pullback `g^*L` of a line bundle along a morphism (the underlying vector bundle is
`VectorBundle.pullback`, still of rank 1); notation `g ^* L`. Pullback of modules: Stacks 01BG.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def LineBundle.pullback {k : Type u} [Field k] {X Y : Variety k}
    (g : X.toScheme ⟶ Y.toScheme) (L : LineBundle Y) : LineBundle X where
  toVectorBundle := AlgebraicGeometry.VectorBundle.pullback g L.toVectorBundle
  rank_eq_one := L.rank_eq_one

@[inherit_doc] infixr:80 " ^* " => LineBundle.pullback

end
