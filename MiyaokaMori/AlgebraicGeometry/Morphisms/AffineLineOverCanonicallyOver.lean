import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # The affine line over `X` is canonically a scheme over `X`

`A¹_X = AffineSpace (Fin 1) X` is canonically a scheme over `X` (`CanonicallyOver`) via the
projection `toBase`, compatibly with Mathlib's `CanonicallyOver` instance for `𝔸(n; S)`
(`affineLineOver` is a `def`, not an `abbrev`, so Mathlib's instance does not apply automatically).
Consequently `A¹_k` and its open subschemes are `k`-schemes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance AlgebraicGeometry.Scheme.affineLineOver.canonicallyOver (X : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.affineLineOver X).CanonicallyOver X where
  hom := AlgebraicGeometry.Scheme.affineLineOver.toBase X

end
