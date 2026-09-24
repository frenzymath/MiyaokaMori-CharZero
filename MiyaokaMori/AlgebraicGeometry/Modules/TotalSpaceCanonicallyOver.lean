import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

/-! # The total space is canonically a scheme over the base

The total space `Tot(V) = Spec Sym(V^∨)` of a vector bundle is canonically a scheme over `X` via the
projection `p : Tot(V) → X` (`CanonicallyOver`). Hence any `S`-structure on `X` (for instance
`X → Spec k` for a `k`-variety) gives, by composition `Tot(V) → X → S`, an `S`-structure on `Tot(V)` and
on its open subschemes, so that uses of `evalHomogeneousAtSections`, `projectivizationMorphism`,
`IsTupleProjectivization`, etc. requiring `[T.Over (Spec k)]` are found by instance search when
`T = Tot(L)` or an open subscheme of it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance AlgebraicGeometry.Scheme.totalSpace.canonicallyOver {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    (AlgebraicGeometry.Scheme.totalSpace V).left.CanonicallyOver X where
  hom := (AlgebraicGeometry.Scheme.totalSpace V).hom

end
