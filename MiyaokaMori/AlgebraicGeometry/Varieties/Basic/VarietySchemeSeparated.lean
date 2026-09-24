import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # The underlying scheme of a variety is separated

The underlying scheme of a variety `X` over `k` is separated (i.e. `X → Spec ℤ` is separated):
`X → Spec k` is separated by definition, `Spec k → Spec ℤ` is a morphism of affine schemes and
hence separated, and separated morphisms compose. Registered as an instance so that
constructions requiring `[Y.IsSeparated]` (such as `RationalMap.toPartialMap`) apply directly to
varieties.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance Variety.isSeparated_toScheme {k : Type u} [Field k] (X : Variety k) :
    X.toScheme.IsSeparated :=
  ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance⟩

end
