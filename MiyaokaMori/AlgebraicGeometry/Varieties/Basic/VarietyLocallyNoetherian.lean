import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Varieties are locally Noetherian

The underlying scheme of a variety over `k` is locally Noetherian (`Spec k` is Noetherian and the
structure morphism is of finite type), and so is the underlying scheme of a closed subvariety (a
closed immersion is locally of finite type). These instances provide the `IsLocallyNoetherian`
hypotheses needed by `Scheme.ord`, `principalCycle` and `rationalSectionDivisor`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance Variety.isLocallyNoetherian {k : Type u} [Field k] (X : Variety k) :
    AlgebraicGeometry.IsLocallyNoetherian X.toScheme :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

instance ClosedSubvariety.isLocallyNoetherian {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) : AlgebraicGeometry.IsLocallyNoetherian V.carrier :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian V.ι

end
