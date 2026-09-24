import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual

/-! # The dual of a vector bundle

The dual `E^∨` of a vector bundle: the underlying sheaf is `Hom(E, O_X)`, and the rank is unchanged
(used for `T_X = Ω_X^∨` in §1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.VectorBundle.dual {k : Type u} [Field k] {X : Variety k}
    (E : AlgebraicGeometry.VectorBundle X) : AlgebraicGeometry.VectorBundle X :=
  haveI := E.isFiniteType
  { toModules := AlgebraicGeometry.Scheme.Modules.dual E.toModules
    rank := E.rank
    locallyFree :=
      (AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual E.toModules E.rank
        E.locallyFree E.rankAtStalk_eq).1
    isFiniteType :=
      AlgebraicGeometry.Scheme.Modules.isFiniteType_dual E.toModules E.locallyFree
    rankAtStalk_eq := fun x =>
      (AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual E.toModules E.rank
        E.locallyFree E.rankAtStalk_eq).2 x }

end
