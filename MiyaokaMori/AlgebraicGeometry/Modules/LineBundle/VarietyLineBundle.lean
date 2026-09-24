import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf

/-! # Line bundles on a variety

Line bundles / invertible sheaves: vector bundles of rank 1; `LineBundle.toVectorBundle` is the forgetful
projection to vector bundles (e.g. `A = f^*O_X(1)`, `d_L = deg L`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

structure LineBundle {k : Type u} [Field k] (X : Variety k) extends AlgebraicGeometry.VectorBundle X where
  rank_eq_one : toVectorBundle.rank = 1

/-- Morphisms of line bundles = morphisms of the underlying modules; `L ≅ M` and the isomorphism classes
of `Pic` use this. -/

instance {k : Type u} [Field k] (X : Variety k) : CategoryTheory.Category.{u} (LineBundle X) :=
  inferInstanceAs (CategoryTheory.Category.{u}
    (CategoryTheory.InducedCategory X.carrier.Modules (fun L : LineBundle X => L.toModules)))

end
