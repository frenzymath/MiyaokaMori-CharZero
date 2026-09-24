import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankConstantConnected
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Vector bundles

A vector bundle of rank `r` on a variety `X`: a locally free `O_X`-module of finite type whose fibre
dimension at every point is `r`, packaged as a structure with the rank as a field (the bundles `T_X`
and `E = s^*T_{Z/C}` of rank `n+1` in §§1–2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A vector bundle on a variety `X`: a locally free `O_X`-module of finite type with constant rank
`rank` at every stalk. -/
structure AlgebraicGeometry.VectorBundle {k : Type u} [Field k] (X : Variety k) where
  toModules : X.carrier.Modules
  rank : ℕ
  locallyFree : toModules.IsLocallyFree
  isFiniteType : toModules.IsFiniteType
  rankAtStalk_eq : ∀ x : X.carrier,
    AlgebraicGeometry.Scheme.Modules.rankAtStalk toModules x = rank

/- The two property fields are registered as instances, so that `IsLocallyFree` / `IsFiniteType` on
   `E.toModules` are found by instance search (`weightedSymAlgebra`, `weightedProjBundle`,
   `isLocallyFree_dual`, etc. take them as instance arguments). -/

attribute [instance] AlgebraicGeometry.VectorBundle.locallyFree AlgebraicGeometry.VectorBundle.isFiniteType

end
