import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Bundling an unbundled line bundle

Bundling a line bundle in unbundled form (`M : X.Modules` with `[M.IsLineBundle]`) into a `LineBundle X`;
inverse to `LineBundle.toModules` (the underlying module is unchanged).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Bundling: here a line bundle is "a module + locally free of rank 1" (`IsLocallyFreeRank M 1`); `M` is packed
   together with the local freeness and finite type provided by `IsLineBundle`, with rank 1. -/

noncomputable def LineBundle.ofModules {k : Type u} [Field k] {X : Variety k}
    (M : X.toScheme.Modules) [M.IsLineBundle] : LineBundle X :=
  { toModules := M
    rank := 1
    locallyFree := inferInstance
    isFiniteType := inferInstance
    -- locally isomorphic to O_X, so the rank at every stalk is 1
    rankAtStalk_eq := AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle M
    rank_eq_one := rfl }

theorem LineBundle.ofModules_toModules {k : Type u} [Field k] {X : Variety k}
    (M : X.toScheme.Modules) [M.IsLineBundle] : (LineBundle.ofModules M).toModules = M :=
  rfl

end
