import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerTopLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # The determinant line bundle

The determinant line bundle `det E = Λ^r E` of a vector bundle of rank `r` (used for `det T_X` in the
paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `det E = Λ^r E` (`r = E.rank`): the underlying sheaf of modules is
`Scheme.Modules.exteriorPower E.toModules E.rank`; local freeness, finite type and rank `C(r,r) = 1`,
needed to package it as a `LineBundle`, are `exteriorPower_top_isLocallyFree`. -/
noncomputable def AlgebraicGeometry.VectorBundle.det {k : Type u} [Field k] {X : Variety k}
    (E : AlgebraicGeometry.VectorBundle X) : LineBundle X :=
  have h := AlgebraicGeometry.Scheme.Modules.exteriorPower_top_isLocallyFree E.toModules E.rank
    E.locallyFree E.isFiniteType E.rankAtStalk_eq
  { toModules := AlgebraicGeometry.Scheme.Modules.exteriorPower E.toModules E.rank
    rank := 1
    locallyFree := h.1
    isFiniteType := h.2.1
    rankAtStalk_eq := h.2.2
    rank_eq_one := rfl }

end
