import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankBridge
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle

/-! # A vector bundle is locally free of its rank

A `VectorBundle` `E` on a curve `C` (`IsLocallyFree` + `IsFiniteType` + rank `E.rank` at every
stalk) satisfies `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank ⟨C, C ↘ Spec k⟩ E.toModules E.rank`. Shared by
`VectorBundle.degree_spec` and `LineBundle.degree_spec`. The proof is the general bridge
`AlgebraicGeometry.Scheme.Modules.isLocallyFreeRank_of_rankAtStalk_eq` (`LocallyFreeRankBridge`).
-/

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

/-- A vector bundle `E` on a curve is locally free of rank `E.rank` in the sense of
`AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank`. -/
theorem AlgebraicGeometry.VectorBundle.isLocallyFreeRank {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (E : AlgebraicGeometry.VectorBundle C.toVariety) :
    AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank
      (⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      E.toModules E.rank :=
  letI : E.toModules.IsLocallyFree := E.locallyFree
  letI : E.toModules.IsFiniteType := E.isFiniteType
  AlgebraicGeometry.Scheme.Modules.isLocallyFreeRank_of_rankAtStalk_eq (fun x => E.rankAtStalk_eq x)

end
