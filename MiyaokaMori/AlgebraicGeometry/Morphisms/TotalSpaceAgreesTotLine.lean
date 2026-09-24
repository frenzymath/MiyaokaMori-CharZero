import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.Paper.S2WeightedJets.Cone.TotLineAffineOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

/-! # The total space of a line bundle inside the ruled surface

`Tot(L) = totalSpace L = Spec_X Sym(L^∨)` as an open subscheme of the ruled surface `W = P(O ⊕ L)`:
the open immersion `ruledSurface.totalSpaceIncl L := totalSpace.toProjBundle L`,
compatible with the projections (`totalSpaceIncl_comp_π`). This is the description of `Tot(L)` as the
complement of the `L`-section in `P(O ⊕ L)` in §2.1 of the paper; the complement statement is the
theorem `totalSpace.range_toProjBundle_eq` / `ruledSurface.range_totalSpaceIncl`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The open immersion `Tot(L) ↪ W = P(O ⊕ L)` (`W` is by definition `P(O ⊕ L)`, so this is `totalSpace.toProjBundle`). -/
noncomputable def ruledSurface.totalSpaceIncl {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).left ⟶ (ruledSurface L).toScheme :=
  AlgebraicGeometry.Scheme.totalSpace.toProjBundle L.toModules

theorem ruledSurface.totalSpaceIncl_isOpenImmersion {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    AlgebraicGeometry.IsOpenImmersion (ruledSurface.totalSpaceIncl L) :=
  AlgebraicGeometry.Scheme.totalSpace.toProjBundle_isOpenImmersion L.toModules

theorem ruledSurface.totalSpaceIncl_comp_π {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    ruledSurface.totalSpaceIncl L ≫ ruledSurface.π L
      = (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom :=
  AlgebraicGeometry.Scheme.totalSpace.toProjBundle_comp_hom L.toModules

end
