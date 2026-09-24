import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.FiltrationLineQuotients
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle

/-! # The split weighted projectivization

`Y^sp`, the weighted projectivization of one copy of `⊕_i Q_i` in each of the weights `1, …, k`, with
`π_sp : Y^sp → C` (Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable abbrev splitWeightedProjectivization {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder : ℕ) : CategoryTheory.Over C.toScheme :=
  AlgebraicGeometry.Scheme.relativeProj (splitWeightedAlgebraOf F jetOrder)

end
