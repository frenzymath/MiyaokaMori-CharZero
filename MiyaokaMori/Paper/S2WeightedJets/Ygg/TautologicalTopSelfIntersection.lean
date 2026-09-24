import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClassWellDefined
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor

/-! # The rational tautological top self-intersection

The rational top self-intersection `H^s := (O(m)^s) / m^s` of the tautological class of a
sufficiently divisible polarization `O(m)`; it does not depend on the choice of `m`
(Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The top self-intersection of the line bundle `L` (thought of as `O(m)`) divided by
`m ^ dim X`: the rational top self-intersection of `c₁(L) / m`. -/
noncomputable def tautologicalTopSelfIntersection {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (L : X.Modules) [L.IsLineBundle] (m : ℕ) (hm : 0 < m) : ℚ :=
  (AlgebraicGeometry.topSelfIntersection X hX L : ℚ) / (m : ℚ) ^ X.dimension

end
