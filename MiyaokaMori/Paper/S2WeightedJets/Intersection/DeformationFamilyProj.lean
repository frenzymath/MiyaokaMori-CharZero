import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC

/-! # The deformation family as a relative Proj

`𝒴`, the relative Proj over `C × 𝔸¹` of the deformed graded algebra (Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def deformationFamily {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ) :
    CategoryTheory.Over (AlgebraicGeometry.Scheme.affineLineOver C.toScheme) :=
  AlgebraicGeometry.Scheme.relativeProj (deformedJetAlgebra Z sec hs r)

end
