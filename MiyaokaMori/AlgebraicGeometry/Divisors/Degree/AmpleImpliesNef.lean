import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleInterEqIntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RestrictionDegreePositiveOfAmple

/-! # Ample line bundles are nef

An ample line bundle is nef: for every integral curve `Γ ⊂ X`, `L · [Γ] = deg(L|_Γ)`
(`LineBundle.inter_fundamentalClass_eq_degree`), and the restriction of an ample line bundle to an
integral curve has positive degree (`degree_restrict_pos_of_ample`), so `L · [Γ] > 0 ≥ 0`.
Used in the proof of Lemma 5.1 of the paper (`A_S = Φ^*O_X(1)` is nef);
see also the remark after Lazarsfeld, Definition 1.4.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An ample line bundle on a smooth projective variety is nef. -/
theorem IsAmple.isNef {k : Type u} [Field k] [IsAlgClosed k] {X : SmoothProjectiveVariety k}
    {L : LineBundle X.toVariety} (hL : AlgebraicGeometry.IsAmple L.toModules) : IsNef L := by
  intro Γ
  rw [LineBundle.inter_fundamentalClass_eq_degree L Γ]
  exact (degree_restrict_pos_of_ample hL Γ).le

end
