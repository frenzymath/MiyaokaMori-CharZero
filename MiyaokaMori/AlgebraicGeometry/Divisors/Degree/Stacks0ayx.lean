import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleHom
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.PicardGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Additivity of the degree under tensor products (Stacks 0AYX)

On a smooth projective curve, `deg(L ⊗ M) = deg L + deg M` (the rank-one case of Stacks 0AYX).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem divisor_degree_add {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (D E : CartierDivisor C.toVariety) :
    CartierDivisor.degree C (D + E) =
      CartierDivisor.degree C D + CartierDivisor.degree C E := by
  let : AlgebraicGeometry.IsProper
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    exact IsProjectiveOver.isProper C.projective
  -- the degree is `AlgebraicCycle.degree` of the Weil cycle, so additivity is `degree_add`
  rw [CartierDivisor.degree_weilCycle, CartierDivisor.degree_weilCycle,
    CartierDivisor.degree_weilCycle, CartierDivisor.weilCycle_add]
  exact AlgebraicGeometry.AlgebraicCycle.degree_add _ _

/-- If `T ≅ L ⊗ M` then `deg T = deg L + deg M`. -/
theorem LineBundle.degree_eq_add_of_iso_tensor {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M T : LineBundle C.toVariety)
    (e : T.toModules ≅ AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules) :
    T.degree = L.degree + M.degree := by
  let DL : CartierDivisor C.toVariety :=
    Classical.epsilon fun D : CartierDivisor C.toVariety ↦ Nonempty (D.lineBundle ≅ L)
  let DM : CartierDivisor C.toVariety :=
    Classical.epsilon fun D : CartierDivisor C.toVariety ↦ Nonempty (D.lineBundle ≅ M)
  let DT : CartierDivisor C.toVariety :=
    Classical.epsilon fun D : CartierDivisor C.toVariety ↦ Nonempty (D.lineBundle ≅ T)
  have hDL : Nonempty (DL.lineBundle ≅ L) :=
    Classical.epsilon_spec (LineBundle.exists_cartierDivisor C L)
  have hDM : Nonempty (DM.lineBundle ≅ M) :=
    Classical.epsilon_spec (LineBundle.exists_cartierDivisor C M)
  have hDT : Nonempty (DT.lineBundle ≅ T) :=
    Classical.epsilon_spec (LineBundle.exists_cartierDivisor C T)
  obtain ⟨eDL⟩ := hDL
  obtain ⟨eDM⟩ := hDM
  obtain ⟨eDT⟩ := hDT
  obtain ⟨eadd⟩ := CartierDivisor.lineBundle_add DL DM
  let esumMod : (DL + DM).lineBundle.toModules ≅ T.toModules :=
    eadd ≪≫ AlgebraicGeometry.Scheme.Modules.tensorIsoCongr
      (LineBundle.toModulesIso eDL) (LineBundle.toModulesIso eDM) ≪≫ e.symm
  let esum : (DL + DM).lineBundle ≅ T := LineBundle.isoOfModules esumMod
  rw [LineBundle.degree_eq_cartierDivisor_degree C (LineBundle.toModulesIso eDT),
    LineBundle.degree_eq_cartierDivisor_degree C (LineBundle.toModulesIso eDL),
    LineBundle.degree_eq_cartierDivisor_degree C (LineBundle.toModulesIso eDM)]
  calc
    CartierDivisor.degree C DT = CartierDivisor.degree C (DL + DM) :=
      CartierDivisor.degree_eq_of_lineBundle_iso C (eDT ≪≫ esum.symm)
    _ = CartierDivisor.degree C DL + CartierDivisor.degree C DM :=
      divisor_degree_add C DL DM

end
