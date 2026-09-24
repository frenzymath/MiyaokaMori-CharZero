import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleHom
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.PicardGroup
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # The trivial line bundle has degree zero

`deg O_C = 0`: the trivial line bundle corresponds to the zero divisor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The trivial line bundle on a smooth projective curve has degree `0`. -/
theorem LineBundle.degree_one {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    LineBundle.degree (LineBundle.one C.toVariety) = 0 := by
  let D : CartierDivisor C.toVariety :=
    Classical.epsilon fun D : CartierDivisor C.toVariety =>
      Nonempty (CartierDivisor.lineBundle D ≅ LineBundle.one C.toVariety)
  have hD : Nonempty (D.lineBundle ≅ LineBundle.one C.toVariety) := by
    exact Classical.epsilon_spec (p := fun D : CartierDivisor C.toVariety =>
      Nonempty (CartierDivisor.lineBundle D ≅ LineBundle.one C.toVariety))
      (LineBundle.exists_cartierDivisor C (LineBundle.one C.toVariety))
  obtain ⟨eD⟩ := hD
  obtain ⟨e0⟩ := CartierDivisor.lineBundle_zero (X := C.toVariety)
  let e0' : (0 : CartierDivisor C.toVariety).lineBundle ≅
      LineBundle.one C.toVariety :=
    { hom := ⟨e0.hom⟩
      inv := ⟨e0.inv⟩
      hom_inv_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        change e0.hom ≫ e0.inv = 𝟙 _
        exact e0.hom_inv_id
      inv_hom_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        change e0.inv ≫ e0.hom = 𝟙 _
        simpa [LineBundle.one_toModules] using e0.inv_hom_id }
  have hweil :
      (CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety) :
        AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ) = 0 := by
    have h := CartierDivisor.weilCycle_add C.toVariety
      (0 : CartierDivisor C.toVariety) 0
    have h' :
        (CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety) :
          AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ) + 0 =
          CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety) +
            CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety) := by
      simpa using h
    exact (add_left_cancel h').symm
  have hdegree_zero : CartierDivisor.degree C (0 : CartierDivisor C.toVariety) = 0 := by
    have hdim_eq : C.toScheme.dimension = 1 := by
      unfold AlgebraicGeometry.Scheme.dimension
      rw [C.dim_one]
      simp
    have hdim : C.toScheme.dimension - 1 = 0 := by omega
    let α : AlgebraicGeometry.Intersection.DimensionCycle C.toScheme 0 :=
      ⟨(CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety) :
          AlgebraicGeometry.AlgebraicCycle C.toScheme ℤ), by
        rw [← hdim]
        exact (CartierDivisor.weilCycle C.toVariety (0 : CartierDivisor C.toVariety)).property⟩
    have hα : α = AlgebraicGeometry.Intersection.DimensionCycle.zero C.toScheme 0 := by
      apply Subtype.ext
      exact hweil
    letI : AlgebraicGeometry.IsProper
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      exact IsProjectiveOver.isProper C.projective
    unfold CartierDivisor.degree
    change AlgebraicGeometry.Intersection.rawZeroCycleDegree
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) α = 0
    rw [hα]
    exact AlgebraicGeometry.Intersection.rawZeroCycleDegree_zero _
  rw [LineBundle.degree_eq_cartierDivisor_degree C (D := D) (LineBundle.toModulesIso eD)]
  calc
    CartierDivisor.degree C D = CartierDivisor.degree C (0 : CartierDivisor C.toVariety) :=
      CartierDivisor.degree_eq_of_lineBundle_iso C (eD ≪≫ e0'.symm)
    _ = 0 := hdegree_zero

end
