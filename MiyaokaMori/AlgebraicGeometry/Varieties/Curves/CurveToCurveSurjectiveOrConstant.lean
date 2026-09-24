import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperImageClosed
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField

/-! # A morphism from a proper curve to a smooth projective curve is constant or surjective

A `K`-morphism from an integral scheme `Γ` proper over `K` to a smooth projective curve `C` either
has a single closed point as image or is surjective: the image is closed and irreducible, and `C`
is one-dimensional.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem range_closedPoint_or_surjective {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    (Γ : AlgebraicGeometry.Scheme.{u}) [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Γ] (hΓ : IsProperOver K Γ)
    (g : Γ ⟶ C.toScheme) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))] :
    (∃ c : C.toScheme, IsClosed ({c} : Set C.toScheme) ∧ Set.range g.base ⊆ {c})
      ∨ Function.Surjective g.base := by
  letI : AlgebraicGeometry.UniversallyClosed
      (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    hΓ.toUniversallyClosed
  letI : AlgebraicGeometry.IsSeparated
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := C.isSeparated
  have hclosed : IsClosed (Set.range g.base) := by
    simpa [AlgebraicGeometry.Scheme.Hom.setImage] using
      (AlgebraicGeometry.Scheme.Hom.isClosed_setImage g
        (inferInstance : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))))
  let η : Γ := genericPoint Γ
  let z : C.toScheme := g.base η
  have hzgen : IsGenericPoint z (closure (Set.range g.base)) := by
    simpa [z, η, Set.image_univ] using
      (genericPoint_spec Γ).image g.continuous
  have hzgen' : IsGenericPoint z (Set.range g.base) := by
    simpa [hclosed.closure_eq] using hzgen
  by_cases hz : z = genericPoint C.toScheme
  · right
    intro y
    have hmem : genericPoint C.toScheme ∈ Set.range g.base := by
      rw [← hz]
      exact hzgen'.mem
    have hyall : y ∈ Set.range g.base :=
      (genericPoint_spec C.toScheme).mem_closed_set_iff hclosed |>.mp hmem (by trivial)
    exact hyall
  · left
    letI : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
    have hdim : topologicalKrullDim C.toScheme ≤ 1 := by
      rw [C.dim_one]
    have hkrull : Order.krullDim C.toScheme ≤ 1 := by
      rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C.toScheme))]
      exact hdim
    have hco : Order.coheight z ≤ 1 :=
      WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim z).trans hkrull)
    have hco0 : Order.coheight z ≠ 0 := by
      intro hzero
      have hmax : IsMax z := Order.coheight_eq_zero.mp hzero
      have hzg : genericPoint C.toScheme ≤ z := by
        exact hmax (AlgebraicGeometry.Scheme.le_iff_specializes.mpr
          (genericPoint_specializes z))
      have hgz : z ≤ genericPoint C.toScheme :=
        AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes z)
      exact hz (Inseparable.eq ((genericPoint_specializes z).antisymm
        (AlgebraicGeometry.Scheme.le_iff_specializes.mp hzg)).symm)
    have hco1 : Order.coheight z = 1 := by
      apply le_antisymm hco
      exact Order.one_le_iff_ne_zero.mpr hco0
    have hzclosed : IsClosed ({z} : Set C.toScheme) :=
      AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one hdim z hco1
    refine ⟨z, hzclosed, ?_⟩
    exact hzgen'.mem_closed_set_iff hzclosed |>.mp (by simp)

end
