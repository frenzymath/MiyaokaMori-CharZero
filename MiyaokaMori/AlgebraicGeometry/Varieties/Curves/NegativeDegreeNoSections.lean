import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierOfSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierWeilNonneg
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonzeroSectionRegular
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree

/-! # Line bundles of negative degree have no nonzero global sections

On a smooth projective curve, a line bundle of negative degree has no nonzero global section.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem no_global_sections_of_degree_neg {k : Type u} [Field k]
    (Ct : SmoothProjectiveCurve k) (L : LineBundle Ct.toVariety) (hL : L.degree < 0) :
    Subsingleton (AlgebraicGeometry.sheafCohomology Ct.toScheme L.toModules 0) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hH0
  let _ := hH0
  obtain ⟨s, hs⟩ :=
    AlgebraicGeometry.exists_section_ne_zero_of_nontrivial_sheafCohomology_zero L.toModules
  have hs_regular := isRegular_germ_of_ne_zero L.toModules s hs
  obtain ⟨D, _, ⟨eD⟩⟩ :=
    AlgebraicGeometry.exists_effectiveCartierDivisor_of_regular_section L.toModules s hs_regular
  obtain ⟨D', hD', ⟨eD'⟩⟩ := EffectiveCartierDivisor.exists_cartierDivisor_nonneg Ct D
  have hD_nonneg : 0 ≤ CartierDivisor.degree Ct D' := by
    unfold CartierDivisor.degree AlgebraicGeometry.AlgebraicCycle.degree
    exact finsum_nonneg fun x ↦ mul_nonneg (hD' x) (Int.natCast_nonneg _)
  let DL : CartierDivisor Ct.toVariety :=
    Classical.epsilon fun E : CartierDivisor Ct.toVariety ↦ Nonempty (E.lineBundle ≅ L)
  have hDL : Nonempty (DL.lineBundle ≅ L) := by
    exact Classical.epsilon_spec
      (p := fun E : CartierDivisor Ct.toVariety ↦ Nonempty (E.lineBundle ≅ L))
      (LineBundle.exists_cartierDivisor Ct L)
  let eD'LModules : D'.lineBundle.toModules ≅ L.toModules := eD' ≪≫ eD
  let eD'L : D'.lineBundle ≅ L :=
    { hom := CategoryTheory.InducedCategory.homMk eD'LModules.hom
      inv := CategoryTheory.InducedCategory.homMk eD'LModules.inv
      hom_inv_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        exact eD'LModules.hom_inv_id
      inv_hom_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        exact eD'LModules.inv_hom_id }
  -- the degree of `L` equals the degree of the Cartier divisor `D'`
  have hdegree : L.degree = CartierDivisor.degree Ct D' :=
    LineBundle.degree_eq_cartierDivisor_degree Ct eD'LModules
  omega

end
