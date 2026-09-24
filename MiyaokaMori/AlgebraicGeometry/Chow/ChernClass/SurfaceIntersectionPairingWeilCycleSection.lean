import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamental
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree

/-! # The Weil cycle of a Cartier divisor is the divisor of a rational section

The Weil cycle `[D]` (`CartierDivisor.weilCycle`) of a Cartier divisor `D` on a variety `X` is the
divisor `div_{O(D)}(s)` of some nonzero rational section `s` of the line bundle `O_X(D)` (the section
form of Hartshorne II.6.13); hence in the Chow group of the scheme, `[D] = c₁(O_X(D)) ∩ [X]`
(Stacks 02SJ / Fulton §2.5). Used for the symmetry `D·E = E·D` of the intersection pairing on a
surface, but valid for any variety.

Route:
1. `CartierDivisor.exists_lineCartierPresentation_coefficient_variety` (Hartshorne II.6.13) gives `s`
   in the stalk of `O_X(D)` at the generic point and a Cartier presentation `P` whose coefficient
   function equals `[D]` pointwise; `P.section_ne_zero` gives `s ≠ 0`.
2. `MiyaokaMori.RationalSectionDegree.coefficient_eq_rationalSectionOrd`: the coefficients of `P` equal
   `rationalSectionOrd O(D) s` pointwise, i.e. `div_{O(D)}(s) = [D]` as cycles.
3. `firstChernClass_fundamentalChowClass_eq_mk_rationalSectionDivisor` (Stacks 02SJ):
   `c₁(O(D)) ∩ [X] = [div_{O(D)}(s)]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Hartshorne II.6.13 (section form): `[D] = div_{O_X(D)}(s)` for some nonzero rational section `s` of
`O_X(D)`. -/
theorem CartierDivisor.exists_rationalSectionDivisor_eq_weilCycle {k : Type u} [Field k]
    (X : Variety k) (D : CartierDivisor X) :
    ∃ s : D.lineBundle.toModules.stalk (genericPoint X.toScheme), s ≠ 0 ∧
      D.lineBundle.toModules.rationalSectionDivisor s =
        (CartierDivisor.weilCycle X D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) := by
  obtain ⟨s, P, hP⟩ := CartierDivisor.exists_lineCartierPresentation_coefficient_variety X D
  -- the type of `s` is spelled `presheaf.stalk`, while `rationalSectionDivisor` wants `Modules.stalk`
  -- (definitionally equal); switch to the latter spelling first, otherwise `rw`/`exact` time out
  -- unfolding between the two spellings
  let s' : D.lineBundle.toModules.stalk (genericPoint X.toScheme) := s
  have hP' : ∀ x, P.cartier.coefficient x = D.lineBundle.toModules.rationalSectionOrd s' x :=
    fun x => MiyaokaMori.RationalSectionDegree.coefficient_eq_rationalSectionOrd
      ⟨X.toScheme, X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩
      D.lineBundle.toModules s' P x
  refine ⟨s', P.section_ne_zero, ?_⟩
  ext x
  rw [AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_apply, ← hP' x, hP x]

/-- The divisor form of Stacks 02SJ: if `X` is a variety of dimension `d+1`, then `[D] ∈ Z_d(X)` and in
the Chow group `A_d(X.toScheme)` one has `[D] = c₁(O_X(D)) ∩ [X]`. -/
theorem CartierDivisor.chowMk_weilCycle_eq_firstChernClass_cap_fundamentalChowClass {k : Type u} [Field k]
    (X : Variety k) (D : CartierDivisor X) (d : ℕ) (hX : X.toScheme.dimension = d + 1)
    (h : (CartierDivisor.weilCycle X D : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) ∈
      AlgebraicGeometry.cycleSubgroup X.toScheme d) :
    AlgebraicGeometry.ChowGroup.mk ⟨(CartierDivisor.weilCycle X D :
        AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ), h⟩ =
      AlgebraicGeometry.firstChernClass D.lineBundle.toModules (d + 1)
        (X.toScheme.fundamentalChowClass (d + 1)) := by
  obtain ⟨s, hs, hcyc⟩ := CartierDivisor.exists_rationalSectionDivisor_eq_weilCycle X D
  obtain ⟨h', heq⟩ :=
    AlgebraicGeometry.firstChernClass_fundamentalChowClass_eq_mk_rationalSectionDivisor (k := k)
      D.lineBundle.toModules d hX s hs
  rw [heq]
  congr 1
  exact Subtype.ext hcyc.symm

end
