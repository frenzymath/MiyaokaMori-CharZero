import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Chow.NormalizedFirstChernClassIndep

/-! # The tautological class does not depend on `m`

The rational tautological class `H_k = c₁(O(m)) / m` of the weighted projectivization is
independent of the sufficiently divisible `m`: for two such `m, m'` one has
`c₁(O(m)) / m = c₁(O(m')) / m'` (Lemma 2.2 of the paper).

This is the special case, for the graded jet algebra, of
`AlgebraicGeometry.Scheme.relativeProj.normalizedFirstChernClass_indep`, which holds for any
graded quasi-coherent algebra `S`: `O(m)^{⊗m'} ≃ O(mm') ≃ O(m')^{⊗m}`, `c₁` is additive on
tensor powers, and one divides by `mm'` after tensoring with `ℚ`.
The instance hypotheses `[C.Over Spec k]`, `[LocallyOfFiniteType (C ↘ Spec k)]` and
`[LocallyOfFiniteType Z.hom]` are not used by the proof (the general lemma also holds when
`X` is not locally of finite type over a field: then both `firstChernClass` maps are zero);
they are kept in the statement so that downstream uses in the finite-type setting see the
genuine `c₁`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem tautologicalClass_indep {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom] [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (m m' : ℕ) (hm : ((jetGradedAlgebra (k := k) Z s hs r).1).SufficientlyDivisible m)
    (hm' : ((jetGradedAlgebra (k := k) Z s hs r).1).SufficientlyDivisible m') (d : ℕ) :
    haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z s hs r).1 m hm
    haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z s hs r).1 m' hm'
    (m : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z s hs r).1 (m : ℤ)) d).ratExtend =
      (m' : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z s hs r).1 (m' : ℤ)) d).ratExtend :=
  AlgebraicGeometry.Scheme.relativeProj.normalizedFirstChernClass_indep
    (jetGradedAlgebra (k := k) Z s hs r).1 m m' hm hm' d

end
