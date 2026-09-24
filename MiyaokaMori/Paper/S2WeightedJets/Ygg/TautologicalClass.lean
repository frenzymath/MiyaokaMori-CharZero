import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClassWellDefined
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization

/-! # The tautological class

The rational tautological class `H_k = c₁(O_{Y_k^GG}(m)) / m ∈ A^1(Y_k^GG)_ℚ` of the weighted
projectivization; `O(m)` is a line bundle only for sufficiently divisible `m`
(Lemma 2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The tautological class `H_k = c₁(O(m)) / m`, as the operator
`A_d(Y_k^GG)_ℚ → A_{d-1}(Y_k^GG)_ℚ` for a sufficiently divisible `m`. -/
noncomputable def tautologicalClass {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (m : ℕ) (hm : ((jetGradedAlgebra (k := k) Z s hs r).1).SufficientlyDivisible m) (d : ℕ) :
    AlgebraicGeometry.ChowGroupRat (weightedJetProjectivization (k := k) Z s hs r).left d →ₗ[ℚ]
      AlgebraicGeometry.ChowGroupRat (weightedJetProjectivization (k := k) Z s hs r).left (d - 1) :=
  haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (jetGradedAlgebra (k := k) Z s hs r).1 m hm
  (m : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
    (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z s hs r).1 (m : ℤ)) d).ratExtend

end
