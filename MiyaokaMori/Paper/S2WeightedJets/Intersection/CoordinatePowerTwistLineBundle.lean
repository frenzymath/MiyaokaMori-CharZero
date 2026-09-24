import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible

/-! # The twist carrying the coordinate powers is a line bundle

If every weight `1, ..., kk` of the split weighted algebra `splitWeightedAlgebraOf F kk` divides the positive integer
`m`, then the twisting sheaf `O(m)` on the relative Proj is a line bundle (Lemma 2.2 of the
paper: `O(m)` is invertible for sufficiently divisible `m`).
Proof:
1. when every weight `1, ..., kk` divides `m`, `m` is sufficiently divisible for `splitWeightedAlgebraOf F kk`
   (`m > 0` and the `m`-th Veronese subalgebra is generated in degree one; `SplitWeightedAlgebraSufficientlyDivisible`);
2. for sufficiently divisible `m`, `O(m)` on the relative Proj is a line bundle.
(Equivalently, `O(m)` is trivialized on the coordinate opens `D_+(x_{i,q})` by `x_{i,q}^{m/q}`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem splitWeightedTwist_isLineBundle_of_dvd_lemma {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) :
    (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).IsLineBundle :=
  AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist (splitWeightedAlgebraOf F kk) m
    (splitWeightedAlgebra_sufficientlyDivisible_of_dvd F kk m hm hdiv)

end
