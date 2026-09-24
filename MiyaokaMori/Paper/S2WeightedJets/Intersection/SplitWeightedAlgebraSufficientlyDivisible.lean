import MiyaokaMori.RingTheory.MonomialSplitIntoWeightMOfDvd
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraAtlas
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.WeightedPolynomialAtlasVeroneseGenerationOfSplit

/-! # Sufficient divisibility for the split weighted algebra

The split weighted algebra `splitWeightedAlgebraOf F jetOrder` has weights `1, ..., jetOrder`. If `m > 0` and every
weight divides `m`, then its `m`-th Veronese subalgebra is generated in degree one, so `m` is sufficiently divisible
for this graded algebra (Lemma 2.2 of the paper, applied to `Y^sp`).
Proof, in three steps:
1. `splitWeightedAlgebraOf F jetOrder` has a weighted polynomial atlas with weights `(i, q) ↦ q + 1` (variables
   `ULift (Fin r × Fin jetOrder)`), `SplitWeightedAlgebraAtlas`.
2. A monomial exponent of weight `l·m` decomposes into a sum of `l` exponents of weight `m` (pure combinatorics; the
   paper treats the case `m = s_k·lcm`).
3. A graded algebra sheaf with an atlas satisfying the decomposition property of step 2 has its `m`-th Veronese
   generated in degree one.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem splitWeightedAlgebra_sufficientlyDivisible_of_dvd {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 jetOrder, q ∣ m) :
    (splitWeightedAlgebraOf F jetOrder).SufficientlyDivisible m := by
  refine ⟨hm, ?_⟩
  obtain ⟨atlas⟩ := splitWeightedAlgebraOf_isLocallyWeightedPolynomial F jetOrder
  refine AlgebraicGeometry.Scheme.GradedQCAlgebra.veronese_generatedInDegreeOne_of_atlas_of_split
    (splitWeightedAlgebraOf F jetOrder)
    (fun iq : ULift.{u} (Fin r × Fin jetOrder) => ((iq.down.2 : ℕ) + 1)) m ?_ atlas
  intro e l hl he
  exact exists_split_of_weight_eq_mul_of_dvd (k := jetOrder) _
    (fun iq => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, Nat.succ_le_of_lt iq.down.2.isLt⟩)
    m hm hdiv e l hl he

end
