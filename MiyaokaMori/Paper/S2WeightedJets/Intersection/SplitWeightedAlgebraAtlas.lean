import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkBiproduct
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymLocallyWeightedPolynomial

/-! # A weighted polynomial atlas for the split weighted algebra

The split weighted algebra `splitWeightedAlgebraOf F jetOrder` (the weighted symmetric algebra of one copy of
`⊕_i Q_i` in each weight `1..jetOrder`) is locally a weighted polynomial algebra with weights `(i, q) ↦ q + 1` on
the variable set `ULift (Fin r × Fin jetOrder)` (`r` line quotients times `jetOrder` weights), i.e. it has a
weighted polynomial atlas (`IsLocallyWeightedPolynomial`); this is the local description of the coordinate
algebra of `Y^sp` in Lemma 2.3 of the paper.
Proof:
1. by definition `splitWeightedAlgebraOf F jetOrder = weightedSymAlgebra V` with `V q := ⊕_{i<r} Q_i` (one copy
   per weight);
2. `weightedSymAlgebra_isLocallyWeightedPolynomial`: if every `V q` is locally free of finite type of constant
   pointwise rank `ρ`, then `weightedSymAlgebra V` is locally a weighted polynomial algebra with weights
   `(i,q) ↦ q+1` on the variables `ULift (Fin ρ × Fin r')`; here `r' = jetOrder`, `ρ = r`;
3. rank: `rankAtStalk (⊕_i Q_i) x = Σ_i rankAtStalk Q_i x`, and for the line bundles `Q_i` each term is `1`
   (`rankAtStalk_eq`, `rank_eq_one`), giving `r`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The biproduct of line quotients `⊕_{i<r} Q_i` has pointwise rank `r`. -/
theorem splitWeightedAlgebra_lineQuotientBiproduct_rankAtStalk {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (x : C.toScheme) :
    haveI : ∀ i : Fin r, (F.lineQuotient i).toModules.IsLocallyFree :=
      fun i => (F.lineQuotient i).locallyFree
    haveI : ∀ i : Fin r, (F.lineQuotient i).toModules.IsFiniteType :=
      fun i => (F.lineQuotient i).isFiniteType
    AlgebraicGeometry.Scheme.Modules.rankAtStalk
      (CategoryTheory.Limits.biproduct (fun i : Fin r => (F.lineQuotient i).toModules)) x = r := by
  have : ∀ i : Fin r, (F.lineQuotient i).toModules.IsLocallyFree :=
    fun i => (F.lineQuotient i).locallyFree
  have : ∀ i : Fin r, (F.lineQuotient i).toModules.IsFiniteType :=
    fun i => (F.lineQuotient i).isFiniteType
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_biproduct]
  have h1 : ∀ i : Fin r,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk (F.lineQuotient i).toModules x = 1 := by
    intro i
    rw [(F.lineQuotient i).rankAtStalk_eq x]
    exact (F.lineQuotient i).rank_eq_one
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The split weighted algebra is locally a weighted polynomial algebra with weights `(i, q) ↦ q + 1` (atlas
form). -/
theorem splitWeightedAlgebraOf_isLocallyWeightedPolynomial {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder : ℕ) :
    (splitWeightedAlgebraOf F jetOrder).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin r × Fin jetOrder) => ((iq.down.2 : ℕ) + 1))
      (fun _ => Nat.succ_pos _) := by
  have h1 : ∀ i : Fin r, (F.lineQuotient i).toModules.IsLocallyFree :=
    fun i => (F.lineQuotient i).locallyFree
  have h2 : ∀ i : Fin r, (F.lineQuotient i).toModules.IsFiniteType :=
    fun i => (F.lineQuotient i).isFiniteType
  have hrank : ∀ (_ : Fin jetOrder) (x : C.toScheme),
      AlgebraicGeometry.Scheme.Modules.rankAtStalk
        (CategoryTheory.Limits.biproduct (fun i : Fin r => (F.lineQuotient i).toModules)) x = r :=
    fun _ x => splitWeightedAlgebra_lineQuotientBiproduct_rankAtStalk F x
  exact (AlgebraicGeometry.Scheme.weightedSymAlgebra_isLocallyWeightedPolynomial
    (fun _ : Fin jetOrder =>
      CategoryTheory.Limits.biproduct (fun i : Fin r => (F.lineQuotient i).toModules)) hrank).1

end
