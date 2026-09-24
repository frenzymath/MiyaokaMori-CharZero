import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraAtlas
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveSpaceIsIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationFiber
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjSpaceDimension

/-! # The fibers of the split weighted projectivization

The fiber of `Y^sp` at a closed point is integral of dimension `s − 1` (Lemma 2.3 and
Proposition 2.4 of the paper; `Y_c ≅ P(w)`), one of the inputs of `pushforward_taut_pow_eq_fiberDegree`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The fiber of `Y^sp` at a closed point is integral of dimension `s − 1`**: the scheme-theoretic fiber of
`π_sp : Y^sp = Proj_C(Sym^w(⊕Q_i)) → C` at any point `c` is an integral scheme of dimension `(n+1)·kk − 1`
(Lemma 2.3 of the paper: `Y_c ≅ P(w)`, `dim = s − 1`).

Proof.
1. Locally weighted polynomial structure: `splitWeightedAlgebraOf F kk = weightedSymAlgebra (fun _ : Fin kk => ⊕_i Q_i)`;
   `⊕_i Q_i` is locally free of finite type of rank `n + 1` at every point, so
   `weightedSymAlgebra_isLocallyWeightedPolynomial` gives `(splitWeightedAlgebraOf F kk).IsLocallyWeightedPolynomial w hw`
   with `σ := ULift (Fin (n+1) × Fin kk)`, `w (i,q) := q + 1` (`splitWeightedAlgebraOf_isLocallyWeightedPolynomial`).
2. `relativeProj_fiber_weightedProjectiveSpace`: there is `e : π_sp.fiber c ≅ weightedProjectiveSpace κ(c) w hw`
   compatible with the structure morphisms to `Spec κ(c)`.
3. Integrality: `weightedProjectiveSpace.isIntegral κ(c) w hw` (`σ` is nonempty since `kk ≥ 1`, `n + 1 ≥ 1`), and
   integrality transports along isomorphisms (`isIntegral_of_isOpenImmersion e.hom`; the fiber is `Nonempty` via
   `e.inv.base (Classical.arbitrary _)`).
4. Dimension: `weightedProjectiveSpace_dimension κ(c) w hw : topologicalKrullDim P = card σ − 1` with
   `card σ = (n+1)·kk` (`Fintype.card_ulift`, `Fintype.card_prod`, `Fintype.card_fin`); homeomorphisms preserve the
   Krull dimension (`IsHomeomorph.topologicalKrullDim_eq`, the homeomorphism of `e` via `Scheme.homeoOfIso`), and the
   definition of `Scheme.dimension` (`WithBot.unbotD 0 · |>.toNat`) gives `.dimension = (n+1)·kk − 1`. -/
theorem splitWeightedProjectivization_fiber_isIntegral_and_dimension {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {n kk : ℕ} (hkk : 1 ≤ kk)
    {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (c : C.carrier) :
    AlgebraicGeometry.IsIntegral ((splitWeightedProjectivization F kk).hom.fiber c) ∧
      ((splitWeightedProjectivization F kk).hom.fiber c).dimension = (n + 1) * kk - 1 := by
  let σ := ULift.{u} (Fin (n + 1) × Fin kk)
  let w : σ → ℕ := fun iq => (iq.down.2 : ℕ) + 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.succ_pos _
  have hS : (splitWeightedAlgebraOf F kk).IsLocallyWeightedPolynomial w hw :=
    splitWeightedAlgebraOf_isLocallyWeightedPolynomial F kk
  obtain ⟨e, -, -⟩ :=
    relativeProj_fiber_weightedProjectiveSpace (splitWeightedAlgebraOf F kk) w hw hS c
  have : Nonempty σ := ⟨⟨(0, ⟨0, hkk⟩)⟩⟩
  have := weightedProjectiveSpace.isIntegral (C.toScheme.residueField c) w hw
  have : Nonempty ((splitWeightedProjectivization F kk).hom.fiber c) :=
    ⟨e.inv.base (Classical.arbitrary _)⟩
  refine ⟨AlgebraicGeometry.isIntegral_of_isOpenImmersion e.hom, ?_⟩
  have hcard : Fintype.card σ = (n + 1) * kk := by
    simp [σ, Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin]
  unfold AlgebraicGeometry.Scheme.dimension
  rw [IsHomeomorph.topologicalKrullDim_eq _ (AlgebraicGeometry.Scheme.homeoOfIso e).isHomeomorph,
    weightedProjectiveSpace_dimension _ w hw, hcard]
  exact ENat.toNat_natCast _

end
