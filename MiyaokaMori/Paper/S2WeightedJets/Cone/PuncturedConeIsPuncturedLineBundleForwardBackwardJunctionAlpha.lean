import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardInlineAuxProofs
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardSectionAPI

/-! # Junction α: `IsConeToTotalSpaceHom` restated in the section API

See `…JunctionBeta` for why this lives in its own module (here the conversion happens to be cheap, but the
body of `IsConeToTotalSpaceHom` carries `…_proof_k` auxiliary lemmas all the same).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `IsConeToTotalSpaceHom` in the section API: α ≫ π = g and, for every i, ⟨w_α, g^*q_i⟩ = z_i. -/
theorem IsConeToTotalSpaceHom.exists_val {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    {α : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶
      (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme}
    (hα : IsConeToTotalSpaceHom e E A hdeg α) :
    ∃ hα1 : α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) = puncturedConeToProduct e E A hdeg,
      ∀ i : Fin (N + 1),
        conePuncturedLineBundle.contractSections' e A (puncturedConeToProduct e E A hdeg)
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv' (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) (α ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι)
            (by rw [CategoryTheory.Category.assoc]; exact hα1))
          (sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e i)) =
        puncturedConeToProduct.coordOverProduct e E A hdeg i := by
  obtain ⟨hα1, h⟩ := hα
  refine ⟨hα1, fun i => ?_⟩
  have hi := h i
  inline_aux_proofs at hi
  exact hi

end
