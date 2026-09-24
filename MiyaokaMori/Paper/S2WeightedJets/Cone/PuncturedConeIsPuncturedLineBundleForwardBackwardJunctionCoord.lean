import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardInlineAuxProofs
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardSectionAPI

/-! # Junction z: `coordOverProduct` unfolded in the section API

The body of `coordOverProduct` carries `…_proof_k` auxiliary lemmas and is typed through `Γ(-, ⊤)` and
`pullback pr₁ ⋙ pullback g`; see `…JunctionBeta`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `coordOverProduct` in the section API: z_i over C ×ₖ X is Ψ of z_i over C. -/
theorem puncturedConeToProduct.coordOverProduct_eq {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) (i : Fin (N + 1)) :
    puncturedConeToProduct.coordOverProduct e E A hdeg i =
      AlgebraicGeometry.Scheme.Modules.uncompSection (puncturedConeToProduct e E A hdeg) (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) A
        (AlgebraicGeometry.Scheme.Modules.transportSection (puncturedConeToProduct.comp_fst e E A hdeg).symm A
          (puncturedConeToProduct.coord e E A hdeg i)) := by
  delta puncturedConeToProduct.coordOverProduct
  exact (AlgebraicGeometry.Scheme.Modules.uncompSection_transportSection_eq_app _ _ _ _ _).symm

end
