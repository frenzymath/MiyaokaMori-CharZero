import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardInlineAuxProofs
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardSectionAPI

/-! # Junction β: `IsTotalSpaceToConeHom` restated in the section API

The body of `IsTotalSpaceToConeHom` (a `Prop`-valued definition) carries the auxiliary lemmas
`…_proof_k` produced by `abstractNestedProofs`, and its two sides are typed through `Γ(-, ⊤)` and
`(Over.mk π).hom`. This module is the only place where that shape meets the section API of
`…ForwardBackwardTransport`; the kernel needs 20–30 s for the single conversion, hence its own module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `IsTotalSpaceToConeHom` in the section API: β ≫ g = π and, for every i,
β^*z_i (transported to Γ(Tot(L)^×, π^*pr₁^*A)) = ⟨w_taut, π^*q_i⟩. -/
theorem IsTotalSpaceToConeHom.exists_val {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    {β : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶
      (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme}
    (hβ : IsTotalSpaceToConeHom e E A hdeg β) :
    ∃ hβ1 : β ≫ puncturedConeToProduct e E A hdeg = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)),
      ∀ i : Fin (N + 1),
        AlgebraicGeometry.Scheme.Modules.transportSection hβ1 ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)
            (AlgebraicGeometry.Scheme.Modules.pullbackSection β (puncturedConeToProduct e E A hdeg) ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)
              (puncturedConeToProduct.coordOverProduct e E A hdeg i)) =
          conePuncturedLineBundle.contractSections' e A (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A)) (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle.coordinate C e i)) := by
  obtain ⟨hβ1, h⟩ := hβ
  refine ⟨hβ1, fun i => ?_⟩
  have hb := (AlgebraicGeometry.Scheme.Modules.transportSection_pullbackSection_eq_app _ _ _ _ _ _).trans (h i)
  have hc := hb.trans (conePuncturedLineBundle.contractSections'_eq e A _ _ _).symm
  inline_aux_proofs at hc
  exact hc

end
