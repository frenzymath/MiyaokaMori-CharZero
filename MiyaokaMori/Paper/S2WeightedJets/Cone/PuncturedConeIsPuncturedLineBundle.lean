import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackward
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackwardForward
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForward
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackward

/-! # The punctured cone is a punctured line bundle

`𝒵^× ≅` the punctured total space of `pr₁^*A ⊗ pr₂^*O_X(-1)`, as schemes over `C × X`
(eq. (2.1) of the paper).

Top-level assembly: the forward morphism `α` and the backward morphism `β` are characterised by their
pairings (`IsConeToTotalSpaceHom` / `IsTotalSpaceToConeHom`, see `…Contract`); they are mutually
inverse by `…ForwardBackward` and `…BackwardForward`; compatibility with the structure morphisms to
`C × X` is the first clause of the characterisation of `α`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Z^× ≅ Tot(L)^×`, and the isomorphism lies over `C × X`: it matches `Z^× → C × X`
(`puncturedConeToProduct`) with the structure morphism of the punctured total space. -/

theorem puncturedConeIsoPuncturedTotalSpace {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ∃ φ : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ≅
        (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme,
      φ.hom ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫
          (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom =
        puncturedConeToProduct e E A hdeg := by
  obtain ⟨α, hα⟩ := puncturedCone_exists_isConeToTotalSpaceHom e E A hdeg
  obtain ⟨β, hβ⟩ := puncturedTotalSpace_exists_isTotalSpaceToConeHom e E A hdeg
  exact ⟨⟨α, β, isConeToTotalSpaceHom_comp_isTotalSpaceToConeHom e E A hdeg α β hα hβ,
      isTotalSpaceToConeHom_comp_isConeToTotalSpaceHom e E A hdeg α β hα hβ⟩, hα.1⟩

end
