import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSmoothRelativeDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The projection of the punctured cone to `C × X` is smooth

The natural morphism `puncturedConeToProduct : 𝒵^× → C ×_k X` is smooth of relative dimension `1`
(eq. (2.1) of the paper).

Proof: by `puncturedConeIsoPuncturedTotalSpace`, `puncturedConeToProduct = φ.hom ≫ ι ≫ Tot(L).hom`,
where `φ` is an isomorphism (an open immersion, relative dimension `0`), `ι` is an open immersion
(relative dimension `0`) and `Tot(L) → C × X` is the total space of a line bundle (relative dimension
`1`: `totalSpace_smoothOfRelativeDimension` + `rankAtStalk_eq_one_of_isLineBundle`). Mathlib's
`smoothOfRelativeDimension_comp` gives `0 + (0 + 1) = 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem puncturedConeToProduct_smoothOfRelativeDimension {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {X : SmoothProjectiveVariety k} {N δ : ℕ}
    (e : ProjectiveEmbedding k X.toScheme N) (E : EmbeddingEquations k e δ)
    (A : C.toScheme.Modules) [A.IsLineBundle] (hdeg : ∀ j, 0 < E.deg j) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (puncturedConeToProduct e E A hdeg) := by
  obtain ⟨φ, hφ⟩ := puncturedConeIsoPuncturedTotalSpace e E A hdeg
  rw [← hφ]
  -- `Tot(L) → C × X`: total space of a line bundle, relative dimension 1
  have : AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom :=
    AlgebraicGeometry.Scheme.totalSpace_smoothOfRelativeDimension _ 1
      (fun x => AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle _ x)
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (0 + (0 + 1))
      (φ.hom ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫
        (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom) := inferInstance
  have hn : 0 + (0 + 1) = 1 := by omega
  rw [hn] at h
  exact h

end
