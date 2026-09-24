import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSmoothRelativeDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The punctured cone is smooth over `C`

`𝒵^×` is smooth over `C` of relative dimension `n+1` (§2.1 of the paper, after
eq. (2.1): "in particular, `𝒵^×` is smooth over `C` of relative dimension `n+1`").

Proof: `Z^× → C` is by definition `puncturedConeToProduct.base`, and
`puncturedConeToProduct ≫ pr_1 = base` (`pullback.lift_fst`). By
`puncturedConeIsoPuncturedTotalSpace`, `puncturedConeToProduct = φ.hom ≫ ι ≫ Tot(L).hom`,
where `φ` is an isomorphism (an open immersion, relative dimension `0`), `ι` is an open immersion
(relative dimension `0`), `Tot(L) → C × X` is the total space of a line bundle (relative dimension `1`:
`totalSpace_smoothOfRelativeDimension` + `rankAtStalk_eq_one_of_isLineBundle`), and
`pr_1 : C × X → C` is the base change of `X → Spec k` (relative dimension `n`:
`smoothOfRelativeDimension_isStableUnderBaseChange`). Mathlib's `smoothOfRelativeDimension_comp`
gives `0 + (0 + (1 + n)) = n + 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem puncturedCone_smoothOfRelativeDimension {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ n : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)
    [AlgebraicGeometry.SmoothOfRelativeDimension n (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] :
    AlgebraicGeometry.SmoothOfRelativeDimension (n + 1)
      ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫ (twistedAffineCone A N E.deg E.F E.homogeneous).hom) := by
  obtain ⟨φ, hφ⟩ := puncturedConeIsoPuncturedTotalSpace e E A hdeg
  -- `Z^× → C` is `puncturedConeToProduct ≫ pr_1`
  have hbase : (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
      (twistedAffineCone A N E.deg E.F E.homogeneous).hom =
      puncturedConeToProduct e E A hdeg ≫
        CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [puncturedConeToProduct, CategoryTheory.Limits.pullback.lift_fst]
    rfl
  rw [hbase, ← hφ]
  -- `Tot(L) → C × X`: total space of a line bundle, relative dimension 1
  have : AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom :=
    AlgebraicGeometry.Scheme.totalSpace_smoothOfRelativeDimension _ 1
      (fun x => AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle _ x)
  -- `pr_1 : C × X → C`: base change of `X → Spec k`, relative dimension `n`
  have hbc : MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.SmoothOfRelativeDimension n) :=
    AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange n
  have : AlgebraicGeometry.SmoothOfRelativeDimension n
      (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :=
    hbc.of_isPullback (CategoryTheory.IsPullback.of_hasPullback _ _).flip inferInstance
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (0 + (0 + (1 + n)))
      (φ.hom ≫ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι ≫
        (AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A)).hom ≫
        CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := inferInstance
  have hn : 0 + (0 + (1 + n)) = n + 1 := by omega
  rw [hn] at h
  simpa only [CategoryTheory.Category.assoc] using h

end
