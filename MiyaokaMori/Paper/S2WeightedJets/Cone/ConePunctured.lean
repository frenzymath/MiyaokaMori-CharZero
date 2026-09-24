import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeSmooth
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionEquationsVanish
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured

/-! # The punctured cone

Two properties of the punctured cone `𝒵^×` (eq. (2.1) of the paper): the morphism
`𝒵^× → C × X` realizes `𝒵^×` as the punctured total space of `pr₁^*A ⊗ pr₂^*O_X(-1)`; consequently
`𝒵^×` is smooth over `C` of relative dimension `n+1`, and the seed section `s` lands in `𝒵^×`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem puncturedCone_spec {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ n : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (f : C ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension n (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord) :
    Nonempty ((puncturedCone (seedLineBundle e f) N E.deg E.deg_pos E.F E.homogeneous).toScheme ≅
        (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e (seedLineBundle e f))).toScheme) ∧
      AlgebraicGeometry.SmoothOfRelativeDimension (n + 1)
        ((puncturedCone (seedLineBundle e f) N E.deg E.deg_pos E.F E.homogeneous).ι ≫
          (twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous).hom) ∧
      ∃ s' : C ⟶ (puncturedCone (seedLineBundle e f) N E.deg E.deg_pos E.F E.homogeneous).toScheme,
        s' ≫ (puncturedCone (seedLineBundle e f) N E.deg E.deg_pos E.F E.homogeneous).ι =
          (seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous
            (seedSection_equations_vanish e E f coord hcoord)).1 := by
  obtain ⟨φ, -⟩ := puncturedConeIsoPuncturedTotalSpace e E (seedLineBundle e f) E.deg_pos
  refine ⟨⟨φ⟩, puncturedCone_smoothOfRelativeDimension e E (seedLineBundle e f) E.deg_pos, ?_⟩
  exact seedSection_mem_punctured e E f coord hcoord E.deg_pos
    (seedSection_equations_vanish e E f coord hcoord)

end
