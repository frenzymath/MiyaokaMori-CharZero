import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension

/-! # A fixed projective embedding

A fixed projective embedding `X ↪ P^N` (a closed immersion over `k`), and `O_X(1)`, the pullback of
`O_{P^N}(1)` along it. The structure `ProjectiveEmbedding k X N` is the library's notion of a projective
embedding; the chart API (`chartKernelAway`, `chartIso`, `embeddingHomogeneousCore`,
`ProjectiveEmbeddingGlobalFactorization.existsUnique_factor`, …) is keyed on the closed immersion itself,
`{N} (emb : X ⟶ ProjectiveSpace N k) [IsClosedImmersion emb]`, and is applied to `e.emb` (the instance
`ProjectiveEmbedding.closed` provides `IsClosedImmersion e.emb`, and `e.over` the compatibility with the
structure morphisms). `O_X(1)` is written `e.oX 1`.

Source: §2 of the paper (Section 2), the embedding `X ↪ P^N` and `O_X(1)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

structure ProjectiveEmbedding (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (N : ℕ) where
  emb : X ⟶ ProjectiveSpace N k
  [closed : AlgebraicGeometry.IsClosedImmersion emb]
  «over» : emb ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)

attribute [instance] ProjectiveEmbedding.closed

noncomputable def ProjectiveEmbedding.oX {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (m : ℤ) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback e.emb).obj (projectiveSpaceTwist k N m)

end
