import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingIdeal
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveVanishingLocus

/-! # Homogeneous generators of the ideal of `X`

A family of homogeneous generators `F_j` of the homogeneous ideal of `X ⊂ ℙ^N`, of degrees
`1 ≤ deg F_j ≤ δ`; if the ideal is zero, `δ = 1` by convention (§2.1 of the paper).
The field `spans` is expressed by the predicate `IsVanishingLocus e F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Homogeneous generators `F_j` (indexed by `ι`) of the homogeneous ideal of the embedded variety `X ⊂ ℙ^N`, of
degrees `deg j` with `1 ≤ deg j ≤ δ`. -/
structure EmbeddingEquations (k : Type u) [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (δ : ℕ) where
  ι : Type u
  deg : ι → ℕ
  F : ι → MvPolynomial (Fin (N + 1)) k
  homogeneous : ∀ j, (F j).IsHomogeneous (deg j)
  deg_le : ∀ j, deg j ≤ δ
  deg_pos : ∀ j, 0 < deg j
  δ_pos : 0 < δ
  /-- The `F_j` generate the saturated homogeneous ideal `Γ_*(I_X)` (`IsVanishingLocus e F`, i.e.
  `Ideal.span (Set.range F) = (projectiveVanishingIdeal e.emb.ker).toIdeal`). -/
  spans : IsVanishingLocus e F

end
