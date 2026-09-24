import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # A fixed projective embedding of a smooth projective variety

For a smooth projective variety `X` we fix one projective embedding: `embDim = N` and
`embedding : X ↪ P^N`, chosen from `X.projective` and packaged as a `ProjectiveEmbedding`. This is the
"fix the embedding `X ↪ P^N`" of §2 of the paper.

`X.projective : IsProjectiveOver k X.toScheme` (`∃ N i`, a closed immersion `i` over `Spec k`) gives
`Nonempty (Σ N, ProjectiveEmbedding k X.toScheme N)`; `embData := Classical.choice` picks one,
`embDim := embData.1` and `embedding := embData.2`. The choice is classical, as in the paper; downstream
statements use `X.embDim` / `X.embedding` only by name, so they all speak about this one fixed choice.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Projectivity `X.projective` yields at least one projective embedding `X ↪ P^N_k` (with its
dimension `N`), packaged as a `ProjectiveEmbedding`. -/
theorem SmoothProjectiveVariety.nonempty_projectiveEmbedding {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) :
    Nonempty (Σ N : ℕ, ProjectiveEmbedding k X.toScheme N) := by
  obtain ⟨N, i, hi, hover⟩ := X.projective
  exact ⟨⟨N, @ProjectiveEmbedding.mk k _ X.toScheme _ N i hi hover.comp_over⟩⟩

/-- The fixed embedding datum `⟨N, X ↪ P^N⟩` ("fix the embedding", §2 of the paper): one witness of
`X.projective`, chosen classically. -/
noncomputable def SmoothProjectiveVariety.embData {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    Σ N : ℕ, ProjectiveEmbedding k X.toScheme N :=
  Classical.choice X.nonempty_projectiveEmbedding

/-- The dimension `N` of the target projective space of the fixed embedding. -/
noncomputable abbrev SmoothProjectiveVariety.embDim {k : Type u} [Field k] (X : SmoothProjectiveVariety k) : ℕ :=
  X.embData.1

/-- The fixed embedding `X ↪ P^{embDim}_k`. -/
noncomputable def SmoothProjectiveVariety.embedding {k : Type u} [Field k] (X : SmoothProjectiveVariety k) :
    ProjectiveEmbedding k X.toScheme X.embDim :=
  X.embData.2

end
