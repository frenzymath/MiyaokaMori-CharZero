import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionTruncation
/-! # Dimension of a scheme

The dimension of a scheme as a natural number: the Krull dimension of the underlying topological
space, truncated to `ℕ` (`0` for the empty scheme and in infinite dimension). A closed subvariety
gets `V.dimension := V.carrier.dimension`. For a `k`-scheme of finite type the dimension is finite
and the truncation loses nothing.

**One definition of dimension.** `Scheme.dimension` is
the only `ℕ`-valued scheme dimension of the library: `Variety.dim`, `Variety.dimension` and
`ClosedSubvariety.dimension` are `abbrev`s of it. The primitive is `topologicalKrullDim X : WithBot ℕ∞`;
`Scheme.dimension` is its truncation `(·.unbotD 0).toNat` (`⊥ ↦ 0` for the empty scheme, `⊤ ↦ 0` for
infinite dimension), and it carries information only when both are excluded — exactly the hypotheses of
`Scheme.dimension_spec` / `Scheme.dimension_eq_iff`, the two lemmas through which every comparison of
`X.dimension` with `topologicalKrullDim X` must go (both are corollaries of
`MiyaokaMori.natCast_unbotD_toNat`, `DimensionTruncation.lean`). For varieties the hypotheses are
automatic (`Variety.dim_spec`, `VarietyDimension.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The dimension of a scheme: the topological Krull dimension truncated to `ℕ`. -/
noncomputable def AlgebraicGeometry.Scheme.dimension (X : AlgebraicGeometry.Scheme.{u}) : ℕ :=
  (WithBot.unbotD 0 (topologicalKrullDim X)).toNat

/-- The truncation loses nothing away from `⊥` (empty scheme) and `⊤` (infinite dimension). -/
theorem AlgebraicGeometry.Scheme.dimension_spec (X : AlgebraicGeometry.Scheme.{u})
    (h : topologicalKrullDim X ≠ ⊥) (h' : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim X = (X.dimension : WithBot ℕ∞) :=
  (MiyaokaMori.natCast_unbotD_toNat h h').symm

/-- The single coercion lemma for `X.dimension = n` versus `topologicalKrullDim X = n`
(hypotheses: nonempty, finite-dimensional). -/
theorem AlgebraicGeometry.Scheme.dimension_eq_iff (X : AlgebraicGeometry.Scheme.{u})
    (h : topologicalKrullDim X ≠ ⊥) (h' : topologicalKrullDim X ≠ ⊤) (n : ℕ) :
    X.dimension = n ↔ topologicalKrullDim X = (n : WithBot ℕ∞) :=
  MiyaokaMori.unbotD_toNat_eq_iff h h' n

/-- Without any hypothesis the truncated dimension is a lower bound for the Krull dimension of a
nonempty scheme (for the empty scheme both sides are compared as `0 ≤ ⊥`, which is false, hence the
hypothesis). -/
theorem AlgebraicGeometry.Scheme.natCast_dimension_le (X : AlgebraicGeometry.Scheme.{u})
    (h : topologicalKrullDim X ≠ ⊥) :
    (X.dimension : WithBot ℕ∞) ≤ topologicalKrullDim X :=
  MiyaokaMori.natCast_unbotD_toNat_le h

/-- The dimension of a closed subvariety is the dimension of its underlying scheme. -/
noncomputable abbrev ClosedSubvariety.dimension {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) : ℕ :=
  V.carrier.dimension

end
