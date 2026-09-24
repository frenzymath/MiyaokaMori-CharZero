import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00ot
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.StandardSmoothChartLocalDimension

/-! # Local dimension of a standard smooth algebra (Stacks 00T7 (7))

Stacks 00T7 (7), over a field: if `S` is a standard smooth `k`-algebra of relative dimension `n`
(`k[x_1..x_N]/(f_1..f_c)` with `n = N − c`), then `Spec S` has local dimension `n` at every point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 00T7 (7) over a field: a standard smooth `k`-algebra of relative dimension `n` has local
dimension `n` at every point of its spectrum. -/

theorem Algebra.IsStandardSmoothOfRelativeDimension.localDimension_eq {k S : Type u} [Field k]
    [CommRing S] [Algebra k S] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k S]
    (x : AlgebraicGeometry.Spec (CommRingCat.of S)) :
    localDimension (AlgebraicGeometry.Spec (CommRingCat.of S)) x = n := by
  -- via "standard smooth = étale over a polynomial ring" and the going-down height formula
  -- (`StandardSmoothChartLocalDimension.lean`), with the chart `V = ⊤`
  let e : S ≃+* Γ(AlgebraicGeometry.Spec (CommRingCat.of S), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv
  have h1 : (algebraMap k S).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  have h2 : ((e : S →+* Γ(AlgebraicGeometry.Spec (CommRingCat.of S), ⊤)).comp (algebraMap k S)).IsStandardSmoothOfRelativeDimension n := by
    have := (RingHom.IsStandardSmoothOfRelativeDimension.equiv e).comp h1
    rwa [zero_add] at this
  exact (AlgebraicGeometry.isAffineOpen_top _).localDimension_eq_of_isStandardSmoothOfRelativeDimension
    _ h2 x trivial

end
