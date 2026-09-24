import MiyaokaMori.Prelude

/-! # Long exact sequence of sheaf cohomology

A short exact sequence of abelian sheaves on a scheme induces a long exact sequence of
sheaf cohomology groups `H^0 → H^0 → H^0 → H^1 → …`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The long exact sequence of sheaf cohomology attached to a short exact sequence of abelian
sheaves on a scheme, as an exact sequence in `AddCommGrpCat.{u}`. This is Mathlib's
`Ext.covariantSequence_exact`; the `Ext` groups live in `Type u`
(instance `IsGrothendieckAbelian.hasExt`), the same universe as `sheafCohomology`.
The sequence carries no `k`-linear structure; the `k`-linear version (with connecting map
and `range = ker` identities) is in `SheafCohomologyLinearLongExact.lean`. -/
theorem sheafCohomology_long_exact {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (CategoryTheory.Abelian.Ext.covariantSequence
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) hS n₀ n₁ h :
      CategoryTheory.ComposableArrows AddCommGrpCat.{u} 5).Exact := by
  exact CategoryTheory.Abelian.Ext.covariantSequence_exact _ hS n₀ n₁ h

end
