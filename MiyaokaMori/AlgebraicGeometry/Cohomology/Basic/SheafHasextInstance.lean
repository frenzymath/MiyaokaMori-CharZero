import MiyaokaMori.Prelude

/-! # `HasExt` for abelian sheaves on a scheme

Existence of `Ext` groups (`HasExt.{u}`) for the category of abelian sheaves on a scheme `X`, in
Mathlib's Grothendieck universe `u`. Mathlib provides this automatically for Grothendieck abelian
categories (`IsGrothendieckAbelian.hasExt` via `Sheaf.instIsGrothendieckAbelian`). The instance
below is a `Prop` and merely a shortcut (`inferInstance`) for that instance chain, so that every
occurrence of `Sheaf.H` does not re-run the search `IsGrothendieckAbelian → HasSheafify → …`.
Consequently `sheafCohomology` (`Sheaf.H.{u} … : Type u`) is literally the same type as the
cohomology used in Mathlib's `TopCat`-level statements (e.g. Stacks 02UZ); no universe bridge is
needed.

Source: Mathlib `CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`
(`IsGrothendieckAbelian.hasExt`), `CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean`
(`Sheaf.instIsGrothendieckAbelian`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Shortcut instance: abelian sheaves on a scheme `X` have `Ext` groups in universe `u`. -/
instance AlgebraicGeometry.Scheme.sheafAddCommGrpHasExt (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  inferInstance

end
