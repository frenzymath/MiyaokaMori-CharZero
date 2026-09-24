import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup

/-! # The vanishing ideal of a closed point

Two descriptions of the ideal sheaf of a closed point agree: the vanishing ideal of the reduced
closed subscheme, `IdealSheafData.vanishingIdeal ⟨{p}, hp⟩`, equals
`pointIdeal X p = (X.fromSpecResidueField p).ker`.

Proof from Mathlib's `IdealSheafData.map_vanishingIdeal`, `map_bot`, `range_fromSpecResidueField`.
Used by `pointBlowup.iso_away` to match the blow-up of Stacks 01OG with the universal-property
predicate `IsBlowup (pointIdeal S p) _`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The vanishing ideal sheaf of a closed point `p` is the kernel of the residue field point
`Spec κ(p) → X`.

Proof sketch: `pointIdeal X p = (X.fromSpecResidueField p).ker = (⊥ : IdealSheafData (Spec κ(p))).map f`
(`map_bot`); `Spec κ(p)` is reduced, so `⊥ = nilradical = vanishingIdeal ⊤`; `map_vanishingIdeal`
gives `(vanishingIdeal ⊤).map f = vanishingIdeal (closure (f '' univ))`, and
`range f = {p}` (`range_fromSpecResidueField`) is closed. -/
theorem AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal
    {X : AlgebraicGeometry.Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X)) :
    AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ =
      MiyaokaMori.Statement.pointIdeal X p := by
  unfold MiyaokaMori.Statement.pointIdeal
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.map_bot,
    ← AlgebraicGeometry.Scheme.nilradical_eq_bot (X := AlgebraicGeometry.Spec (X.residueField p)),
    ← AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top,
    AlgebraicGeometry.Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp [Closeds.coe_closure]

end
