import MiyaokaMori.Prelude

/-! # The free sheaf of modules on an index set

The free `O_X`-module `O_X^{(I)}` on an index set `I` — the comparison object for local freeness.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The free sheaf is Mathlib's `SheafOfModules.free` (with `R := X.ringCatSheaf`); `Scheme.Modules.free`
   is just an abbreviation for it (Mathlib has no such name). -/

noncomputable abbrev AlgebraicGeometry.Scheme.Modules.free {X : AlgebraicGeometry.Scheme.{u}} (I : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) I

end
