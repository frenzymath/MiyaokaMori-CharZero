import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The unit `O_X`-module, typed in `X.Modules`

`SheafOfModules.unit X.ringCatSheaf` (Mathlib) has type `SheafOfModules X.ringCatSheaf`. The
category of sheaves of modules on a scheme used here is `X.Modules`, a plain `def` around the
same type, so a hom `SheafOfModules.unit … ⟶ M` elaborates in the wrong category
(`Scheme.Modules.Hom.app`, `.presheaf`, `.support`, … do not apply; a type ascription
`(… : X.Modules)` does not move the term either), and instance search finds
`IsLocallyFree` / `IsFiniteType` for a reducible name of type `X.Modules` but not for the bare term.

`unitModule X` is that reducible name: the unique spelling of the structure sheaf as an object of
`X.Modules`. Being an `abbrev`, it is reducibly equal to Mathlib's term, so
every Mathlib lemma about `SheafOfModules.unit` applies (`simp [unitModule]` unfolds it when a
syntactic match is needed). No mathematical content: this is Mathlib's unit object with a type.

The module imports only Mathlib, so it can be imported from anywhere. Import it directly wherever
the name is used. -/

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The structure sheaf `O_X` as an object of `X.Modules` (Mathlib's `SheafOfModules.unit
X.ringCatSheaf` with the category fixed; reducible). -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

end AlgebraicGeometry.Scheme.Modules

end
