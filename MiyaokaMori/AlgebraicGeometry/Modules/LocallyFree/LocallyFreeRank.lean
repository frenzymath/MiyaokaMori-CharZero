import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Local freeness of a module sheaf at a fixed finite rank

`IsLocallyFreeRank X M n` records an actual local trivialization of `M` by the
free module sheaf of rank `n` around every scheme point.  The isomorphism is part
of the witness, so this predicate cannot be satisfied by supplying a bare rank
label or an unrelated proposition.

The `SchemeOver` parameter carries the base field structure of the geometric object.
`ULift (Fin n)` keeps the indexing type in the universe of the scheme's section rings.
-/

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Proj

universe u

variable {k : Type u} [Field k]

/-- A genuine local free presentation of a module sheaf of fixed finite rank. -/
structure IsLocallyFreeRank (X : SchemeOver k) (M : X.scheme.Modules) (n : ℕ) : Prop where
  local_frame : ∀ x : X.scheme, ∃ U : X.scheme.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))

end AlgebraicGeometry.Scheme.Modules
