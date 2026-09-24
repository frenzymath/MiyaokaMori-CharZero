import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan

/-! # Finite limits and colimits of sheaves of modules agree with those of abelian sheaves (Stacks 01AH)

Finite limits and finite colimits of `O_X`-modules agree with those of the underlying abelian sheaves
(Stacks 01AH): the forgetful functor `Mod(O_X) → Ab(X)` is exact.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance SheafOfModules.toSheaf_preservesFiniteColimits {X : AlgebraicGeometry.Scheme.{u}} :
    CategoryTheory.Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := by
  exact MiyaokaMori.FreeStalk.toSheaf_preservesFiniteColimits X

-- The finite-limits half is already in Mathlib:

-- noncomputable instance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R)

--   (Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits)

end
