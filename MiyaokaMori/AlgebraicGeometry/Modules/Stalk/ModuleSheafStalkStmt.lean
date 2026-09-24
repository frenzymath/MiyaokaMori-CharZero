import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # Stalks of sheaves of modules (statement module)

The stalk `E_x` of an `O_X`-module `E` at a point `x`, with its `O_{X,x}`-module structure
(Mathlib provides the stalk of the underlying abelian sheaf; the module structure is the one of
`Mathlib.Algebra.Category.ModuleCat.Stalk`). The definition itself lives in `ModuleSheafStalk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The stalk of a sheaf of modules is the object `ModuleCat.of _ (M.presheaf.stalk x)` of
   `AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor`, with the `O_{X,x}`-module structure `moduleStalkModule`
   (the instance of Mathlib's `Stalk.lean`). -/

end
