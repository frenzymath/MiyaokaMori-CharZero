import MiyaokaMori.Prelude

/-! # The stalk of a sheaf of modules as a module over the local ring

The stalk of an `O_X`-module `E` at `x` as an `O_{X,x}`-module: the underlying abelian group is the
stalk at `x` of the underlying presheaf of abelian groups of `E`, and the module structure is the
instance of `Mathlib.Algebra.Category.ModuleCat.Stalk` (for a presheaf of modules `M` over
`R ⋙ forget₂`, `stalk M.presheaf x` is an `R.stalk x`-module), wrapped with `ModuleCat.of`.

Source: `Mathlib.Algebra.Category.ModuleCat.Stalk`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The stalk is the object `ModuleCat.of _ (M.presheaf.stalk x)` of `AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor`,
   with the `O_{X,x}`-module structure `moduleStalkModule` (the instance of Mathlib's `Stalk.lean`).
   It is an `abbrev`, so that it is transparently the object of that one stalk functor. -/

/-- The stalk of `E : X.Modules` at `x` as an `O_{X,x}`-module: the object of the stalk functor
`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x` (carrier `E.presheaf.stalk x`, Mathlib's module structure). -/
abbrev AlgebraicGeometry.Scheme.Modules.stalk {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (x : X) : ModuleCat.{u} (X.presheaf.stalk x) :=
  (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x).obj E

end
