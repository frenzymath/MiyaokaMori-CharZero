import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk

/-! # The stalk functor on sheaves of modules

The stalk functor `X.Modules ⥤ ModuleCat (O_{X,x})`: on objects `M ↦ M_x` (`M.stalk x`, the stalk
of the underlying abelian presheaf with the `O_{X,x}`-module structure of Mathlib's `Stalk.lean`),
on morphisms `φ ↦` the induced stalk map (`TopCat.Presheaf.stalkFunctor` applied to the morphism of
underlying abelian presheaves; it is compatible with the `O_{X,x}`-action, hence linear).

Source: Stacks 01AJ (stalk of a sheaf of modules).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- On objects `M ↦ M.stalk x`; on morphisms the stalk map of the underlying abelian presheaves
   `(TopCat.Presheaf.stalkFunctor Ab x).map φ.mapPresheaf` (Mathlib's `Scheme.Modules.Hom.mapPresheaf`),
   which is compatible with the `O_{X,x}`-action (it is `O(U)`-linear on germs over each open `U`),
   hence a linear map. -/

/-- The stalk functor `X.Modules ⥤ ModuleCat (O_{X,x})`: a reducible alias, in the `Scheme.Modules`
namespace, of the one construction `AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x` (see `ModuleGenericFiber`). -/
abbrev AlgebraicGeometry.Scheme.Modules.stalkFunctor {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x

/- On objects the stalk functor gives exactly `M.stalk x`. -/

theorem AlgebraicGeometry.Scheme.Modules.stalkFunctor_obj {X : AlgebraicGeometry.Scheme.{u}} (x : X)
    (M : X.Modules) : (AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj M = M.stalk x :=
  rfl

end
