import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt

/-! # Torsion-free sheaves of modules

A sheaf of modules on a scheme is torsion-free if each stalk is a torsion-free module
over the local ring at that point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `M` is torsion-free: for every point `x`, the stalk `M_x` is a torsion-free
`O_{X,x}`-module (with the module structure `AlgebraicGeometry.Scheme.Modules.moduleStalkModule`). -/
def AlgebraicGeometry.Scheme.Modules.IsTorsionFree {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : Prop :=
  ∀ x : X, @Module.IsTorsionFree (X.presheaf.stalk x) (M.presheaf.stalk x) _ _
    (AlgebraicGeometry.Scheme.Modules.moduleStalkModule X M x)

end
