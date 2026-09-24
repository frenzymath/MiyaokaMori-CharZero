import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01us

/-! # The relative tangent sheaf

The relative tangent sheaf `T_{Z/C} := (Ω_{Z/C})^∨`, the `O_Z`-dual of the sheaf of relative
differentials of a morphism of schemes `p : Z → C` (§2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.relativeTangent {Z C : AlgebraicGeometry.Scheme.{u}}
    (p : Z ⟶ C) : Z.Modules :=
  AlgebraicGeometry.Scheme.Modules.dual (AlgebraicGeometry.Omega p)

end
