import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt

/-! # The rank of a sheaf of modules at a point

The rank of an `O_X`-module at a point: the dimension of the fibre `E_x ⊗_{O_{X,x}} κ(x)` as a
`κ(x)`-vector space.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped TensorProduct

/-- The rank of `E` at `x`: `dim_{κ(x)} (κ(x) ⊗_{O_{X,x}} E_x)`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.rankAtStalk {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (x : X) : ℕ :=
  letI := (X.residue x).hom.toAlgebra
  Module.finrank (X.residueField x) (X.residueField x ⊗[X.presheaf.stalk x] (E.stalk x))

end
