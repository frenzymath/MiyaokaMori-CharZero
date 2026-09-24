import MiyaokaMori.Prelude

/-! # Finite direct sum powers of a sheaf of modules

The finite direct sum power `V^{⊕n}` of a sheaf of modules (the `A^{⊕(N+1)}` of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `X.Modules` is an abelian category, hence has finite biproducts; Mathlib's `Abelian.hasFiniteBiproducts`
   is not a global instance (lean4#2055), so we register it for `X.Modules` here. -/

instance AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.Limits.HasFiniteBiproducts X.Modules :=
  CategoryTheory.Abelian.hasFiniteBiproducts

noncomputable def AlgebraicGeometry.Scheme.Modules.pow {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (n : ℕ) : X.Modules :=
  CategoryTheory.Limits.biproduct (fun _ : Fin n => V)

end
