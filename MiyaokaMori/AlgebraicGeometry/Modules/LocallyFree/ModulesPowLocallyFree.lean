import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow

/-! # Finite direct sums of locally free sheaves are locally free

A finite direct sum of locally free sheaves is locally free (`A^{⊕(N+1)}` is a vector bundle of rank
`N+1`; used for the total space `Tot(A^{⊕(N+1)})` in §2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A finite direct sum `M^{⊕n}` of a locally free sheaf is locally free. -/
instance AlgebraicGeometry.Scheme.Modules.pow_isLocallyFree {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.pow V n).IsLocallyFree :=
  AlgebraicGeometry.Scheme.Modules.biproduct_isLocallyFree (fun _ : Fin n => V)

end
