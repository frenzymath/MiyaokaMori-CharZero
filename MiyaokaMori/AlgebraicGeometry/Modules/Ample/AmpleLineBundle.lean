import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Ample invertible sheaves

An invertible sheaf `L` on a quasi-compact scheme `X` is ample if every point lies in an affine
nonvanishing locus `X_s` of a global section `s` of some `L^{⊗m}`, `m > 0` (Stacks 01PS).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in

/-- `L` is ample: `X` is quasi-compact and every point `x` lies in an affine nonvanishing locus
`X_s` of a global section `s` of `L^{⊗m}` for some `m > 0` (Stacks 01PS). -/
def AlgebraicGeometry.IsAmple {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] : Prop :=
  CompactSpace X ∧
    ∀ x : X, ∃ (m : ℕ) (_ : 0 < m)
      (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L m, ⊤)),
      x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus s ∧
      AlgebraicGeometry.IsAffineOpen
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L m).nonvanishingLocus s)

end
