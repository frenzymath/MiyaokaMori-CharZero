import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinear

/-! # The linear isomorphism `H'(M, n, ⊤) ≃ₗ H^n(X, M)`

The `Γ(X,⊤)`-linear form of `H'TopAddEquiv`:

`H'(M, n, ⊤) ≃ₗ[Γ(X,⊤)] sheafCohomology X M n`

Linearity is `CategoryTheory.Sheaf.H'TopAddEquiv_comp_mk₀` with `f = M.smulEnd r`: on both sides
scalar multiplication is postcomposition with `Ext.mk₀ (M.smulEnd r)` (`Scheme.Modules.moduleSheafH'`
and `moduleSheafH` are the same formula), and the isomorphism commutes with postcomposition. The
comparison of `finrank` / `χ` needs this linear form, not a bare `Nonempty`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The `Γ(X,⊤)`-linear version of `H'TopAddEquiv`**: `H'(M, n, ⊤) ≃ₗ[Γ(X,⊤)] H^n(X, M)`. -/
def sheafCohomologyTopLinearEquiv (M : X.Modules) (n : ℕ) :
    (M.toAddCommGrpSheaf.H' n (⊤ : X.Opens) : Type u) ≃ₗ[Γ(X, ⊤)]
      AlgebraicGeometry.sheafCohomology X M n :=
  { CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop M.toAddCommGrpSheaf n with
    map_smul' := fun r x =>
      CategoryTheory.Sheaf.H'TopAddEquiv_comp_mk₀ _ isTerminalTop (M.smulEnd r) n x }

end AlgebraicGeometry

end
