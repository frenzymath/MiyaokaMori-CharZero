import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections

/-! # Finite type of quasi-coherent sheaves on affine schemes (Stacks 01PB)

On an affine scheme, a quasi-coherent sheaf is of finite type iff its global sections form a finitely
generated module (Stacks 01PB, together with the fact that a quasi-coherent sheaf on an affine scheme
is determined by its global sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 01PB: a quasi-coherent sheaf on an affine scheme is of finite type iff its global sections
are a finitely generated module. -/
theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_iff_finite_sections {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    SheafOfModules.IsFiniteType M ↔ Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  constructor
  · intro _
    exact AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType M
      (AlgebraicGeometry.isAffineOpen_top X)
  · intro hM
    letI : Module.Finite Γ(X, ⊤) Γ(M, ⊤) := hM
    apply AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections M
    intro x
    exact ⟨⊤, AlgebraicGeometry.isAffineOpen_top X, trivial, hM⟩

end

#print axioms AlgebraicGeometry.Scheme.Modules.isFiniteType_iff_finite_sections
