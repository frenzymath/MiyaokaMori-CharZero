import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX

/-! # The Chow group with rational coefficients

The Chow group with rational coefficients `A_p(X)_ℚ = A_p(X) ⊗_ℤ ℚ`. The weighted tautological class
`H_k` of §2 of the paper lives here (one could equally use `NS(X) ⊗ ℚ`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Chow group with rational coefficients `A_p(X)_ℚ = A_p(X) ⊗_ℤ ℚ`. -/
noncomputable def AlgebraicGeometry.ChowGroupRat (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) : Type u :=
  TensorProduct ℤ ℚ (AlgebraicGeometry.ChowGroup X p)

noncomputable instance (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    AddCommGroup (AlgebraicGeometry.ChowGroupRat X p) := inferInstanceAs (AddCommGroup (TensorProduct ℤ ℚ _))

noncomputable instance (X : AlgebraicGeometry.Scheme.{u}) (p : ℕ) :
    Module ℚ (AlgebraicGeometry.ChowGroupRat X p) := inferInstanceAs (Module ℚ (TensorProduct ℤ ℚ _))

/-- The canonical map `A_p(X) → A_p(X)_ℚ`, `c ↦ 1 ⊗ c`. -/
noncomputable def AlgebraicGeometry.ChowGroupRat.of {X : AlgebraicGeometry.Scheme.{u}} {p : ℕ} :
    AlgebraicGeometry.ChowGroup X p →+ AlgebraicGeometry.ChowGroupRat X p :=
  (TensorProduct.mk ℤ ℚ (AlgebraicGeometry.ChowGroup X p) 1).toAddMonoidHom

end
