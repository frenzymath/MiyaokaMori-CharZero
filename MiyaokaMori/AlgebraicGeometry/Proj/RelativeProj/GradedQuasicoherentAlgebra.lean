import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Graded quasi-coherent algebra sheaves

An `ℕ`-graded quasi-coherent `O_X`-algebra sheaf `S = ⊕_{m ≥ 0} S_m` on a scheme `X`: the input of
the relative Proj. The graded coordinate algebra of the jet scheme in §2 of the paper is such a sheaf.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- `⊗`, `𝟙_`, `λ_`, `α_`, `▷`, `◁` are the monoidal structure of `X.Modules` and `β_` its braiding;
   the indices `0 + m`, `m + (n + p)`, `n + m` are only propositionally equal to `m`, `m + n + p`,
   `m + n`, so they are transported with `eqToHom`. -/

structure AlgebraicGeometry.Scheme.GradedQCAlgebra (X : AlgebraicGeometry.Scheme.{u}) where
  part : ℕ → X.Modules
  [quasicoherent : ∀ m, (part m).IsQuasicoherent]
  mul : ∀ m n, part m ⊗ part n ⟶ part (m + n)
  one : 𝟙_ X.Modules ⟶ part 0
  one_mul : ∀ m, (one ▷ part m) ≫ mul 0 m =
    (λ_ (part m)).hom ≫ eqToHom (congrArg part (Nat.zero_add m).symm)
  mul_assoc : ∀ m n p, (α_ (part m) (part n) (part p)).hom ≫ (part m ◁ mul n p) ≫ mul m (n + p) =
    (mul m n ▷ part p) ≫ mul (m + n) p ≫ eqToHom (congrArg part (Nat.add_assoc m n p))
  mul_comm : ∀ m n, (β_ (part m) (part n)).hom ≫ mul n m =
    mul m n ≫ eqToHom (congrArg part (Nat.add_comm m n))

end
