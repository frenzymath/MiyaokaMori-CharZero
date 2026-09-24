import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing

/-! # From a graded quasi-coherent algebra to a quasi-coherent algebra, on sections

A piecewise embedding `ι_m : S_m ⟶ A` of a graded quasi-coherent algebra `S = ⊕_m S_m` into a
quasi-coherent algebra `A` (compatible with unit and multiplication) induces ring homomorphisms on
sections `ψ_U : ⨁_m Γ(U, S_m) →+* A(U)` (`sectionsToRingHom`), compatible with restriction
(`sectionsToRingHom_restrict`).

Use: in the jet grading, `S_m := ker φ_m ⊆ π_*O_T` (the `λ^m`-eigensections of the `G_m`-action) and
`ι_m := kernel.ι`; this is the **map part** of the relative version of Stacks 0EKK
("`S = ⊕ S_m ⟶ A` is an isomorphism"; bijectivity is proved separately).

Reference: Stacks 0EKK (`G_m`-actions ⟺ `ℤ`-gradings), the map `⊕ A_n → A`; §2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (A : X.QCAlgebra)
  (ι : ∀ m, S.part m ⟶ A.carrier)

/-- `S.one ≫ ι 0 = A.one` pointwise: `ι_0` sends the graded unit to `1 ∈ A(U)`. -/
theorem sectionsGOne_app_of_one_comp (h1 : S.one ≫ ι 0 = A.one) (U : X.Opens) :
    (ι 0).app U (S.sectionsGOne U) = (1 : A.sectionsRing U) := by
  have h := congrArg (fun φ : 𝟙_ X.Modules ⟶ A.carrier => φ.app U (1 : Γ(X, U))) h1
  exact h

/-- `S.mul m n ≫ ι (m+n) = (ι m ⊗ₘ ι n) ≫ A.mul` pointwise: `ι` preserves the graded multiplication
(`Modules.tensorHom_tensorSections` + `QCAlgebra.sectionsMul_eq_mul_tensorSections`). -/
theorem sectionsGMul_app_of_mul_comp
    (h2 : ∀ m n, S.mul m n ≫ ι (m + n) = (ι m ⊗ₘ ι n) ≫ A.mul) (U : X.Opens) {m n : ℕ}
    (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    (ι (m + n)).app U (S.sectionsGMul U a b) =
      (show A.sectionsRing U from (ι m).app U a) * (show A.sectionsRing U from (ι n).app U b) := by
  have h := congrArg
    (fun φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) (S.part m) (S.part n) ⟶
        A.carrier =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b))
    (h2 m n)
  have hT := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (ι m) (ι n) U a b
  rw [A.sectionsMul_eq_mul_tensorSections]
  refine h.trans ?_
  show A.mul.app U ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) (ι m) (ι n)).val.app
    (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b)) = _
  rw [hT]
  rfl

/-- `ψ_U : ⨁_m Γ(U, S_m) →+* A(U)`, given on the `m`-th summand by `ι_m` on sections (`DirectSum.toSemiring`). -/
noncomputable def sectionsToRingHom (h1 : S.one ≫ ι 0 = A.one)
    (h2 : ∀ m n, S.mul m n ≫ ι (m + n) = (ι m ⊗ₘ ι n) ≫ A.mul) (U : X.Opens) :
    S.sectionsRing U →+* A.sectionsRing U :=
  DirectSum.toSemiring (fun m => (((ι m).app U).hom : S.sectionsPiece U m →+ A.sectionsRing U))
    (S.sectionsGOne_app_of_one_comp A ι h1 U)
    (fun a b => S.sectionsGMul_app_of_mul_comp A ι h2 U a b)

/-- `ψ_U` on the `m`-th summand is `ι_m` on sections. -/
theorem sectionsToRingHom_of (h1 : S.one ≫ ι 0 = A.one)
    (h2 : ∀ m n, S.mul m n ≫ ι (m + n) = (ι m ⊗ₘ ι n) ≫ A.mul) (U : X.Opens) (m : ℕ)
    (a : S.sectionsPiece U m) :
    S.sectionsToRingHom A ι h1 h2 U (DirectSum.of (S.sectionsPiece U) m a) = (ι m).app U a :=
  DirectSum.toSemiring_of _ _ _ m a

/-- `ψ` is compatible with restriction: `ψ_U ∘ S.sectionsRestrict = A.sectionsRestrict ∘ ψ_{U'}` (both sides
are additive homomorphisms; compare on `DirectSum.of`, which reduces to the naturality
`PresheafOfModules.naturality_apply` of `ι_m`). -/
theorem sectionsToRingHom_restrict (h1 : S.one ≫ ι 0 = A.one)
    (h2 : ∀ m n, S.mul m n ≫ ι (m + n) = (ι m ⊗ₘ ι n) ≫ A.mul) {U U' : X.Opens} (h : U ≤ U')
    (x : S.sectionsRing U') :
    S.sectionsToRingHom A ι h1 h2 U (S.sectionsRestrict h x) =
      A.sectionsRestrict h (S.sectionsToRingHom A ι h1 h2 U' x) := by
  have key : (S.sectionsToRingHom A ι h1 h2 U).toAddMonoidHom.comp
        (S.sectionsRestrictRingHom h).toAddMonoidHom =
      (A.sectionsRestrict h).toAddMonoidHom.comp (S.sectionsToRingHom A ι h1 h2 U').toAddMonoidHom := by
    refine DirectSum.addHom_ext ?_
    intro m a
    show S.sectionsToRingHom A ι h1 h2 U (S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece U') m a)) =
      A.sectionsRestrict h (S.sectionsToRingHom A ι h1 h2 U' (DirectSum.of (S.sectionsPiece U') m a))
    rw [S.sectionsRestrictRingHom_of, S.sectionsToRingHom_of, S.sectionsToRingHom_of]
    exact _root_.PresheafOfModules.naturality_apply (ι m).val (CategoryTheory.homOfLE h).op a
  exact DFunLike.congr_fun key x

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
