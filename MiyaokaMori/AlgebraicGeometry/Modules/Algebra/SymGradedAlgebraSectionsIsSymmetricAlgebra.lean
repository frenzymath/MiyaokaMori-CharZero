import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective

/-! # The section ring of the symmetric algebra sheaf over an affine open is a symmetric algebra

The sections ring of the sheaf symmetric algebra over an affine open is the algebraic symmetric algebra
of the sections: for `W` quasi-coherent on `X` and `U ⊆ X` affine open, the degree-one inclusion
`ι_U : Γ(U, W) → A(U) := Γ(U, Sym(W))` (`symGen W ≫ totalIncl 1`, packaged as the `Γ(X, U)`-linear map
`symGenTotalLinearMap`) satisfies Mathlib's `IsSymmetricAlgebra ι_U`, i.e. the induced algebra map
`Sym_{Γ(X,U)}(Γ(U, W)) → A(U)` is bijective. Consequently, when `Γ(U, W)` is free with basis `b`,
`A(U) ≃ₐ Γ(X,U)[X_i]` with `ι_U (b i) ↦ X_i` (`SymmetricAlgebra.equivMvPolynomial`).

Source: Stacks 01CG/01I8 (Sym of a quasi-coherent module; sections over an affine open of tensor
products and quotients of quasi-coherent modules), Bourbaki Algebra III §6; the same fact underlies the
integrality of the section ring of the total space and the local model of the symmetric algebra sheaf.
Used through the bridge `totalSpace.isSymmetricAlgebra_linearFunctionLinearMap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For `W` quasi-coherent and `U` affine, the degree-one inclusion
`ι_U : Γ(U, W) → A(U) = Γ(U, Sym(W))` (`symGenTotalLinearMap`, `SymGenTotalLinearMap.lean`) makes `A(U)` the
symmetric algebra of the `Γ(X, U)`-module `Γ(U, W)`: `IsSymmetricAlgebra ι_U` (Mathlib: `SymmetricAlgebra.lift ι_U`
is bijective).

Source: Stacks 01CG (`Sym^n F` is the sheafification of `U ↦ Sym^n Γ(U, F)`; for `F` quasi-coherent and
`U` affine, `Γ(U, Sym^n F) = Sym^n Γ(U, F)`), Bourbaki Algebra III §6 no. 6.

Proof (assembly): `SymmetricAlgebra.lift ι_U` is
* surjective — `symGradedAlgebra_lift_symGenTotalLinearMap_surjective`
  (`Γ(U, ∐_m Sym^m W) = ⨁_m Γ(U, Sym^m W)` for the
  quasi-compact `U` (Stacks 01AI) and `Sym W` is generated in degree one on affine sections (Stacks 01N0,
  `GeneratedInDegreeOne.sectionsGrading_mem_closure`), degree `0`/`1` being `Γ(X, U)`/`Γ(U, W)` because
  `O_X → Sym^0 W` and `symGen : W → Sym^1 W` are isomorphisms);
* injective — `symGradedAlgebra_lift_symGenTotalLinearMap_injective`, from
  `symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap` (a `Γ(X, U)`-algebra retraction
  `A(U) → Sym_{Γ(X,U)} Γ(U, W)` of `ι_U`, built from the module map `W → g_* O_{Spec Sym}`).
Both halves are packaged as `symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`
(`TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective.lean`).

Edge cases: `U = ∅` — `R = 0`, both sides are the zero ring, `lift` is bijective; `W = 0` — `A(U) = R`,
`Sym_R 0 = R`; `W` not quasi-coherent is excluded by the hypothesis (the trivial branch of
`symGradedAlgebra` would make the statement false). -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_sectionsRing_isSymmetricAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules) [W.IsQuasicoherent] (U : X.affineOpens) :
    letI := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
    IsSymmetricAlgebra (AlgebraicGeometry.Scheme.Modules.symGenTotalLinearMap W U.1) :=
  AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction W U

end
