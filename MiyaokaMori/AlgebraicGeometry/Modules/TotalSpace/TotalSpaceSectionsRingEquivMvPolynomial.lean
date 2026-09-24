import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSectionsBasisOfTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # The section ring of `Sym(V^∨)` on a trivializing affine open is a polynomial ring

Statement: `V` a locally free sheaf of finite type on a scheme `X`, `U` an affine open on which `V` is
trivialised by `e : V|_U ≅ O_U^{⊕I}`. Then the section ring of `Sym(V^∨)` over `U`,
`A(U) := (symGradedAlgebra (dual V)).total.sectionsRing U = Γ(U, Sym(V^∨))`, is the polynomial ring
`Γ(X, U)[x_i : i ∈ I]`, by a ring isomorphism carrying the structure map `sectionsUnit U : Γ(X, U) → A(U)`
to the constants `MvPolynomial.C`.

This is the algebraic side of "the total space of a vector bundle is locally `A^r_U`" (Stacks 01M2 area;
Hartshorne II Ex. 5.18): `Tot(V) = Spec_X Sym(V^∨)` lies over `U` as `Spec A(U)` (`relativeSpec.affineIso`,
`AffineAlgebra.chart_isPullback`), so `A(U) ≅ Γ(U)[x_1, …, x_r]` says `Tot(V)|_U ≅ A^r_U`.

The consequence "A(U) is a domain when X is integral" is `totalSpace_sectionsRing_isDomain_of_le_locallyFreeData`
(by `MulEquiv.isDomain` with `MvPolynomial.instIsDomain` and the trivialisation `(q.generators i).π` of
`locallyFreeData V` restricted to `U`).

Step 1 of the proof is `exists_basis_dual_sections_of_pullback_iso_free` (`DualSectionsBasisOfTrivialization`) and
`finite_index_of_restrict_iso_free`; step 2 is `IsSymmetricAlgebra (symGenTotalLinearMap (dual V) U)`, from
`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`
(`TotalSpaceSectionsRingEquivMvPolynomialSymSectionsInjective`); step 3 is Mathlib's `SymmetricAlgebra.equivMvPolynomial`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Section ring of `Sym(V^∨)` on a trivialising affine open is a polynomial ring.**

Notation: `W := V^∨ = Modules.dual V`, `R := Γ(X, U)`, `A(U) := (symGradedAlgebra W).total.sectionsRing U`
(= `Γ(U, ⨁_m Sym^m W)` with the ring structure `sectionsMul` / `sectionsUnit` of `QcAlgebraSectionsRing`).

Proof (Bourbaki Algebra III §6 no. 6 Thm 1, Stacks 01CG/01I8).
1. **`W|_U` is free with basis indexed by `I`.** `e : V|_U ≅ free I`. Dualising, `W|_U = (V|_U)^∨ ≅ (free I)^∨`
   (the dual commutes with restriction to opens: `ModulesDualMap` / `DualPullbackCommute`; the dual of an iso is an
   iso), and `(free I)^∨ ≅ free I` for finite `I` (`DualFreeSheafFree.dualSheafFreeIso` / `dual_free_iso`;
   dual basis `e_i^∨ =` the `i`-th coordinate projection). `I` is finite whenever `U ≠ ∅`
   (`finite_index_of_restrict_iso_free`, from `IsFiniteType`); when `U = ∅` all rings below are the zero ring and
   the statement is trivial (`MvPolynomial I 0 = 0`, `Subsingleton` ring equiv). Hence the `R`-module
   `Γ(U, W)` is free with basis `(e_i^∨)_{i ∈ I}` (`Module.Basis`).
2. **`A(U)` is the symmetric algebra of the `R`-module `Γ(U, W)`.** `W` is quasi-coherent (locally free ⇒ qc,
   `isQuasicoherent_of_isLocallyFree`, `SheafDualLocallyFree`), so `symGradedAlgebra W` is in the
   `symGradedAlgebraOfQC` branch (`symGradedAlgebra_of_isQuasicoherent`, `dif_pos`): `part m = symPow W m`,
   the coequaliser of the adjacent transpositions of `W^{⊗m}` with quotient map `symPowπ W m`, multiplication
   `symPowMul`, unit `symPowπ W 0`; `total.carrier = ⨁_m symPow W m` (`GradedQCAlgebra.total`,
   `total_isQuasicoherent`). On the affine open `U`:
   (a) sections of a coproduct of qc sheaves over the quasi-compact `U` are the direct sum of the sections
       (`biproduct_section_eq_sum`-type statements, `GradedAlgebraTotalProjection`), so
       `A(U) = ⨁_m Γ(U, symPow W m)` as an `R`-module, and `sectionsMul` is the componentwise product given by
       `Γ(U, symPowMul)` (`total_mul_component`, `GradedAlgebraTotalComponent`);
   (b) for qc `F, G` on affine `U`, `Γ(U, F ⊗ G) = Γ(U, F) ⊗_R Γ(U, G)` and `Γ(U, coequaliser) = coequaliser of
       Γ(U, ·)` (Γ(U, ·) is exact on qc sheaves over affine `U`; Stacks 01I8, `Stacks01ce01id`,
       `Stacks01cmTensorHom` are the closest existing material), so `Γ(U, symPow W m) = Sym^m_R Γ(U, W)`
       (the `m`-th symmetric power of the module, as the quotient of `Γ(U,W)^{⊗m}` by the transpositions), and
       `Γ(U, symPowMul)` is the product of the symmetric algebra;
   (c) the structure map `sectionsUnit U : R → A(U)` is `r ↦ r · 1`, landing in degree `0 = Sym^0 = R`.
   In Mathlib's language: the `R`-linear map `ι : Γ(U, W) →ₗ[R] A(U)` (degree-one inclusion,
   `WeightedSymGenerator.symGen` followed by the coproduct inclusion; cf. `TotalSpaceLinearCoordinate.linearFunctionHom`)
   satisfies `IsSymmetricAlgebra ι` (Mathlib `Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`): every
   `R`-linear map `Γ(U, W) → B` into a commutative `R`-algebra extends uniquely to an `R`-algebra map `A(U) → B`
   (existence degreewise by the coequaliser universal property `symPowDesc`, uniqueness because `A(U)` is generated
   in degree one, `SymGradedAlgebraGeneratedInDegreeOne` / `SectionsRingGeneratedInDegreeOne`).
3. **Polynomial ring.** From 1 and 2, `IsSymmetricAlgebra.mvPolynomial` / `SymmetricAlgebra.equivMvPolynomial`
   (Mathlib) with the basis `(e_i^∨)` gives `A(U) ≃ₐ[R] MvPolynomial I R`; as an `R`-algebra map it sends
   `sectionsUnit U r = algebraMap R A(U) r` to `algebraMap R (MvPolynomial I R) r = MvPolynomial.C r`
   (`MvPolynomial.algebraMap_eq`). Take `φ` to be the underlying ring equivalence.

As formalized: step 1 is `exists_basis_dual_sections_of_pullback_iso_free` and `finite_index_of_restrict_iso_free`;
step 2 is `symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction` (surjectivity of `lift ι_U` from generation
in degree one on sections + finiteness of coproduct sections on a quasi-compact open — no `Γ(U, F ⊗ G)` or exactness
of `Γ(U, ·)` needed; injectivity from the algebra retraction); step 3 is Mathlib
(`IsSymmetricAlgebra.equiv`, `SymmetricAlgebra.equivMvPolynomial`, `AlgEquiv.commutes`).

Edge cases: `U = ∅` (all rings zero, statement trivially true); `I = ∅` (`Sym(0) = O_X`, `MvPolynomial ∅ R = R`,
fine); `I` infinite is impossible for nonempty `U` because `V` is of finite type, and harmless for `U = ∅`.
The statement needs `V` locally free (so that `V^∨` is quasi-coherent and `symGradedAlgebra` does not fall into
its trivial branch) but is true without `IsFiniteType`; the instance is kept because `totalSpace` requires it. -/
theorem AlgebraicGeometry.Scheme.totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (U : X.affineOpens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj V ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I) :
    ∃ φ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing U.1 ≃+*
        MvPolynomial I Γ(X, U.1),
      ∀ r : Γ(X, U.1), φ ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U.1 r) = MvPolynomial.C r := by
  classical
  obtain ⟨U, hUa⟩ := U
  let _ := ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U).toAlgebra
  by_cases hU : (U : Set X).Nonempty
  · -- nonempty `U`: `I` is finite, `Γ(U, V^∨)` is free on the dual basis, `A(U)` is its symmetric algebra
    obtain ⟨x, hx⟩ := hU
    have : Finite I :=
      AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free V U I e x hx
    have : (AlgebraicGeometry.Scheme.Modules.dual V).IsQuasicoherent :=
      have := AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
      AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
    have hS := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction
      (AlgebraicGeometry.Scheme.Modules.dual V) ⟨U, hUa⟩
    obtain ⟨b⟩ := AlgebraicGeometry.Scheme.Modules.exists_basis_dual_sections_of_pullback_iso_free V U I e
    let ψ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing U ≃ₐ[Γ(X, U)]
        MvPolynomial I Γ(X, U) :=
      hS.equiv.symm.trans (SymmetricAlgebra.equivMvPolynomial b)
    refine ⟨ψ.toRingEquiv, fun r => ?_⟩
    change ψ (algebraMap Γ(X, U) _ r) = _
    rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
  · -- empty `U`: every ring in sight is the zero ring
    have hbot : U = ⊥ := by
      ext1
      exact Set.not_nonempty_iff_eq_empty.mp hU
    subst hbot
    have : Subsingleton ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing ⊥) :=
      Module.subsingleton Γ(X, ⊥) _
    have : Subsingleton (MvPolynomial I Γ(X, ⊥)) :=
      ⟨fun p q => MvPolynomial.ext p q fun _ => Subsingleton.elim _ _⟩
    let _ : Unique ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing ⊥) :=
      @Unique.mk' _ ⟨0⟩ _
    let _ : Unique (MvPolynomial I Γ(X, ⊥)) := @Unique.mk' _ ⟨0⟩ _
    exact ⟨RingEquiv.ofUnique, fun _ => Subsingleton.elim _ _⟩

end
