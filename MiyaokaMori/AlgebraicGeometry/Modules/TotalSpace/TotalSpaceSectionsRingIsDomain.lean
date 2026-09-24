import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomial

/-! # The section ring of `Sym(V^∨)` on a trivializing affine open is a domain

Statement: `X` integral, `V` locally free of finite type, `U ⊆ X` a nonempty affine open contained in some
trivializing open (the `X i` of `Modules.locallyFreeData V`); then the section ring `A(U) := Γ(U, Sym(V^∨))` of
`Sym(V^∨)` over `U` is a domain.

This is the ring-level input of `totalSpace_isIntegral` (`Tot(V)` integral): `Tot(V) = Spec_X Sym(V^∨)` lies over `U`
as `Spec A(U)` (`affineIso` of the relative Spec), and the gluing part (reduced + irreducible ⇒ integral) is in
`TotalSpaceIsIntegral`.

Reference: the algebraic side of "the total space of a vector bundle is locally `A^r_W`" (near Stacks 01M2):
`Γ(U, Sym(V^∨)) = O(U)[t_1,…,t_r]`.

Assembled from `totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial` (`TotalSpaceSectionsRingEquivMvPolynomial`):
`A(U) ≃+* MvPolynomial I Γ(X,U)`, `Γ(X,U)` is a domain (`X` integral, `U` nonempty), polynomial rings over domains are
domains, transport along the ring isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A trivialisation `p : free I ≅ M|_U` (an iso in `SheafOfModules (X.ringCatSheaf.over U)`) transported to the
pullback form `(pullback U.ι).obj M ≅ free I` on the scheme `U`. This replays the `IsIso` half of the private
`localTriv.transport` of `LocalTrivializationPullback`: the equivalence
`F := (overEquiv U).functor` preserves the coproduct `free I` (`SheafOfModules.mapFreeIso`, with the unit
identified by `restrictUnitIso` and `overFunctorEquiv`), and `F.obj (M.over U) ≅ (restrictFunctor U.ι).obj M ≅
(pullback U.ι).obj M` (`overFunctorEquiv`, `restrictFunctorIsoPullback`). -/
private theorem AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_isIso_over
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u)
    (p : SheafOfModules.free I ⟶ M.over U) [IsIso p] :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  let F : SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor
  have : F.IsEquivalence :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.IsEquivalence
  have : PreservesColimitsOfShape (Discrete I) F :=
    (F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}).preservesColimitsOfShape
  let e1 : F.obj (M.over U) ≅ (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj M :=
    (AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M
  let e2 := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app
        (SheafOfModules.unit X.ringCatSheaf)).symm
  let e3 := SheafOfModules.mapFreeIso F I η
  exact ⟨(e3 ≪≫ F.mapIso (asIso p) ≪≫ e1 ≪≫ e2).symm⟩

/-- **The section ring of `Sym(V^∨)` on a trivializing affine open is a domain.**

Let `X` be integral, `V` locally free of finite type, `q := Modules.locallyFreeData V` the local freeness data
extracted from `IsLocallyFree` (`SheafOfModules.LocalGeneratorsData`: the opens `q.X i` cover `X`, and
`(q.generators i).π : free((q.generators i).I) ⟶ V.over (q.X i)` is an isomorphism, `locallyFreeData_isLocallyFreeData`),
and `U` a **nonempty** affine open contained in some `q.X i`. Then `A(U) := (symGradedAlgebra (dual V)).total.sectionsRing U`
is a domain.

Proof sketch (the algebraic side of "the total space of a vector bundle is locally `A^r_W`", near Stacks 01M2). Write
`W := V^∨ = Modules.dual V`, `R := Γ(X, U)`, `I := (q.generators i).I`.
1. **`W|_U` is free**: `V|_{q.X i} ≅ free(I)|_{q.X i}` (`π` is an isomorphism) restricts along `U ≤ q.X i` to
   `V|_U ≅ free(I)|_U`; the dual preserves isomorphisms and commutes with restriction, and the dual of `free(I)` is
   `free(I)` (`DualFreeSheafFree.dualSheafFreeIso`, `I` finite by `IsFiniteType`; dual basis = the coordinate projections
   of `dualBasisHom`), so `W|_U ≅ free(I)|_U` and the `R`-module `Γ(U, W)` has the basis `(e_j^∨)_{j ∈ I}`.
2. **`A(U)` is the symmetric algebra of `Γ(U, W)`**: `W` is quasi-coherent (locally free ⇒ quasi-coherent), so
   `symGradedAlgebra W` is in the `symGradedAlgebraOfQC` branch (`part m = symPow W m`, the coequalizer `symPowπ` of the
   transpositions on `W^{⊗m}`; `total.carrier = ⊕_m symPow W m`; multiplication `symPowMul`). On the affine open `U`,
   sections of tensor products and quotients of quasi-coherent sheaves are tensor products and quotients of the section
   modules (Stacks 01CE/01ID), and sections of a direct sum over the quasi-compact `U` are the direct sum of the sections,
   so `Γ(U, Sym^m W) ≅ Sym^m_R Γ(U, W)`, `A(U) ≅ ⊕_m Sym^m_R Γ(U,W)`, with `sectionsMul` the multiplication of the
   symmetric algebra and `sectionsUnit` the structure map `R → A(U)`. In Mathlib's language: the `R`-linear map
   `ι := Γ(U, symGen W)` followed by the degree-one inclusion, `Γ(U, W) →ₗ[R] A(U)`, satisfies `IsSymmetricAlgebra ι`.
3. **Polynomial ring**: by 1, 2 and `IsSymmetricAlgebra.mvPolynomial` / `SymmetricAlgebra.equivMvPolynomial`,
   `A(U) ≃ₐ[R] MvPolynomial I R`.
4. **Domain**: `U` nonempty and `X` integral ⇒ `R` is a domain (`IsIntegral.component_integral`); `MvPolynomial I R` is a
   domain (`MvPolynomial.instIsDomain`); transport along the ring isomorphism of step 3 (`MulEquiv.isDomain`).

Steps 1–3 are exactly `totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial` (given a trivialization `e : V|_U ≅ free I`,
`∃ φ : A(U) ≃+* MvPolynomial I Γ(X,U)`), which this proof uses; it only (i) transports the trivialization
`(q.generators i).π` of `locallyFreeData V` on `q.X i` (`IsLocallyFreeData.isIso`) to the pullback form
`(pullback (q.X i).ι).obj V ≅ free I` (`pullback_iso_free_of_isIso_over`) and shrinks it along `U ≤ q.X i`
(`pullback_iso_free_of_le`), and (ii) performs step 4 (`IsIntegral.component_integral`, `MvPolynomial.instIsDomain`,
`MulEquiv.isDomain`).
The statement does not need `IsFiniteType` (polynomial rings in any number of variables over a domain are domains); the
instance is kept because `totalSpace` requires it. Edge cases: `U` nonempty is necessary (for `U = ∅`, `A(U) = 0` is not
a domain), hence the instance hypothesis `[Nonempty U.1]`; the trivial branch of `Sym` (`W` not quasi-coherent) does
not occur (`W` locally free ⇒ quasi-coherent). -/
theorem AlgebraicGeometry.Scheme.totalSpace_sectionsRing_isDomain_of_le_locallyFreeData
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (U : X.affineOpens) [Nonempty U.1]
    (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).I)
    (hU : U.1 ≤ (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i) :
    IsDomain ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsRing U.1) := by
  classical
  have : IsIso ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).generators i).π :=
    (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData V).isIso i
  -- the trivialisation of `V` on the chart `q.X i`, in pullback form
  obtain ⟨e₀⟩ := AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_isIso_over V
    ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i)
    ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).generators i).I
    ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).generators i).π
  -- shrink it to `U ≤ q.X i`
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le V hU _ e₀
  -- `A(U) ≃+* Γ(X, U)[x_j : j ∈ I]`
  obtain ⟨φ, -⟩ :=
    AlgebraicGeometry.Scheme.totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial V U _ e
  -- `Γ(X, U)` is a domain (X integral, U nonempty), hence so is the polynomial ring, hence `A(U)`
  have : IsDomain Γ(X, U.1) := AlgebraicGeometry.IsIntegral.component_integral U.1
  exact φ.toMulEquiv.isDomain _

end
