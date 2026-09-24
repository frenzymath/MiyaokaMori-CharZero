import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks01xkHPrimeExt
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkSectionsLocalization
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.ExtZeroSections

/-! # Degree-`0` base case of the Mayer–Vietoris induction for Stacks 01XJ/01XK

**Degree-0 base case of the Mayer–Vietoris induction in Stacks 01XJ/01XK**: for a quasi-coherent
`M` on `X`, an affine open `V`, `r ∈ Γ(X, O_X)` and `W = V ∩ D(r) = X.basicOpen (r|_V)`, the
restriction `H'⁰(V, M) → H'⁰(W, M)` (Mathlib `Sheaf.H'` in degree `0`, in `Ext` form with the
`Γ(X, ⊤)`-action of `smulEndAction`) is a localization of `Γ(X, ⊤)`-modules at the powers of `r`.

**Proof (natural language, self-contained).**
1. *Degree-0 cohomology is sections.* For every open `U`, `Ext(ℤ[h_U]^#, F, 0) ≃ Hom(ℤ[h_U]^#, F)`
   (`Ext.addEquiv₀`), and `Hom(ℤ[h_U]^#, F) ≃ F(U)` (`Stacks09sxAux.sectionsEquiv`, the composite
   of the sheafification adjunction, the free–forgetful adjunction and Yoneda). Concretely the
   composite sends `x` to `(addEquiv₀ x).val.app (op U) (η_U)`, where
   `η_U = toSheafify.app (op U) (FreeAbelianGroup.of (𝟙 U))` is the canonical generator; in this form
   the map is visibly additive. It is natural in `U`: for `W ≤ U`, `x ↦ (mk₀ ℤ[W → U]).comp x`
   corresponds to the restriction `F(U) → F(W)` (naturality of `toSheafify` and of `x.val`), and it
   is `Γ(X, ⊤)`-linear: `r • x = x.comp (mk₀ (M.smulEnd r))` corresponds to
   `(M.smulEnd r).val.app (op U) = (r|_U) • -` (`smulEnd_app`), which is the `Γ(X, ⊤)`-action of
   `M.sectionsOverTop U`. Hence `Ext(ℤ[h_U]^#, F, 0) ≃ₗ[Γ(X,⊤)] M.sectionsOverTop U`, compatibly
   with restriction.
2. *Sections localize.* For `V` affine and `W = X.basicOpen (r|_V)`, the restriction
   `Γ(M, V) → Γ(M, W)` is the localization at the powers of `r`
   (`isLocalizedModule_sectionsOverTopRestrict_basicOpen` with `A = Γ(X, ⊤)`, `a = id`; from Stacks 01P7).
3. Transport 2 along the linear equivalences of 1 (`IsLocalizedModule.of_linearEquiv`,
   `IsLocalizedModule.of_linearEquiv_right`).

Step 1 is `Stacks09sxAux.ext₀SectionsAddEquiv` with its naturality lemmas (`ExtZeroSections.lean`); the
`Γ(X, ⊤)`-linear version is `eZeroLinearEquiv` below.

Source: Stacks 01XJ proof paragraph 1 (the case of an affine); Stacks 01P7; Mathlib `Ext.addEquiv₀`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

attribute [local instance] smulEndAction ExtAction.module

attribute [local instance] Stacks09sxAux.ExtAction.sectionsModule

/-- Sections of a quasi-coherent module over an affine open localize along a basic open
(Stacks 01P7, `isLocalizedModule_sectionsOverTopRestrict_basicOpen`), stated for the restriction
`sectionsRes` of the abelian sheaf underlying `M` with the `Γ(X, ⊤)`-action of `smulEndAction`
(the two module structures and the two maps are definitionally equal). -/
theorem isLocalizedModule_sectionsRes_of_basicOpen [M.IsQuasicoherent] (r : Γ(X, ⊤))
    {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : W = X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r)) (hle : W ≤ V) :
    IsLocalizedModule (Submonoid.powers r)
      (Stacks09sxAux.sectionsRes Γ(X, ⊤) M.toAddCommGrpSheaf (homOfLE hle)) :=
  isLocalizedModule_sectionsOverTopRestrict_basicOpen M (RingHom.id Γ(X, ⊤)) r hV hW hle

/-- **Degree-0 base case**: for `V` affine and `W = V ∩ D(r)`, the restriction
`H'⁰(V, M) → H'⁰(W, M)` is the localization at the powers of `r` (as `Γ(X, ⊤)`-modules).
Proof: degree-0 cohomology is sections (`ExtZeroSections.lean`), and sections of a
quasi-coherent module over an affine localize along basic opens (Stacks 01P7). -/
theorem isLocalizedModule_precompLinear_zero_of_isAffineOpen [M.IsQuasicoherent] (r : Γ(X, ⊤))
    {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : W = X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r)) (hle : W ≤ V) :
    IsLocalizedModule (Submonoid.powers r)
      (precompLinear Γ(X, ⊤) M.toAddCommGrpSheaf ((freeSheafFunctor X).map (homOfLE hle)) 0) :=
  Stacks09sxAux.isLocalizedModule_precompLinear_zero_of_sections Γ(X, ⊤) M.toAddCommGrpSheaf
    (Submonoid.powers r) (homOfLE hle) (isLocalizedModule_sectionsRes_of_basicOpen M r hV hW hle)

end AlgebraicGeometry.Scheme.Modules

end
