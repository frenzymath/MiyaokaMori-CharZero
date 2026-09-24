import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfRestrictFreeCover

/-! # Locally free sheaves are quasi-coherent

A locally free `O_X`-module on a scheme `X` (Mathlib's site-theoretic `SheafOfModules.IsLocallyFree`,
of arbitrary rank) is quasi-coherent. Consequences: (a) if every point of `X` lies in the image of
some open immersion `g : Y ⟶ X` along which `M` restricts to a free sheaf `free ι`, then `M` is
quasi-coherent; (b) line bundles are quasi-coherent (a low-priority instance).

Proof sketch:
1. Mathlib's instance `SheafOfModules.instIsQuasicoherentOfIsLocallyFree` (end of
   `Sheaf/LocallyFree.lean`): local freeness data `q` gives `QuasicoherentData` "without relations"
   (same cover, generators of `q` on each piece, empty relation index; `π` is an isomorphism so the
   kernel is zero). Its site hypotheses `∀ U, HasSheafify (J.over U) AddCommGrpCat` and
   `∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat` are found by instance search on `Opens X`.
2. For `M : X.Modules`, `infer_instance` still fails (type class search at instances transparency does
   not match the spelling of the site instances implicit in `[M.IsLocallyFree]`), but **applying the
   instance explicitly** (`exact`, at default transparency) works.
3. (a) from `isLocallyFree_of_restrict_free` and step 1; (b) from `IsLineBundle.isLocallyFree` and
   step 1.

References: Stacks 01BE (quasi-coherent), 01C6 (locally free), 01CR (invertible sheaves); Mathlib
`Sheaf/LocallyFree.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Locally free (of any rank) ⇒ quasi-coherent. Apply Mathlib's instance explicitly;
`infer_instance` does not find it (see step 2 of the module docstring). -/
theorem isQuasicoherent_of_isLocallyFree (M : X.Modules) [M.IsLocallyFree] : M.IsQuasicoherent :=
  SheafOfModules.instIsQuasicoherentOfIsLocallyFree M

/-- Restricting to free sheaves along a family of open immersions covering `X` ⇒ quasi-coherent. -/
theorem isQuasicoherent_of_restrict_free (M : X.Modules)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (_ : IsOpenImmersion g) (ι : Type u),
      x ∈ Set.range g.base ∧ Nonempty (M.restrict g ≅ SheafOfModules.free (R := Y.ringCatSheaf) ι)) :
    M.IsQuasicoherent :=
  have := isLocallyFree_of_restrict_free M h
  isQuasicoherent_of_isLocallyFree M

/-- Line bundles are quasi-coherent (Stacks 01CR + 01BE). A low-priority instance: definitions such as
`symGradedAlgebra` that branch (`dite`) on `V.IsQuasicoherent` rely on it to take the true branch. -/
instance (priority := 100) IsLineBundle.isQuasicoherent (M : X.Modules) [M.IsLineBundle] :
    M.IsQuasicoherent :=
  isQuasicoherent_of_isLocallyFree M

end AlgebraicGeometry.Scheme.Modules
