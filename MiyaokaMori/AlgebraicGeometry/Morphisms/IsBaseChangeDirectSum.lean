import MiyaokaMori.Prelude
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Base change commutes with finite direct sums

Two pure-algebra facts about `IsBaseChange` (Mathlib `RingTheory/IsTensorProduct.lean`) used to
package Stacks 01I9 (sections of a quasi-coherent module along a base change, piecewise) into the
hypothesis `IsBaseChange R' fR.toLinearMap` of Stacks 01N2 (`Proj.isPullback_of_isBaseChange`,
`Stacks01n2.lean`) for the section rings `⊕_m Γ(U, 𝒜_m)`:

* (a direct sum of base changes is a base change is already Mathlib's `IsBaseChange.directSum`,
  `RingTheory/TensorProduct/IsBaseChangePi.lean`, re-exported here by the import);
* `IsBaseChange.of_isIso_extendRestrictScalars_transpose`: if the adjoint transpose
  `S ⊗_R M → N` of an `R`-linear map `M → N` (an iso in `ModuleCat S`, the form in which
  `Modules.isIso_transpose_pullbackSectionsNative` states 01I9) is an isomorphism, then the map is a
  base change (with `Algebra R S := φ.toAlgebra`, `Module R N := Module.compHom N φ`).

Source: Mathlib (`IsBaseChange.of_equiv`, `TensorProduct.directSumRight`,
`ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars`); Stacks 01I9, 01N2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open TensorProduct
open scoped DirectSum

namespace IsBaseChange


section transpose

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- If the adjoint transpose `S ⊗[R] M ⟶ N` of `α : M ⟶ N` (restriction of scalars along `φ`)
is an isomorphism in `ModuleCat S`, then `α` is a base change along `φ`. Stated with
`Algebra R S := φ.toAlgebra` and `Module R N := Module.compHom N φ` (the module structure of
`ModuleCat.restrictScalars`), so that it applies verbatim to `isIso_transpose_pullbackSectionsNative`. -/
theorem of_isIso_extendRestrictScalars_transpose
    (α : ModuleCat.of R M ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of S N))
    [hα : IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α)]
    (f : letI : Module R N := Module.compHom N φ; M →ₗ[R] N) (hf : ∀ m, α.hom m = f m) :
    letI := φ.toAlgebra
    letI : Module R N := Module.compHom N φ
    letI : IsScalarTower R S N := ⟨fun r s n => by
      change (φ r * s) • n = φ r • s • n
      exact mul_smul _ _ _⟩
    IsBaseChange S f := by
  let _ := φ.toAlgebra
  let _ : Module R N := Module.compHom N φ
  let _ : IsScalarTower R S N := ⟨fun r s n => by
    change (φ r * s) • n = φ r • s • n
    exact mul_smul _ _ _⟩
  have hbij : Function.Bijective
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  -- `IsBaseChange S f` is bijectivity of `TensorProduct.lift (s ⊗ m ↦ s • f m)`, and the transpose
  -- is that map (`HomEquiv.fromExtendScalars`: `s ⊗ m ↦ s • α m`)
  show Function.Bijective (TensorProduct.lift _)
  have key : ∀ z, TensorProduct.lift
      (((Algebra.linearMap S (Module.End S (M →ₗ[R] N))).flip f).restrictScalars R) z =
        (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α).hom z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      exact (map_zero (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α).hom).symm
    | tmul s m =>
      show s • f m = s • α.hom m
      rw [hf]
      rfl
    | add x y hx hy =>
      rw [map_add, hx, hy]
      exact (map_add (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α).hom x y).symm
  have : ⇑(TensorProduct.lift
      (((Algebra.linearMap S (Module.End S (M →ₗ[R] N))).flip f).restrictScalars R)) =
        ⇑(((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm α).hom :=
    funext key
  rw [this]
  exact hbij

end transpose

end IsBaseChange
