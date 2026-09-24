import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id

/-! # Quasi-coherent sheaves are closed under the monoidal structure and finite biproducts

Quasi-coherent `O_X`-modules are closed under the monoidal structure and finite biproducts (`⊗` and `⨁`
in the spelling of the monoidal structure / biproducts of `X.Modules`):
* `unit_isQuasicoherent`: `𝟙_ X.Modules = O_X` is quasi-coherent — `O_X ≅ free PUnit` (a coproduct over
  one point, `coproductUniqueIso`), free sheaves are locally free (Mathlib `Sheaf/LocallyFree.lean`),
  locally free ⇒ quasi-coherent (`isQuasicoherent_of_isLocallyFree`); `SheafOfModules.unit = 𝟙_` is
  `unit_eq_tensorUnit` (rfl).
* `tensorObj_isQuasicoherent`: Stacks 01CE (`isQuasicoherent_tensor`, for `Modules.tensor`), transported
  to the monoidal `⊗` along `tensorIsoTensorObj : Modules.tensor F G ≅ F ⊗ G`.
* `isQuasicoherent_biproduct_of_fintype`: a finite biproduct `⨁ M` (index `J : Type`) is quasi-coherent,
  reduced to `isQuasicoherent_colimit` (small colimits preserve quasi-coherence, Stacks 01LA;
  `Stacks01ce01id`): `⨁ M ≅ ∐ M ≅ ∐ (M ∘ ULift.down) = colimit (Discrete.functor _)`
  (`biproduct.isoCoproduct`, `Sigma.whiskerEquiv`, the latter only to lift the index to `Type u`).

Source: Stacks 01BE (definition), 01CE (tensor product), 01LA (colimits).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `𝟙_ X.Modules = O_X` is quasi-coherent. -/
theorem unit_isQuasicoherent (X : AlgebraicGeometry.Scheme.{u}) : (𝟙_ X.Modules).IsQuasicoherent := by
  have h : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u+1}).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  have e : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u+1} : X.Modules) ≅ 𝟙_ X.Modules :=
    coproductUniqueIso _ ≪≫ eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e h

/-- The tensor product (monoidal `⊗`) preserves quasi-coherence (Stacks 01CE). -/
theorem tensorObj_isQuasicoherent (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (F ⊗ G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G)
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor F G)

/-- Finite biproducts preserve quasi-coherence (via `isQuasicoherent_colimit`, see the module docstring). -/
theorem isQuasicoherent_biproduct_of_fintype {J : Type} [Fintype J] (M : J → X.Modules)
    (hM : ∀ j, (M j).IsQuasicoherent) : (⨁ M).IsQuasicoherent := by
  let F : Discrete (ULift.{u} J) ⥤ X.Modules := Discrete.functor (fun j => M j.down)
  have h : (colimit F).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_colimit F (fun j => hM j.as.down)
  have e : ⨁ M ≅ colimit F :=
    biproduct.isoCoproduct M ≪≫
      Sigma.whiskerEquiv (f := M) (g := fun k : ULift.{u} J => M k.down) Equiv.ulift.symm
        (fun j => Iso.refl _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm h

end AlgebraicGeometry.Scheme.Modules
