import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOps
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # Comparison of the two dual sheaves

The isomorphism `dualSheafIsoOld : dualSheaf M ≅ moduleSheafDual M` between the unsheafified dual
and the sheafified one (at the level of module sheaves, not only of sections), and the resulting
instance `(moduleSheafDual M).IsLineBundle`.

Design: `ModuleDualSectionEquiv.unitIso` only gives a **presheaf** isomorphism (the sheafification
unit is invertible because the dual presheaf is already a sheaf); downstream one needs an
isomorphism in `X.Modules` to transfer `IsLineBundle.of_iso` and the like. The right adjoint
(`forget ⋙ restrictScalars 𝟙`) of the sheafification adjunction
`PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)` is fully faithful (the counit is
invertible); it sends `dualSheaf M` to `moduleDualPresheaf M` (`rfl`) and `moduleSheafDual M` to the
target of `unitIso` (`rfl`), so the preimage of `unitIso` is the required isomorphism. This connects
the line-bundle property on both sides: `dualSheaf` (used for `O_X(D)`) and `moduleSheafDual`
(`= Scheme.Modules.dual = Scheme.Modules.internalHom · O_X`, also used for the negative powers of
`zpow`); the dual half of Stacks 01CT (`IsLineBundle.dual`) follows from the instance here.

Reference: Mathlib `PresheafOfModules.sheafificationAdjunction`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The right adjoint (`forget ⋙ restrictScalars 𝟙`) of the sheafification adjunction is fully faithful. -/
def sheafificationRightFullyFaithful (X : Scheme.{u}) :
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).FullyFaithful :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).fullyFaithfulROfIsIsoCounit

/-- The isomorphism between the unsheafified dual sheaf and the sheafified one. -/
def dualSheafIsoOld (M : X.Modules) : dualSheaf M ≅ AlgebraicGeometry.Scheme.Modules.moduleSheafDual M :=
  (sheafificationRightFullyFaithful X).preimageIso
    (MiyaokaMori.ModuleDualSectionEquiv.unitIso M)

/-- The isomorphism between the unsheafified dual sheaf and the internal Hom `𝓗om(M, O_X)`.
`moduleSheafDual M` and `internalHom M O_X` are the **same** sheafification
(`moduleDualPresheaf M = internalHomPresheaf M O_X` is `rfl`), so this is the previous isomorphism;
it is stated separately because that definitional equality check is expensive (about 20 s) and
should be paid only once. -/
def dualSheafIsoInternalHom (M : X.Modules) :
    dualSheaf M ≅ Modules.internalHom M (SheafOfModules.unit X.ringCatSheaf) :=
  dualSheafIsoOld M

/-- Taking the dual once more: `(dualSheaf M)^∨ ≅ (M^∨)^∨` (the dual functor applied to
`dualSheafIsoOld`). Since `O_X(D)` is `dualSheaf I_D`, places that write `Modules.dual O_X(D)`
(`EffectiveCartierRestrictionSequence`) need this to connect the two spellings
(`Scheme.Modules.dual` unfolds to `moduleSheafDual`, which is used directly here). -/
def dualDualSheafIsoOld (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleSheafDual (dualSheaf M) ≅
      AlgebraicGeometry.Scheme.Modules.moduleSheafDual (AlgebraicGeometry.Scheme.Modules.moduleSheafDual M) :=
  AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (dualSheafIsoOld M).symm

/-- The sheafified dual of a line bundle is a line bundle (the dual half of Stacks 01CT). -/
instance moduleSheafDual_isLineBundle (M : X.Modules) [M.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.moduleSheafDual M).IsLineBundle :=
  IsLineBundle.of_iso (dualSheafIsoOld M)

end AlgebraicGeometry.Scheme.Modules

end
