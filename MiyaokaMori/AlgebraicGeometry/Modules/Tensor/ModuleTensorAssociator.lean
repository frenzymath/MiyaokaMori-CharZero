import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowers
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorSheafificationComparison

/-!
# Associativity of the original tensor sheaf

Both nested tensor sheaves are compared with the sheafification of a common
triple tensor presheaf. The comparison on the left uses the actual tensor of
the sheafification unit, followed by its identity scalar-restriction transport.
Braiding gives the corresponding comparison on the right. Their inverses and
the sectionwise presheaf associator produce the required sheaf isomorphism.

The section formulas concern the specified nested tensor sections. The inverse
identities hold on all sections because the maps are isomorphisms; no generation
by globally pure tensor sections is assumed. All modules and opens are arbitrary.

Sources: Stacks Project, `modules.tex`, `section-tensor-product` and
`lemma-tensor-product-sheafification`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

-- Bridge instance: `X.PresheafOfModules` unfolds to `PresheafOfModules X.ringCatSheaf.obj`, where
-- `Scheme.ringCatSheaf` goes through the non-reducible `sheafCompose`; instance search at reducible
-- transparency cannot see through it, so `MonoidalCategory X.PresheafOfModules` is never found. The
-- same Mathlib instance is registered again with `R` filled in as `X.presheaf` — not a new definition.
-- The name carries a file-specific suffix: a `local instance` is local only as an **attribute**, the
-- name is still global.
local instance schemePresheafOfModulesMonoidalStructForAssociator (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)

local instance schemePresheafOfModulesMonoidalForAssociator (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance schemePresheafOfModulesSymmetricForAssociator (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

namespace ModuleTensorAssociator

/-- Identify identity-restricted scalars with the original module presheaf. -/
def identityScalarIso (P : X.PresheafOfModules) :
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P ≅ P :=
  -- The dot notation `(𝟙 X.ringCatSheaf.obj).app U` does not elaborate (the type of `𝟙 …` stops at
  -- `CategoryStruct.toQuiver.1 …`, not a constant head); write `NatTrans.app (𝟙 …) U` instead.
  { hom :=
      { app := fun U ↦
          (ModuleCat.restrictScalarsId'App
            (NatTrans.app (𝟙 X.ringCatSheaf.obj) U).hom rfl (P.obj U)).hom
        naturality := by
          intro U V i
          ext x
          rfl }
    inv :=
      { app := fun U ↦
          (ModuleCat.restrictScalarsId'App
            (NatTrans.app (𝟙 X.ringCatSheaf.obj) U).hom rfl (P.obj U)).inv
        naturality := by
          intro U V i
          ext x
          rfl }
    hom_inv_id := by
      -- `ext U x` would go all the way down to elements and destroy the shape of `Iso.hom_inv_id`;
      -- stop at `hom_ext` and use the isomorphism's own `hom_inv_id`.
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.restrictScalarsId'App
        (NatTrans.app (𝟙 X.ringCatSheaf.obj) U).hom rfl (P.obj U)).hom_inv_id
    inv_hom_id := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.restrictScalarsId'App
        (NatTrans.app (𝟙 X.ringCatSheaf.obj) U).hom rfl (P.obj U)).inv_hom_id }

/-- Sheafifying the first factor gives an isomorphism after tensor sheafification.
The second factor is arbitrary; the original unit's scalar transport is explicit. -/
def leftUnitIso (P Q : X.PresheafOfModules) :
    moduleSheafification X (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) ≅
      moduleSheafification X (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleSheafification X P).val Q) := by
  letI := moduleSheafification_tensor_unit_isIso P Q
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 Q))) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.tensorIso (identityScalarIso (moduleSheafification X P).val)
        (Iso.refl Q))

/-- The left comparison sends the original tensor generator through the original unit. -/
theorem leftUnitIso_section (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (leftUnitIso P Q).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
          (p ⊗ₜ[Γ(X, U)] q)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (moduleSheafification X P).val Q) U
        (moduleSheafificationUnit X P U p ⊗ₜ[Γ(X, U)] q) := by
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (MonoidalCategory.tensorIso (identityScalarIso (moduleSheafification X P).val)
        (Iso.refl Q)).hom).val.app (op U)
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P) (𝟙 Q))).val.app (op U) _) = _
  erw [moduleSheafificationUnit_naturality, moduleSheafificationUnit_naturality]
  rfl

/-- The inverse left comparison recovers the specified original tensor generator. -/
theorem leftUnitIso_inv_section (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (leftUnitIso P Q).inv.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleSheafification X P).val Q) U
          (moduleSheafificationUnit X P U p ⊗ₜ[Γ(X, U)] q)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
        (p ⊗ₜ[Γ(X, U)] q) := by
  have h := congrArg
    (fun f ↦ f.app U
      (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
        (p ⊗ₜ[Γ(X, U)] q))) (leftUnitIso P Q).hom_inv_id
  change (leftUnitIso P Q).inv.app U
      ((leftUnitIso P Q).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
          (p ⊗ₜ[Γ(X, U)] q))) = _ at h
  rw [leftUnitIso_section P Q U p q] at h
  exact h

/-- Sheafifying the second factor is obtained by braiding the actual left comparison. -/
def rightUnitIso (P Q : X.PresheafOfModules) :
    moduleSheafification X (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) ≅
      moduleSheafification X (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        P (moduleSheafification X Q).val) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (BraidedCategory.braiding (C := X.PresheafOfModules) P Q) ≪≫
    leftUnitIso Q P ≪≫
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
        (BraidedCategory.braiding (C := X.PresheafOfModules)
          P (moduleSheafification X Q).val)).symm

/-- The right comparison sends precisely the second original factor through the unit. -/
theorem rightUnitIso_section (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (rightUnitIso P Q).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
          (p ⊗ₜ[Γ(X, U)] q)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          P (moduleSheafification X Q).val) U
        (p ⊗ₜ[Γ(X, U)] moduleSheafificationUnit X Q U q) := by
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (BraidedCategory.braiding (C := X.PresheafOfModules)
        P (moduleSheafification X Q).val).inv).val.app (op U)
      ((leftUnitIso Q P).hom.app U
        (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (BraidedCategory.braiding (C := X.PresheafOfModules) P Q).hom).val.app (op U) _)) = _
  erw [moduleSheafificationUnit_naturality]
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (BraidedCategory.braiding (C := X.PresheafOfModules)
        P (moduleSheafification X Q).val).inv).val.app (op U)
      ((leftUnitIso Q P).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) Q P) U
          (q ⊗ₜ[Γ(X, U)] p))) = _
  rw [leftUnitIso_section]
  erw [moduleSheafificationUnit_naturality]
  rfl

/-- The sheafified presheaf associator acts on the specified triple tensor generator. -/
theorem presheafAssoc_section (P Q R : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) (r : R.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
        (MonoidalCategory.associator (C := X.PresheafOfModules) P Q R)).hom.val.app (op U)
      (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) R) U
        ((p ⊗ₜ[Γ(X, U)] q) ⊗ₜ[Γ(X, U)] r)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) Q R)) U
        (p ⊗ₜ[Γ(X, U)] (q ⊗ₜ[Γ(X, U)] r)) := by
  exact moduleSheafificationUnit_naturality X
    (MonoidalCategory.associator (C := X.PresheafOfModules) P Q R).hom U
    ((p ⊗ₜ[Γ(X, U)] q) ⊗ₜ[Γ(X, U)] r)

end ModuleTensorAssociator

/-- Reassociate the original sheafified tensor products of three arbitrary module sheaves. -/
def moduleTensorAssociator (L M N : X.Modules) :
    moduleTensor (moduleTensor L M) N ≅ moduleTensor L (moduleTensor M N) :=
  (ModuleTensorAssociator.leftUnitIso (moduleTensorPresheaf L M) N.val).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.associator (C := X.PresheafOfModules) L.val M.val N.val) ≪≫
    ModuleTensorAssociator.rightUnitIso L.val (moduleTensorPresheaf M N)

/-- The associator preserves all three specified factors of an original tensor section. -/
@[simp]
theorem moduleTensorAssociator_hom_section {L M N : X.Modules} {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) (r : Γ(N, U)) :
    (moduleTensorAssociator L M N).hom.app U
        (moduleTensorSection (moduleTensorSection s t) r) =
      moduleTensorSection s (moduleTensorSection t r) := by
  change (ModuleTensorAssociator.rightUnitIso L.val (moduleTensorPresheaf M N)).hom.app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
        (MonoidalCategory.associator (C := X.PresheafOfModules) L.val M.val N.val)).hom.val.app (op U)
        ((ModuleTensorAssociator.leftUnitIso (moduleTensorPresheaf L M) N.val).inv.app U
          (moduleSheafificationUnit X
            (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
              (moduleSheafification X (moduleTensorPresheaf L M)).val N.val) U
            (moduleSheafificationUnit X (moduleTensorPresheaf L M) U
              (s ⊗ₜ[Γ(X, U)] t) ⊗ₜ[Γ(X, U)] r)))) = _
  rw [ModuleTensorAssociator.leftUnitIso_inv_section]
  -- The pattern of `presheafAssoc_section` is `tensorObj (tensorObj ?P ?Q) ?R`, but the goal has
  -- `tensorObj (moduleTensorPresheaf L M) N.val` (a plain `def`, which `kabstract` does not see
  -- through); unfold it first, then `rw`.
  simp only [moduleTensorPresheaf]
  rw [ModuleTensorAssociator.presheafAssoc_section]
  rw [ModuleTensorAssociator.rightUnitIso_section]
  rfl

/-- The inverse associator recovers the original left-bracketed tensor section. -/
@[simp]
theorem moduleTensorAssociator_inv_section {L M N : X.Modules} {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) (r : Γ(N, U)) :
    (moduleTensorAssociator L M N).inv.app U
        (moduleTensorSection s (moduleTensorSection t r)) =
      moduleTensorSection (moduleTensorSection s t) r := by
  have h := congrArg
    (fun f ↦ f.app U (moduleTensorSection (moduleTensorSection s t) r))
    (moduleTensorAssociator L M N).hom_inv_id
  change (moduleTensorAssociator L M N).inv.app U
      ((moduleTensorAssociator L M N).hom.app U
        (moduleTensorSection (moduleTensorSection s t) r)) = _ at h
  rw [moduleTensorAssociator_hom_section] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
