import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowers

/-!
# Unit isomorphisms for the original tensor module

The left and right unit isomorphisms are obtained by sheafifying Mathlib's
presheaf unit isomorphisms and composing with the actual sheafification counit.
Compatibility with the original sheafification unit (`…_fac`) gives the scalar action
formulas on tensor sections; the inverse formulas insert the section `1` and follow from
`hom_inv_id`. Naturality is proved by injectivity of the sheafification adjunction's
`homEquiv`, which reduces it to Mathlib's presheaf-level unitor naturality.

These isomorphisms serve degree zero in the coefficient modules and the unit
of the truncated jet algebra of the paper. The tensor
object, structure module and sheafification adjunction are the existing ones.
No assertion that arbitrary tensor-sheaf sections are pure is used.

Source: Stacks Project, `modules.tex`, `section-tensor-product`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

-- Mathlib registers the monoidal structure only for `PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)`,
-- while `X.PresheafOfModules` unfolds to `PresheafOfModules X.ringCatSheaf.obj`, where
-- `Scheme.ringCatSheaf` goes through the non-reducible `sheafCompose`; instance search at reducible
-- transparency cannot see through it, so `MonoidalCategoryStruct X.PresheafOfModules` is never found.
-- Below, the same Mathlib instance is registered again with `R` filled in as `X.presheaf` — not a new
-- definition, only a hint for instance search. The name carries a file-specific suffix: a
-- `local instance` is local only as an **attribute**, the name is still global.
local instance schemePresheafOfModulesMonoidalStructForUnit (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)

local instance schemePresheafOfModulesMonoidalForUnit (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)


set_option backward.isDefEq.respectTransparency false in
/-- The original structure module is a left unit for the original sheafified tensor. -/
def moduleTensorLeftUnitIso (M : X.Modules) :
    moduleTensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.leftUnitor (C := X.PresheafOfModules) M.val) ≪≫
    -- Not `asIso (counit.app M)`: since `Scheme.Modules` is a plain `def`, its `Category` instance is
    -- not the same instance term as that of `SheafOfModules`, and instance search (at reducible
    -- transparency) does not find `IsIso (counit.app M)`. Taking the natural isomorphism first and then
    -- its component is equivalent and elaborates.
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

set_option backward.isDefEq.respectTransparency false in
/-- The original structure module is a right unit for the original sheafified tensor. -/
def moduleTensorRightUnitIso (M : X.Modules) :
    moduleTensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategory.rightUnitor (C := X.PresheafOfModules) M.val) ≪≫
    -- Not `asIso (counit.app M)`: since `Scheme.Modules` is a plain `def`, its `Category` instance is
    -- not the same instance term as that of `SheafOfModules`, and instance search (at reducible
    -- transparency) does not find `IsIso (counit.app M)`. Taking the natural isomorphism first and then
    -- its component is equivalent and elaborates.
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

set_option backward.isDefEq.respectTransparency false in
/-- Before the original sheafification unit, the left unit map is the presheaf unitor. -/
theorem moduleTensorLeftUnitIso_fac (M : X.Modules) :
    moduleTensorSheafificationUnit (SheafOfModules.unit X.ringCatSheaf) M ≫
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (moduleTensorLeftUnitIso M).hom.val =
      (MonoidalCategory.leftUnitor (C := X.PresheafOfModules) M.val).hom := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ (moduleTensorLeftUnitIso M).hom).symm.trans
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply
          (MonoidalCategory.leftUnitor (C := X.PresheafOfModules) M.val).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Before the original sheafification unit, the right unit map is the presheaf unitor. -/
theorem moduleTensorRightUnitIso_fac (M : X.Modules) :
    moduleTensorSheafificationUnit M (SheafOfModules.unit X.ringCatSheaf) ≫
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (moduleTensorRightUnitIso M).hom.val =
      (MonoidalCategory.rightUnitor (C := X.PresheafOfModules) M.val).hom := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ (moduleTensorRightUnitIso M).hom).symm.trans
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply
          (MonoidalCategory.rightUnitor (C := X.PresheafOfModules) M.val).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The left unit isomorphism acts on an original tensor section by scalar multiplication. -/
@[simp]
theorem moduleTensorLeftUnitIso_hom_section {M : X.Modules} {U : X.Opens}
    (r : Γ(X, U)) (s : Γ(M, U)) :
    (moduleTensorLeftUnitIso M).hom.app U
      (moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf) r s) = r • s := by
  have h := congrArg (fun f ↦ f.app (op U) (r ⊗ₜ[Γ(X, U)] s))
    (moduleTensorLeftUnitIso_fac M)
  change (moduleTensorLeftUnitIso M).hom.app U (moduleTensorSection r s) =
    (MonoidalCategory.leftUnitor (C := ModuleCat Γ(X, U)) (M.val.obj (op U))).hom
      (r ⊗ₜ[Γ(X, U)] s) at h
  exact h.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r s)

section RightUnitSection

-- The right unitor of Mathlib's monoidal structure on presheaves of modules lives
-- over the ring `(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)`, whose carrier is
-- `↑(X.ringCatSheaf.obj.obj (op U))`; Mathlib registers `CommRing` on it only in the syntactic
-- form `(R ⋙ forget₂ _ RingCat).obj X` (`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`),
-- which instance search does not recognise through `Scheme.ringCatSheaf`. This is that same
-- instance spelled for the scheme (cf. `ModuleDualPowerContraction`); it is scoped to this section.
-- Name carries a file-specific suffix: `local instance` leaves the *name* global.
local instance moduleTensorUnitRingCatSectionsCommRing (U : X.Opens) :
    CommRing ↑(X.ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing ↑(X.presheaf.obj (op U)))

set_option backward.isDefEq.respectTransparency false in
/-- The right unit isomorphism acts on an original tensor section by scalar multiplication. -/
@[simp]
theorem moduleTensorRightUnitIso_hom_section {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) (r : Γ(X, U)) :
    (moduleTensorRightUnitIso M).hom.app U
      (moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) s r) = r • s := by
  have h := congrArg (fun f ↦ f.app (op U) (s ⊗ₜ[Γ(X, U)] r))
    (moduleTensorRightUnitIso_fac M)
  change (moduleTensorRightUnitIso M).hom.app U (moduleTensorSection s r) =
    (MonoidalCategory.rightUnitor (C := ModuleCat Γ(X, U)) (M.val.obj (op U))).hom
      (s ⊗ₜ[Γ(X, U)] r) at h
  exact h.trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply s r)

end RightUnitSection

set_option backward.isDefEq.respectTransparency false in
/-- The inverse left unit sends an arbitrary original section to its tensor with `1`. -/
@[simp]
theorem moduleTensorLeftUnitIso_inv_section {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) :
    (moduleTensorLeftUnitIso M).inv.app U s =
      moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf)
        ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) s := by
  have h := congrArg
    (fun f ↦ f.app U (moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf)
      ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) s))
    (moduleTensorLeftUnitIso M).hom_inv_id
  change (moduleTensorLeftUnitIso M).inv.app U
      ((moduleTensorLeftUnitIso M).hom.app U
        (moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf)
          ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) s)) =
      moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf)
        ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) s at h
  rw [moduleTensorLeftUnitIso_hom_section, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse right unit sends an arbitrary original section to its tensor with `1`. -/
@[simp]
theorem moduleTensorRightUnitIso_inv_section {M : X.Modules} {U : X.Opens}
    (s : Γ(M, U)) :
    (moduleTensorRightUnitIso M).inv.app U s =
      moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) s
        ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) := by
  have h := congrArg
    (fun f ↦ f.app U (moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) s
      ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U))))
    (moduleTensorRightUnitIso M).hom_inv_id
  change (moduleTensorRightUnitIso M).inv.app U
      ((moduleTensorRightUnitIso M).hom.app U
        (moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) s
          ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)))) =
      moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) s
        ((1 : Γ(X, U)) : Γ(SheafOfModules.unit X.ringCatSheaf, U)) at h
  rw [moduleTensorRightUnitIso_hom_section, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The left unit isomorphism is natural in every morphism of the original module sheaves.

Proof: a morphism out of a sheafification is determined by its composite with the
sheafification unit (`homEquiv` of the adjunction is injective); after the two
`homEquiv_naturality` lemmas, both sides become the presheaf-level naturality
`(𝟙 ◁ φ.val) ≫ (λ_ N.val).hom = (λ_ M.val).hom ≫ φ.val` of Mathlib's monoidal
structure on presheaves of modules. -/
theorem moduleTensorLeftUnitIso_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (𝟙 (SheafOfModules.unit X.ringCatSheaf).val) φ.val) ≫
      (moduleTensorLeftUnitIso N).hom = (moduleTensorLeftUnitIso M).hom ≫ φ := by
  have hN : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (SheafOfModules.unit X.ringCatSheaf).val N.val) N (moduleTensorLeftUnitIso N).hom =
      (MonoidalCategory.leftUnitor (C := X.PresheafOfModules) N.val).hom :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ N).apply_symm_apply _
  have hM : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (SheafOfModules.unit X.ringCatSheaf).val M.val) M (moduleTensorLeftUnitIso M).hom =
      (MonoidalCategory.leftUnitor (C := X.PresheafOfModules) M.val).hom :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply _
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right _ _).symm
  rw [hN, hM]
  exact MonoidalCategory.leftUnitor_naturality (C := X.PresheafOfModules) φ.val

set_option backward.isDefEq.respectTransparency false in
/-- The right unit isomorphism is natural in every morphism of the original module sheaves.

Proof: as for `moduleTensorLeftUnitIso_naturality`, via injectivity of the sheafification
adjunction's `homEquiv` and Mathlib's presheaf-level `rightUnitor_naturality`. -/
theorem moduleTensorRightUnitIso_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          φ.val (𝟙 (SheafOfModules.unit X.ringCatSheaf).val)) ≫
      (moduleTensorRightUnitIso N).hom = (moduleTensorRightUnitIso M).hom ≫ φ := by
  have hN : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        N.val (SheafOfModules.unit X.ringCatSheaf).val) N (moduleTensorRightUnitIso N).hom =
      (MonoidalCategory.rightUnitor (C := X.PresheafOfModules) N.val).hom :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ N).apply_symm_apply _
  have hM : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        M.val (SheafOfModules.unit X.ringCatSheaf).val) M (moduleTensorRightUnitIso M).hom =
      (MonoidalCategory.rightUnitor (C := X.PresheafOfModules) M.val).hom :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ M).apply_symm_apply _
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right _ _).symm
  rw [hN, hM]
  exact MonoidalCategory.rightUnitor_naturality (C := X.PresheafOfModules) φ.val

end AlgebraicGeometry.Scheme.Modules
