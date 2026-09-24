import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualPresheafPairing
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleTensorDualCurry
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorAssociator
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# The canonical exterior-dual comparison morphism

The inverse of the original dual sheafification unit sends actual dual sections to
their compatible local functionals. The exterior presheaf functor and the canonical
determinant pairing then give a pairing of the two original exterior presheaves.
After sheafification, the tensor comparisons identify its domain with the tensor of
the original exterior sheaves. Currying this constructed pairing gives the desired
morphism into the original module dual.

The evaluation formulas retain the determinant convention on every smaller open.
All schemes, modules and exterior degrees are arbitrary, including degree zero.
Invertibility under local finite freeness is a separate statement.

Sources: Stacks Project, `modules.tex`, `lemma-local-tensor-algebra`,
`lemma-tensor-product-sheafification` and `lemma-internal-hom`; Mathlib's exterior-power pairing.
This supplies the comparison map needed for the tangent/anticanonical degree comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

/- `Scheme.ringCatSheaf` is a plain, non-reducible `def` (through `sheafCompose`/`forget₂`), so
typeclass search cannot see through it and does not find the `CommRing` structure on the section
ring. It is transported by hand here; the name carries a file prefix since a `local instance` is local
only as an attribute. -/
local instance exteriorDualSheafComparisonSectionCommRing {X : Scheme.{u}}
    (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

namespace ExteriorDualSheafComparison

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ)

/-- The determinant pairing after recovering the original compatible dual functionals. -/
def presheafPairing :
    PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleExteriorPresheaf X (moduleSheafDual M).val n)
        (moduleExteriorPresheaf X M.val n) ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (SheafOfModules.unit X.ringCatSheaf).val :=
  PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
      (moduleExteriorPresheafMap X n (MiyaokaMori.ModuleDualSectionEquiv.unitIso M).inv)
      (𝟙 (moduleExteriorPresheaf X M.val n)) ≫
    ExteriorDualPresheafPairing.presheafPairing M n

/-- On the original wedge generators the pairing is the determinant of functional values. -/
theorem presheafPairing_wedge (U : X.Opens)
    (Φ : Fin n → Γ(moduleSheafDual M, U)) (v : Fin n → Γ(M, U)) :
    (presheafPairing M n).app (op U)
        (ModuleCat.exteriorPower.mk Φ ⊗ₜ[Γ(X, U)] ModuleCat.exteriorPower.mk v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦
        ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm (Φ j)).val
          (Over.mk (𝟙 U)) (v i))) := by
  change (ExteriorDualPresheafPairing.presheafPairing M n).app (op U)
    ((moduleExteriorPresheafMap X n (MiyaokaMori.ModuleDualSectionEquiv.unitIso M).inv).app
        (op U) (ModuleCat.exteriorPower.mk Φ) ⊗ₜ[Γ(X, U)]
      ModuleCat.exteriorPower.mk v) = _
  rw [moduleExteriorPresheafMap_mk, ExteriorDualPresheafPairing.presheafPairing_tmul]
  exact ExteriorDualPresheafPairing.sectionPairing_pure M n U
    ((MiyaokaMori.ModuleDualSectionEquiv.unitIso M).inv.app (op U) ∘ Φ) v

/-- Sheafifying both actual exterior presheaves identifies their tensor with the original tensor
of the two exterior sheaves. -/
def tensorSheafificationIso :
    moduleSheafification X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (moduleExteriorPresheaf X (moduleSheafDual M).val n)
          (moduleExteriorPresheaf X M.val n)) ≅
      moduleTensor (moduleExteriorPower X (moduleSheafDual M) n)
        (moduleExteriorPower X M n) :=
  ModuleTensorAssociator.leftUnitIso
      (moduleExteriorPresheaf X (moduleSheafDual M).val n)
      (moduleExteriorPresheaf X M.val n) ≪≫
    ModuleTensorAssociator.rightUnitIso (moduleExteriorPower X (moduleSheafDual M) n).val
      (moduleExteriorPresheaf X M.val n)

/-- The tensor comparison sends each original tensor through the two exterior units. -/
theorem tensorSheafificationIso_section (U : X.Opens)
    (a : (moduleExteriorPresheaf X (moduleSheafDual M).val n).obj (op U))
    (b : (moduleExteriorPresheaf X M.val n).obj (op U)) :
    (tensorSheafificationIso M n).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleExteriorPresheaf X (moduleSheafDual M).val n)
            (moduleExteriorPresheaf X M.val n)) U (a ⊗ₜ[Γ(X, U)] b)) =
      moduleTensorSection
        (moduleSheafificationUnit X (moduleExteriorPresheaf X (moduleSheafDual M).val n) U a)
        (moduleSheafificationUnit X (moduleExteriorPresheaf X M.val n) U b) := by
  change (ModuleTensorAssociator.rightUnitIso
      (moduleExteriorPower X (moduleSheafDual M) n).val
      (moduleExteriorPresheaf X M.val n)).hom.app U
    ((ModuleTensorAssociator.leftUnitIso
      (moduleExteriorPresheaf X (moduleSheafDual M).val n)
      (moduleExteriorPresheaf X M.val n)).hom.app U _) = _
  rw [ModuleTensorAssociator.leftUnitIso_section]
  -- `rw` needs the same `?P` at both occurrences in the goal, but here one is
  -- `(moduleExteriorPower X _ n).val` and the other `(moduleSheafification X _).val` (only defeq),
  -- so use `exact` with all arguments explicit; defeq is checked once at the end.
  exact ModuleTensorAssociator.rightUnitIso_section
    (moduleExteriorPower X (moduleSheafDual M) n).val
    (moduleExteriorPresheaf X M.val n) U
    (moduleSheafificationUnit X (moduleExteriorPresheaf X (moduleSheafDual M).val n) U a) b

/-- The inverse tensor comparison recovers the specified original tensor generator. -/
theorem tensorSheafificationIso_inv_section (U : X.Opens)
    (a : (moduleExteriorPresheaf X (moduleSheafDual M).val n).obj (op U))
    (b : (moduleExteriorPresheaf X M.val n).obj (op U)) :
    (tensorSheafificationIso M n).inv.app U
        (moduleTensorSection
          (moduleSheafificationUnit X
            (moduleExteriorPresheaf X (moduleSheafDual M).val n) U a)
          (moduleSheafificationUnit X (moduleExteriorPresheaf X M.val n) U b)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (moduleExteriorPresheaf X (moduleSheafDual M).val n)
          (moduleExteriorPresheaf X M.val n)) U (a ⊗ₜ[Γ(X, U)] b) := by
  rw [← tensorSheafificationIso_section M n U a b]
  exact congrArg (fun f ↦ f.app U
    (moduleSheafificationUnit X
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleExteriorPresheaf X (moduleSheafDual M).val n)
        (moduleExteriorPresheaf X M.val n)) U (a ⊗ₜ[Γ(X, U)] b)))
    (tensorSheafificationIso M n).hom_inv_id

/-- Descend the constructed exterior-presheaf pairing through the original sheafification. -/
def descendedPairing :
    moduleSheafification X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (moduleExteriorPresheaf X (moduleSheafDual M).val n)
          (moduleExteriorPresheaf X M.val n)) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
      (moduleExteriorPresheaf X (moduleSheafDual M).val n)
      (moduleExteriorPresheaf X M.val n)) (SheafOfModules.unit X.ringCatSheaf)).symm
        (presheafPairing M n)

/-- The descended pairing agrees with its original presheaf map before the actual unit. -/
theorem descendedPairing_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          (moduleExteriorPresheaf X (moduleSheafDual M).val n)
          (moduleExteriorPresheaf X M.val n)) ≫
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (descendedPairing M n).val = presheafPairing M n := by
  unfold descendedPairing
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The actual pairing of the original exterior sheaves, using the tensor comparison's inverse. -/
def sheafPairing :
    moduleTensor (moduleExteriorPower X (moduleSheafDual M) n)
        (moduleExteriorPower X M n) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (tensorSheafificationIso M n).inv ≫ descendedPairing M n

/-- Pairing the two unit images recovers the original exterior-presheaf pairing. -/
theorem sheafPairing_unit_sections (U : X.Opens)
    (a : (moduleExteriorPresheaf X (moduleSheafDual M).val n).obj (op U))
    (b : (moduleExteriorPresheaf X M.val n).obj (op U)) :
    (sheafPairing M n).app U
        (moduleTensorSection
          (moduleSheafificationUnit X
            (moduleExteriorPresheaf X (moduleSheafDual M).val n) U a)
          (moduleSheafificationUnit X (moduleExteriorPresheaf X M.val n) U b)) =
      (presheafPairing M n).app (op U) (a ⊗ₜ[Γ(X, U)] b) := by
  change (descendedPairing M n).app U
    ((tensorSheafificationIso M n).inv.app U _) = _
  rw [tensorSheafificationIso_inv_section]
  exact congrArg (fun f ↦ f.app (op U) (a ⊗ₜ[Γ(X, U)] b)) (descendedPairing_unit M n)

/-- Pairing actual wedge sections is the determinant of their compatible functional values. -/
theorem sheafPairing_wedge (U : X.Opens)
    (Φ : Fin n → Γ(moduleSheafDual M, U)) (v : Fin n → Γ(M, U)) :
    (sheafPairing M n).app U
        (moduleTensorSection (moduleExteriorWedge X (moduleSheafDual M) n U Φ)
          (moduleExteriorWedge X M n U v)) =
      Matrix.det (n := Fin n) (.of (fun i j ↦
        ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm (Φ j)).val
          (Over.mk (𝟙 U)) (v i))) :=
  (sheafPairing_unit_sections M n U
    (ModuleCat.exteriorPower.mk Φ) (ModuleCat.exteriorPower.mk v)).trans
      (presheafPairing_wedge M n U Φ v)

end ExteriorDualSheafComparison

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ)

/-- The canonical morphism from the exterior power of the original dual to the dual of the
original exterior power, obtained by currying the constructed determinant pairing. -/
def exteriorDualComparison :
    moduleExteriorPower X (moduleSheafDual M) n ⟶
      moduleSheafDual (moduleExteriorPower X M n) :=
  ModuleTensorDualCurry.curry (moduleExteriorPower X (moduleSheafDual M) n)
    (moduleExteriorPower X M n) (ExteriorDualSheafComparison.sheafPairing M n)

/-- On every smaller open, the comparison evaluates using its actual exterior tensor pairing. -/
theorem exteriorDualComparison_eval (U : X.Opens)
    (s : Γ(moduleExteriorPower X (moduleSheafDual M) n, U))
    (V : Over U) (t : Γ(moduleExteriorPower X M n, V.left)) :
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm
        ((exteriorDualComparison M n).app U s)).val V t =
      (ExteriorDualSheafComparison.sheafPairing M n).app V.left
        (moduleTensorSection
          ((moduleExteriorPower X (moduleSheafDual M) n).presheaf.map V.hom.op s) t) :=
  ModuleTensorDualCurry.curry_eval _ _ _ U s V t

/-- The canonical comparison evaluates two wedges by their original determinant pairing on
every subopen, without a finite-freeness or nondegeneracy assumption. -/
theorem exteriorDualComparison_wedge_eval (U : X.Opens)
    (Φ : Fin n → Γ(moduleSheafDual M, U)) (V : Over U)
    (v : Fin n → Γ(M, V.left)) :
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm
        ((exteriorDualComparison M n).app U
          (moduleExteriorWedge X (moduleSheafDual M) n U Φ))).val V
        (moduleExteriorWedge X M n V.left v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦
        ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm (Φ j)).val V (v i))) := by
  rw [exteriorDualComparison_eval, moduleExteriorWedge_restrict,
    ExteriorDualSheafComparison.sheafPairing_wedge]
  congr 1
  ext i j
  change ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M V.left).symm
      ((moduleSheafDual M).presheaf.map V.hom.op (Φ j))).val
        (Over.mk (𝟙 V.left)) (v i) = _
  rw [ModuleDualSheafificationUnit.sectionEquiv_symm_restrict]
  rfl

/-- Original compatible local functionals give the determinant formula after their own unit
images are wedged; the formula holds on every smaller open and also in degree zero. -/
theorem exteriorDualComparison_functional_wedge_eval (U : X.Opens)
    (Φ : Fin n → LocalDualSections X M U) (V : Over U)
    (v : Fin n → Γ(M, V.left)) :
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm
        ((exteriorDualComparison M n).app U
          (moduleExteriorWedge X (moduleSheafDual M) n U
            (fun j ↦ MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U (Φ j))))).val V
        (moduleExteriorWedge X M n V.left v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ (Φ j).val V (v i))) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    exteriorDualComparison_wedge_eval M n U
      (fun j ↦ MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U (Φ j)) V v

end AlgebraicGeometry.Scheme.Modules
