import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleTensorDualCurry
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# Evaluation of the canonical module dual

The inverse of the original dual sheafification unit turns a dual section into
its compatible family of local functionals. Evaluation on the identity subopen
is bilinear and commutes with every open restriction. It therefore defines a map
from the actual tensor presheaf, which descends to the existing `moduleTensor`.

Currying this evaluation with `ModuleTensorDualCurry.curry` is the identity of
the same `moduleSheafDual`. No local-freeness or nondegeneracy is required.

Sources: Stacks Project, `modules.tex`, `section-tensor-product` and `lemma-internal-hom`; the
coefficient expansion (4.1) in Lemma 4.1 of the paper,
where the dual and the line bundle powers contract in each term.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.ModuleDualTensorEvaluation

universe u

variable {X : Scheme.{u}} (M : X.Modules)

set_option backward.isDefEq.respectTransparency false

/-- The canonical bilinear evaluation on sections, using the identity subopen. -/
def sectionEvaluation (U : X.Opens) :
    Γ(moduleSheafDual M, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun φ := ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val (Over.mk (𝟙 U))
  map_add' φ ψ := by
    ext s
    change (((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm (φ + ψ)).val
        (Over.mk (𝟙 U))) s = _
    simp only [map_add]
    rfl
  map_smul' r φ := by
    ext s
    change (((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm (r • φ)).val
        (Over.mk (𝟙 U))) s = _
    rw [_root_.map_smul]
    change (X.presheaf.map (𝟙 U).op r) *
        (show Γ(X, U) from
          (((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val (Over.mk (𝟙 U))) s) = _
    simp only [op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
    rfl

/-- Section evaluation is precisely the original compatible functional at the identity. -/
theorem sectionEvaluation_apply (U : X.Opens)
    (φ : Γ(moduleSheafDual M, U)) (s : Γ(M, U)) :
    sectionEvaluation M U φ s =
      ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val (Over.mk (𝟙 U)) s := rfl

/-- After restricting a dual section, evaluation recovers its functional on that subopen. -/
theorem sectionEvaluation_subopen (U : X.Opens) (φ : Γ(moduleSheafDual M, U))
    (V : Over U) (s : Γ(M, V.left)) :
    sectionEvaluation M V.left ((moduleSheafDual M).presheaf.map V.hom.op φ) s =
      ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val V s := by
  rw [sectionEvaluation_apply, ModuleDualSheafificationUnit.sectionEquiv_symm_restrict]
  rfl

/-- Bilinear evaluation commutes with simultaneous restriction of both sections. -/
theorem sectionEvaluation_restrict {U V : X.Opens} (i : V ⟶ U)
    (φ : Γ(moduleSheafDual M, U)) (s : Γ(M, U)) :
    sectionEvaluation M V ((moduleSheafDual M).presheaf.map i.op φ)
        (M.presheaf.map i.op s) =
      X.presheaf.map i.op (sectionEvaluation M U φ s) := by
  refine (sectionEvaluation_subopen M U φ (Over.mk i) (M.presheaf.map i.op s)).trans ?_
  rw [sectionEvaluation_apply]
  exact ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).property
    (Over.mk i) (Over.mk (𝟙 U)) (Over.homMk i (by simp)) s

/-- Evaluation on the actual tensor presheaf is the linear lift of section evaluation. -/
def presheafEvaluation :
    moduleTensorPresheaf (moduleSheafDual M) M ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (SheafOfModules.unit X.ringCatSheaf).val where
  app U := ModuleCat.ofHom (TensorProduct.lift (sectionEvaluation M U.unop))
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext fun φ s ↦ by
    change sectionEvaluation M V.unop ((moduleSheafDual M).presheaf.map i φ)
        (M.presheaf.map i s) =
      X.presheaf.map i (sectionEvaluation M U.unop φ s)
    exact sectionEvaluation_restrict M i.unop φ s

/-- The presheaf map evaluates an algebraic pure tensor by the original functional. -/
theorem presheafEvaluation_tmul {U : X.Opens}
    (φ : Γ(moduleSheafDual M, U)) (s : Γ(M, U)) :
    (presheafEvaluation M).app (op U) (φ ⊗ₜ[Γ(X, U)] s) =
      ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val (Over.mk (𝟙 U)) s := rfl

/-- The genuine evaluation from the existing dual tensor the original module to the unit. -/
def evaluation :
    moduleTensor (moduleSheafDual M) M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (moduleTensorPresheaf (moduleSheafDual M) M) (SheafOfModules.unit X.ringCatSheaf)).symm
      (presheafEvaluation M)

/-- Before the original tensor unit, evaluation is the constructed presheaf evaluation. -/
theorem evaluation_fac :
    moduleTensorSheafificationUnit (moduleSheafDual M) M ≫
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (evaluation M).val = presheafEvaluation M := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit _ _ (evaluation M)).symm.trans
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).apply_symm_apply _)

/-- The canonical tensor section evaluates by the original local functional. -/
theorem evaluation_section {U : X.Opens}
    (φ : Γ(moduleSheafDual M, U)) (s : Γ(M, U)) :
    (evaluation M).app U (moduleTensorSection φ s) =
      ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val (Over.mk (𝟙 U)) s := by
  exact (congrArg (fun f ↦ f.app (op U) (φ ⊗ₜ[Γ(X, U)] s))
    (evaluation_fac M)).trans (presheafEvaluation_tmul M φ s)

/-- Evaluation commutes with restriction of every tensor-sheaf section. -/
theorem evaluation_restrict {U V : X.Opens} (i : V ⟶ U)
    (z : Γ(moduleTensor (moduleSheafDual M) M, U)) :
    (evaluation M).app V ((moduleTensor (moduleSheafDual M) M).presheaf.map i.op z) =
      X.presheaf.map i.op ((evaluation M).app U z) :=
  PresheafOfModules.naturality_apply (evaluation M).val i.op z

/-- Currying the actual evaluation recovers the identity of the same canonical dual sheaf. -/
theorem curry_evaluation :
    ModuleTensorDualCurry.curry (moduleSheafDual M) M (evaluation M) =
      𝟙 (moduleSheafDual M) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext φ
  apply (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm.injective
  apply Subtype.ext
  funext V
  ext s
  change ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm
      ((ModuleTensorDualCurry.curry (moduleSheafDual M) M (evaluation M)).app U φ)).val V s =
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm φ).val V s
  rw [ModuleTensorDualCurry.curry_eval, evaluation_section]
  exact sectionEvaluation_subopen M U φ V s

end AlgebraicGeometry.Scheme.Modules.ModuleDualTensorEvaluation
