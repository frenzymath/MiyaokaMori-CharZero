import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSheafificationUnit

/-! # The dual commutes with restriction to open subschemes

The dual sheaf commutes with restriction to an open subscheme: `(E^∨)|_U ≅ (E|_U)^∨` (the internal Hom
sheaf is by definition computed open by open).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

open AlgebraicGeometry.Scheme.Modules

namespace MiyaokaMori.DualRestrictScratch

variable (X : Scheme.{u}) (U : X.Opens) (M : X.Modules)

set_option backward.isDefEq.respectTransparency false in
theorem openRestrict_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (x : Γ(M.restrict U.ι, V)) :
    (r • x : Γ(M.restrict U.ι, V)) =
      (show Γ(X, U.ι ''ᵁ V) from r) • (show Γ(M, U.ι ''ᵁ V) from x) := by
  change (U.ι.appIso V).inv r • (show Γ(M, U.ι ''ᵁ V) from x) =
    (show Γ(X, U.ι ''ᵁ V) from r) • (show Γ(M, U.ι ''ᵁ V) from x)
  rw [Scheme.Opens.ι_appIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
def openLocalFunctionalEquiv (V : U.toScheme.Opens) :
    (Γ(M.restrict U.ι, V) →ₗ[Γ(U.toScheme, V)] Γ(U.toScheme, V)) ≃
      (Γ(M, U.ι ''ᵁ V) →ₗ[Γ(X, U.ι ''ᵁ V)] Γ(X, U.ι ''ᵁ V)) where
  toFun φ :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' r x :=
        (congrArg φ (openRestrict_smul X U M V r x).symm).trans (φ.map_smul r x) }
  invFun φ :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' r x :=
        (congrArg φ (openRestrict_smul X U M V r x)).trans (φ.map_smul r x) }
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in
def openLocalDualRestrict (V : U.toScheme.Opens) :
    LocalDualSections X M (U.ι ''ᵁ V) →ₗ[Γ(U.toScheme, V)]
      LocalDualSections U.toScheme (M.restrict U.ι) V where
  toFun φ := ⟨fun W ↦ (openLocalFunctionalEquiv X U M W.left).symm
    (φ.1 ((Over.post U.ι.opensFunctor).obj W)), by
      intro W Z j x
      change φ.1 ((Over.post U.ι.opensFunctor).obj W)
          (M.presheaf.map (U.ι.opensFunctor.map j.left).op x) =
        X.presheaf.map (U.ι.opensFunctor.map j.left).op
          (φ.1 ((Over.post U.ι.opensFunctor).obj Z) x)
      exact φ.2 _ _ ((Over.post U.ι.opensFunctor).map j) x⟩
  map_add' φ ψ := rfl
  map_smul' r φ := rfl

def openOverImageEquiv (V : U.toScheme.Opens) : Over V ≃ Over (U.ι ''ᵁ V) :=
  Equiv.ofBijective (Over.post U.ι.opensFunctor).obj (by
    constructor
    · intro W Z h
      apply CostructuredArrow.obj_ext _ _
        (U.ι.image_injective (congrArg Over.left h))
      exact Subsingleton.elim _ _
    · intro W
      have hle : U.ι ⁻¹ᵁ W.left ≤ V := by
        intro x hx
        exact U.ι.apply_mem_image_iff.mp ((leOfHom W.hom) hx)
      have him : U.ι ''ᵁ (U.ι ⁻¹ᵁ W.left) = W.left := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        exact inf_eq_right.mpr ((leOfHom W.hom).trans (U.ι_image_le V))
      refine ⟨Over.mk (homOfLE hle), CostructuredArrow.obj_ext _ _ him ?_⟩
      exact Subsingleton.elim _ _)

def openLocalFunctionalFamilyEquiv (V : U.toScheme.Opens) :
    LocalFunctionalFamily X M (U.ι ''ᵁ V) ≃
      LocalFunctionalFamily U.toScheme (M.restrict U.ι) V :=
  (Equiv.piCongrLeft (LocalFunctional X M (U.ι ''ᵁ V))
      (openOverImageEquiv X U V)).symm.trans
    (Equiv.piCongrRight fun W ↦ (openLocalFunctionalEquiv X U M W.left).symm)

theorem openLocalFunctionalFamilyEquiv_apply (V : U.toScheme.Opens)
    (φ : LocalFunctionalFamily X M (U.ι ''ᵁ V)) (W : Over V) :
    openLocalFunctionalFamilyEquiv X U M V φ W =
      (openLocalFunctionalEquiv X U M W.left).symm
        (φ ((Over.post U.ι.opensFunctor).obj W)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem openLocalFunctionalFamilyEquiv_compatible (V : U.toScheme.Opens)
    (φ : LocalFunctionalFamily X M (U.ι ''ᵁ V)) :
    φ ∈ localDualSubmodule X M (U.ι ''ᵁ V) ↔
      openLocalFunctionalFamilyEquiv X U M V φ ∈
        localDualSubmodule U.toScheme (M.restrict U.ι) V := by
  constructor
  · intro hφ
    exact (openLocalDualRestrict X U M V ⟨φ, hφ⟩).2
  · intro hφ W Z j x
    obtain ⟨W, rfl⟩ := (openOverImageEquiv X U V).surjective W
    obtain ⟨Z, rfl⟩ := (openOverImageEquiv X U V).surjective Z
    obtain ⟨j, rfl⟩ := (Over.post U.ι.opensFunctor).map_surjective j
    exact hφ W Z j x

set_option backward.isDefEq.respectTransparency false in
theorem openLocalDualRestrict_bijective (V : U.toScheme.Opens) :
    Function.Bijective (openLocalDualRestrict X U M V) :=
  ((openLocalFunctionalFamilyEquiv X U M V).subtypeEquiv
    (openLocalFunctionalFamilyEquiv_compatible X U M V)).bijective

set_option backward.isDefEq.respectTransparency false in
def openLocalDualRestrictLinearEquiv (V : U.toScheme.Opens) :
    LocalDualSections X M (U.ι ''ᵁ V) ≃ₗ[Γ(U.toScheme, V)]
      LocalDualSections U.toScheme (M.restrict U.ι) V :=
  LinearEquiv.ofBijective (openLocalDualRestrict X U M V)
    (openLocalDualRestrict_bijective X U M V)

set_option backward.isDefEq.respectTransparency false in
theorem openLocalDualRestrict_restrict {V W : U.toScheme.Opens} (j : V ⟶ W)
    (φ : LocalDualSections X M (U.ι ''ᵁ W)) :
    localDualRestrict (M.restrict U.ι) j (openLocalDualRestrict X U M W φ) =
      openLocalDualRestrict X U M V
        (localDualRestrict M (U.ι.opensFunctor.map j) φ) := rfl

end MiyaokaMori.DualRestrictScratch

/-! ## The sheaf-level isomorphism `(M^∨)|_U ≅ (M|_U)^∨`

`AlgebraicGeometry.Scheme.Modules.DualRestrict.dualRestrictIso` is built through the fact that the dual presheaf is already a
sheaf (`MiyaokaMori.ModuleDualSectionEquiv.unit_isIso`), so that its sections are literally the reindexed
compatible families (`dualRestrictIso_hom_app`, `dualRestrictIso_hom_app_val`). The reindexing helpers
above, the isomorphism and `Scheme.Modules.dual_restrict` form one module.
Source: Stacks Project Tag 01CM (`modules.tex`, internal Hom: `Hom(F, G)(U) = Hom_{O_U}(F|_U, G|_U)`). -/

namespace AlgebraicGeometry.Scheme.Modules

namespace DualRestrict

variable (X : Scheme.{u}) (U : X.Opens) (M : X.Modules)

set_option backward.isDefEq.respectTransparency false

open MiyaokaMori.DualRestrictScratch (openRestrict_smul openLocalDualRestrict
  openLocalDualRestrictLinearEquiv openLocalDualRestrict_restrict)

open ModuleDualSheafificationUnit
open MiyaokaMori.ModuleDualSectionEquiv (unit_isIso unitIso unitIso_hom sectionEquiv sectionEquiv_apply
  sectionEquiv_restrict)

/-- Sections of the restricted dual over `V` are compatible families on `M` over the image open,
`Γ(U, V)`-linearly. -/
def restrictSectionEquiv (V : U.toScheme.Opens) :
    Γ((moduleSheafDual M).restrict U.ι, V) ≃ₗ[Γ(U.toScheme, V)]
      LocalDualSections X M (U.ι ''ᵁ V) where
  toFun s := (sectionEquiv M (U.ι ''ᵁ V)).symm s
  invFun φ := sectionEquiv M (U.ι ''ᵁ V) φ
  map_add' s t := map_add _ s t
  map_smul' r s := by
    rw [openRestrict_smul X U (moduleSheafDual M) V r s]
    exact (sectionEquiv M (U.ι ''ᵁ V)).symm.map_smul _ _
  left_inv s := (sectionEquiv M (U.ι ''ᵁ V)).apply_symm_apply s
  right_inv φ := (sectionEquiv M (U.ι ''ᵁ V)).symm_apply_apply φ

/-- The section-level comparison: sections of the restricted dual over `V` are sections of the
dual of the restriction over `V`. -/
def sectionLinearEquiv (V : U.toScheme.Opens) :
    Γ((moduleSheafDual M).restrict U.ι, V) ≃ₗ[Γ(U.toScheme, V)]
      Γ(moduleSheafDual (M.restrict U.ι), V) :=
  restrictSectionEquiv X U M V ≪≫ₗ openLocalDualRestrictLinearEquiv X U M V ≪≫ₗ
    sectionEquiv (M.restrict U.ι) V

theorem sectionLinearEquiv_apply (V : U.toScheme.Opens)
    (s : Γ((moduleSheafDual M).restrict U.ι, V)) :
    sectionLinearEquiv X U M V s = sectionEquiv (M.restrict U.ι) V
      (openLocalDualRestrict X U M V ((sectionEquiv M (U.ι ''ᵁ V)).symm s)) := rfl

/-- The presheaf-level isomorphism underlying `dualRestrictIso`. -/
def presheafIso :
    ((moduleSheafDual M).restrict U.ι).val ≅ (moduleSheafDual (M.restrict U.ι)).val :=
  PresheafOfModules.isoMk (fun V ↦ (sectionLinearEquiv X U M V.unop).toModuleIso) (by
    intro V W j
    ext s
    change sectionLinearEquiv X U M W.unop
        (((moduleSheafDual M).restrict U.ι).presheaf.map j s) =
      (moduleSheafDual (M.restrict U.ι)).presheaf.map j (sectionLinearEquiv X U M V.unop s)
    have h2 := sectionEquiv_symm_restrict M (U.ι.opensFunctor.map j.unop) s
    rw [show j = j.unop.op from rfl]
    rw [sectionLinearEquiv_apply, sectionLinearEquiv_apply, sectionEquiv_restrict,
      openLocalDualRestrict_restrict]
    congr 2)

/-- **Dual commutes with restriction to an open subscheme**:
`(M^∨)|_U ≅ (M|_U)^∨`. -/
def dualRestrictIso :
    (moduleSheafDual M).restrict U.ι ≅ moduleSheafDual (M.restrict U.ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (presheafIso X U M)

theorem dualRestrictIso_hom_app (V : U.toScheme.Opens)
    (s : Γ((moduleSheafDual M).restrict U.ι, V)) :
    (dualRestrictIso X U M).hom.app V s = sectionEquiv (M.restrict U.ι) V
      (openLocalDualRestrict X U M V ((sectionEquiv M (U.ι ''ᵁ V)).symm s)) := rfl

/-- The functional underlying the image of `s` is the functional underlying `s`, read on the
image open. -/
theorem dualRestrictIso_hom_app_val (V : U.toScheme.Opens)
    (s : Γ((moduleSheafDual M).restrict U.ι, V)) (W : Over V)
    (t : Γ(M.restrict U.ι, W.left)) :
    ((sectionEquiv (M.restrict U.ι) V).symm ((dualRestrictIso X U M).hom.app V s)).1 W t =
      ((sectionEquiv M (U.ι ''ᵁ V)).symm s).1 ((Over.post U.ι.opensFunctor).obj W) t := by
  rw [dualRestrictIso_hom_app, LinearEquiv.symm_apply_apply]
  rfl

end DualRestrict

end AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.dual_restrict {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (U : X.Opens) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        (AlgebraicGeometry.Scheme.Modules.dual E) ≅
      AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E)) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let d := AlgebraicGeometry.Scheme.Modules.DualRestrict.dualRestrictIso X U E
  let q := AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (e.app E).symm
  exact ⟨(e.app (Scheme.Modules.dual E)).symm ≪≫ d ≪≫ q⟩

end
