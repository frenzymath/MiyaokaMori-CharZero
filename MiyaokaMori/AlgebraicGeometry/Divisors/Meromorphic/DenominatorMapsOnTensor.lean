import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.StalkTensorPairing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor

/-! # The denominator maps on tensor products

The two maps of the denominator-ideal trick (Stacks 02P2, `divisors-lemma-make-maps-regular-section`),
written on `Scheme.Modules.tensor`, with their values on pure tensor sections and on germs. This is the
bookkeeping layer for the regularity of the denominator maps.

Given `a : I ⟶ O_X` and `b : I ⟶ L` (in the application: the inclusion of the ideal of denominators of a
regular meromorphic section `s` of `L`, and multiplication by `s`, Stacks 02P0), and any `F`:

* `denomMulMap a F : I ⊗ F ⟶ F`, `h ⊗ t ↦ a(h) • t` — the composite
  `I ⊗ F ≅ I ⊗ F → O_X ⊗ F ≅ F` (`tensorIsoTensorObj`, `a ▷ F`, `unitTensorIso`);
* `denomSectionMap b F : I ⊗ F ⟶ F ⊗ L`, `h ⊗ t ↦ t ⊗ b(h)` — the composite
  `I ⊗ F ≅ I ⊗ F → L ⊗ F ≅ F ⊗ L ≅ F ⊗ L` (`b ▷ F`, the braiding `β_`).

The image of `denomMulMap` is the subsheaf `I·F ⊆ F`; `denomSectionMap` is "multiplication by `s`" on
it. Section formulas: `denomMulMap_app_moduleTensorSection`, `denomSectionMap_app_moduleTensorSection`;
germ formulas: `stalkMap_denomMulMap_germ`, `tensorStalkLinearEquiv_stalkMap_denomSectionMap_germ`
(through `Scheme.Modules.tensorStalkLinearEquiv : (A ⊗ B)_x ≃ A_x ⊗ B_x`, Stacks 01CB).
`linearMap_ext_of_moduleTensorSection` says that a linear map out of `(I ⊗ F)_x` is determined by its
values on germs of pure tensor sections (they generate the stalk: `(I ⊗ F)_x ≅ I_x ⊗ F_x` and two germs
have representatives on a common open, `exists_germ_pair`).

Source: Stacks 02P2 (proof: the maps `IM → M`, `x ↦ x`, and `σ : IM → M_{b₀} ⊗ …`, `x ↦ a₀x/b₀`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(f ≫ g).app U x = g.app U (f.app U x)`. -/
theorem DenominatorMaps.comp_app_apply {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D) (U : X.Opens)
    (x : Γ(A, U)) : (f ≫ g).app U x = g.app U (f.app U x) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

/-- `e.hom.app U (e.inv.app U w) = w` for an isomorphism of module sheaves. -/
theorem DenominatorMaps.iso_hom_app_inv_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens)
    (w : Γ(B, U)) : e.hom.app U (e.inv.app U w) = w := by
  rw [← DenominatorMaps.comp_app_apply, e.inv_hom_id, AlgebraicGeometry.Scheme.Modules.Hom.id_app]
  rfl

/-- `e.inv.app U (e.hom.app U w) = w` for an isomorphism of module sheaves. -/
theorem DenominatorMaps.iso_inv_app_hom_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens)
    (w : Γ(A, U)) : e.inv.app U (e.hom.app U w) = w := by
  rw [← DenominatorMaps.comp_app_apply, e.hom_inv_id, AlgebraicGeometry.Scheme.Modules.Hom.id_app]
  rfl

/-- Right whiskering on a pure tensor section: `(f ▷ B)(a ⊗ b) = f(a) ⊗ b`. -/
theorem DenominatorMaps.whiskerRight_app_tensorSections {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) f B).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

/-- **The inclusion map `I ⊗ F → F`, `h ⊗ t ↦ a(h) • t`** (Stacks 02P2, the map `IM → M`). -/
def denomMulMap {I : X.Modules} (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (F : X.Modules) : AlgebraicGeometry.Scheme.Modules.tensor I F ⟶ F :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj I F).hom ≫
    CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) a F ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ F).inv ≫
    (AlgebraicGeometry.Scheme.Modules.unitTensorIso F).hom

/-- **The "multiplication by `s`" map `I ⊗ F → F ⊗ L`, `h ⊗ t ↦ t ⊗ b(h)`** (Stacks 02P2, the map `σ`). -/
def denomSectionMap {I L : X.Modules} (b : I ⟶ L) (F : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor I F ⟶ AlgebraicGeometry.Scheme.Modules.tensor F L :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj I F).hom ≫
    CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) b F ≫
    (CategoryTheory.BraidedCategory.braiding (C := X.Modules) L F).hom ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F L).inv

/-- `unitTensorIso` on a pure tensor section: `r ⊗ t ↦ r • t`. -/
theorem unitTensorIso_hom_app_moduleTensorSection (F : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (t : Γ(F, U)) :
    (AlgebraicGeometry.Scheme.Modules.unitTensorIso F).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) r t) =
      r • t := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.unitTensorIso F).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) r t) =
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) F).hom.app U
        ((CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
          (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) F).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) F U r t)) := by
    show ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ F).hom ≫
      CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
        (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) F ≫
      (CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := X.Modules) F).hom).app U _ = _
    erw [DenominatorMaps.comp_app_apply, DenominatorMaps.comp_app_apply]
  have h3 : (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
          (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) F).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) F U r t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules) F U r t :=
    DenominatorMaps.whiskerRight_app_tensorSections
      (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) U r t
  rw [h1, h3]
  exact AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections F U r t

/-- `denomMulMap` on a pure tensor section: `h ⊗ t ↦ a(h) • t`. -/
theorem denomMulMap_app_moduleTensorSection {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (F : X.Modules) (U : X.Opens)
    (h : Γ(I, U)) (t : Γ(F, U)) :
    (denomMulMap a F).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t) =
      (show Γ(X, U) from a.app U h) • t := by
  have h1 : (denomMulMap a F).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t) =
      (AlgebraicGeometry.Scheme.Modules.unitTensorIso F).hom.app U
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ F).inv.app U
          ((CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) a F).app U
            (AlgebraicGeometry.Scheme.Modules.tensorSections I F U h t))) := by
    unfold denomMulMap
    erw [DenominatorMaps.comp_app_apply, DenominatorMaps.comp_app_apply,
      DenominatorMaps.comp_app_apply]
  have h2 : (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) a F).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections I F U h t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) F U (a.app U h) t :=
    DenominatorMaps.whiskerRight_app_tensorSections a U h t
  have h3 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) F).inv.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) F U (a.app U h) t) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
        (a.app U h) t :=
    DenominatorMaps.iso_inv_app_hom_app
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ F) U _
  rw [h1, h2, h3]
  exact unitTensorIso_hom_app_moduleTensorSection F U _ t

/-- `denomSectionMap` on a pure tensor section: `h ⊗ t ↦ t ⊗ b(h)`. -/
theorem denomSectionMap_app_moduleTensorSection {I L : X.Modules} (b : I ⟶ L) (F : X.Modules)
    (U : X.Opens) (h : Γ(I, U)) (t : Γ(F, U)) :
    (denomSectionMap b F).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection t (b.app U h) := by
  have h1 : (denomSectionMap b F).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t) =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F L).inv.app U
        ((CategoryTheory.BraidedCategory.braiding (C := X.Modules) L F).hom.app U
          ((CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) b F).app U
            (AlgebraicGeometry.Scheme.Modules.tensorSections I F U h t))) := by
    unfold denomSectionMap
    erw [DenominatorMaps.comp_app_apply, DenominatorMaps.comp_app_apply,
      DenominatorMaps.comp_app_apply]
  rw [h1, DenominatorMaps.whiskerRight_app_tensorSections,
    AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections]
  exact DenominatorMaps.iso_inv_app_hom_app
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F L) U _

/-- Germ formula for `denomMulMap`: the germ of `h ⊗ t` goes to `a(h)_x • t_x`. -/
theorem stalkMap_denomMulMap_germ {I : X.Modules}
    (a : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (h : Γ(I, U)) (t : Γ(F, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomMulMap a F)
        ((AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.germ U x hx
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t)) =
      X.presheaf.germ U x hx (show Γ(X, U) from a.app U h) • F.presheaf.germ U x hx t := by
  erw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, denomMulMap_app_moduleTensorSection]
  exact PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx _ t

/-- Germ formula for `denomSectionMap` through `(F ⊗ L)_x ≃ F_x ⊗ L_x`: the germ of `h ⊗ t` goes to
`t_x ⊗ b(h)_x`. -/
theorem tensorStalkLinearEquiv_stalkMap_denomSectionMap_germ {I L : X.Modules} (b : I ⟶ L)
    (F : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U) (h : Γ(I, U)) (t : Γ(F, U)) :
    AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv F L x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (denomSectionMap b F)
          ((AlgebraicGeometry.Scheme.Modules.tensor I F).presheaf.germ U x hx
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection h t))) =
      F.presheaf.germ U x hx t ⊗ₜ[X.presheaf.stalk x]
        AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x b (I.presheaf.germ U x hx h) := by
  erw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, denomSectionMap_app_moduleTensorSection,
    AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv_germ_moduleTensorSection,
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ]

/-- Germs of pure tensor sections generate `(A ⊗ B)_x`: two linear maps agreeing on them agree. -/
theorem linearMap_ext_of_moduleTensorSection (A B : X.Modules) (x : X) {N : Type u} [AddCommGroup N]
    [Module (X.presheaf.stalk x) N]
    (f g : (AlgebraicGeometry.Scheme.Modules.tensor A B).presheaf.stalk x →ₗ[X.presheaf.stalk x] N)
    (hfg : ∀ (U : X.Opens) (hx : x ∈ U) (a : Γ(A, U)) (b : Γ(B, U)),
      f ((AlgebraicGeometry.Scheme.Modules.tensor A B).presheaf.germ U x hx
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)) =
        g ((AlgebraicGeometry.Scheme.Modules.tensor A B).presheaf.germ U x hx
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b))) :
    f = g := by
  ext z
  obtain ⟨w, rfl⟩ := (AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv A B x).symm.surjective z
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
    obtain ⟨U, hx, a, b, rfl, rfl⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_germ_pair A B x m n
    erw [AlgebraicGeometry.Scheme.Modules.tensorStalkLinearEquiv_symm_tmul_germ]
    exact hfg U hx a b
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end AlgebraicGeometry.Scheme.Modules

end
