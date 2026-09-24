import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.CategoryTheory.LocalizedDeltaCancel

/-! # The tensor–Hom adjunction for sheaves of modules (Stacks 01CM)

Stacks 01CM: the tensor–Hom adjunction `Hom(F ⊗ G, H) ≅ Hom(F, Hom(G, H))` for sheaves of modules,
natural in all three variables.

Source: Stacks 01CM (`lemma-internal-hom`; the proof there is "the same as in the algebraic case").

Structure of the proof. `curryPresheafHom` is the currying on the presheaf level,
`internalHomPresheafEval` / `internalHomEval` the evaluation `𝓗om(G, H) ⊗ G ⟶ H`, and
`tensorHomCurry` / `tensorHomUncurry` the two directions of the adjunction. The two inverse laws
`tensorHomUncurry_tensorHomCurry` / `tensorHomCurry_tensorHomUncurry` avoid any description of the
values of `Localization.Monoidal.μ`:

* the cancellation law of the localized monoidal category (`LocalizedDeltaCancel`),
  `L(η ⊗ 𝟙) ≫ (μ⁻¹ ≫ (ε ⊗ ε)) ≫ ((𝟙 ◁ ε⁻¹) ≫ μ) = 𝟙`, uses only the naturality of `δ = μ⁻¹` and
  the left triangle identity of the adjunction, so `μ` disappears entirely;
* this gives `internalHomEval_tensorSections_unit`: `ev(η χ ⊗ t)` is the component of `χ` at
  `Over.mk (𝟙 U)` applied to `t` — a pure section computation;
* from `unit_comp_internalHomEvalCurry` (`η ≫ c₀ = 𝟙`) and `internalHomEvalCurry_comp_unit`
  (`c₀ ≫ η = 𝟙`) it follows that **`internalHomPresheaf G H` is already a sheaf**, without checking
  the sheaf condition directly: `η ≫ c₀ = 𝟙` and the left triangle identity give `L c₀ = ε`, and
  the injectivity of `homEquiv.symm k = L k ≫ ε` concludes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- Homogeneity of the inner layer of the currying: `φ(s|_V ⊗ (r • t)) = r • φ(s|_V ⊗ t)`.
By `tensorSections_smul_right` (which avoids `tmul_smul` and uses `map_smul` of the linear map
`TensorProduct.mk _ _ _ a`), then move the scalar through `φ`. -/
theorem AlgebraicGeometry.Scheme.Modules.curryPresheafHom_inner_map_smul
    {X : AlgebraicGeometry.Scheme.{u}} {F G H : X.Modules}
    (φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) F G ⟶ H)
    {U : X.Opens} (s : Γ(F, U)) (V : CategoryTheory.Over U) (r : Γ(X, V.left))
    (t : Γ(G, V.left)) (y : Γ(H, V.left))
    (hy : y = φ.val.app (Opposite.op V.left)
      (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left
        (F.presheaf.map V.hom.op s) t)) :
    φ.val.app (Opposite.op V.left)
        (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left
          (F.presheaf.map V.hom.op s) (r • t)) = r • y := by
  subst hy
  exact (congrArg (fun z => φ.val.app (Opposite.op V.left) z)
      (AlgebraicGeometry.Scheme.Modules.tensorSections_smul_right F G V.left r
        (F.presheaf.map V.hom.op s) t _ rfl)).trans
    ((φ.val.app (Opposite.op V.left)).hom.map_smul r _)

/-- Currying on the presheaf level: `s ∈ F(U) ↦ (V ⊆ U, t ∈ G(V) ↦ φ(s|_V ⊗ t)) ∈ Hom_{O_U}(G|_U, H|_U)`
(section pairing `tensorSections`); linearity, compatibility with restriction and naturality follow
from the bilinearity and restriction compatibility of the section pairing (`TensorSectionsBilinear`)
and the naturality of `φ`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.curryPresheafHom {X : AlgebraicGeometry.Scheme.{u}}
    (F G H : X.Modules) (φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) F G ⟶ H) :
    (SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj F ⟶
      AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H where
  app U := ModuleCat.ofHom (R := Γ(X, U.unop)) (X := Γ(F, U.unop))
      (Y := AlgebraicGeometry.Scheme.Modules.localHomSubmodule G H U.unop)
    { toFun := fun s => ⟨fun V =>
        { toFun := fun t => φ.val.app (Opposite.op V.left)
            (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left (F.presheaf.map V.hom.op s) t)
          map_add' := fun t t' => by
            rw [AlgebraicGeometry.Scheme.Modules.tensorSections_add_right, map_add]
            rfl
          map_smul' := fun r t =>
            AlgebraicGeometry.Scheme.Modules.curryPresheafHom_inner_map_smul φ s V r t _ rfl }, by
        intro V W i x
        dsimp only
        have hcomp : (F.presheaf.map V.hom.op) s
            = (F.presheaf.map i.left.op) ((F.presheaf.map W.hom.op) s) := by
          rw [show V.hom.op = W.hom.op ≫ i.left.op from by
            rw [← op_comp, show i.left ≫ W.hom = V.hom from CategoryTheory.Over.w i]]
          exact _root_.PresheafOfModules.map_comp_apply F.val W.hom.op i.left.op s
        have hφ := _root_.PresheafOfModules.naturality_apply φ.val i.left.op
          (AlgebraicGeometry.Scheme.Modules.tensorSections F G W.left
            (F.presheaf.map W.hom.op s) x)
        have hts := AlgebraicGeometry.Scheme.Modules.tensorSections_restrict F G i.left
          ((F.presheaf.map W.hom.op) s) x
        exact (congrArg (fun z => φ.val.app (Opposite.op V.left)
              (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left z
                ((G.presheaf.map i.left.op) x))) hcomp).trans
          ((congrArg (fun z => φ.val.app (Opposite.op V.left) z) hts.symm).trans hφ)⟩
      map_add' := fun s s' => Subtype.ext (funext fun V => LinearMap.ext fun t =>
        ((congrArg (fun z => φ.val.app (Opposite.op V.left)
              (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left z t))
            ((F.presheaf.map V.hom.op).hom.map_add s s')).trans
          ((congrArg (fun z => φ.val.app (Opposite.op V.left) z)
              (AlgebraicGeometry.Scheme.Modules.tensorSections_add_left F G V.left
                ((F.presheaf.map V.hom.op) s) ((F.presheaf.map V.hom.op) s') t)).trans
            ((φ.val.app (Opposite.op V.left)).hom.map_add _ _))))
      map_smul' := fun r s => Subtype.ext (funext fun V => LinearMap.ext fun t =>
        ((congrArg (fun z => φ.val.app (Opposite.op V.left)
              (AlgebraicGeometry.Scheme.Modules.tensorSections F G V.left z t))
            (AlgebraicGeometry.Scheme.Modules.map_smul F V.hom r s)).trans
          ((congrArg (fun z => φ.val.app (Opposite.op V.left) z)
              (AlgebraicGeometry.Scheme.Modules.tensorSections_smul_left F G V.left
                ((X.presheaf.map V.hom.op) r) ((F.presheaf.map V.hom.op) s) t _ rfl)).trans
            ((φ.val.app (Opposite.op V.left)).hom.map_smul _ _)))) }
  naturality := by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext W
    apply LinearMap.ext
    intro t
    exact (congrArg (fun z => (φ.val.app (Opposite.op W.left))
        (AlgebraicGeometry.Scheme.Modules.tensorSections F G W.left z t))
      (_root_.PresheafOfModules.map_comp_apply F.val f W.hom.op s)).symm

/-- Evaluation on the presheaf level `Hom(G, H) ⊗ G → H`: `(φ, t) ↦` the component of `φ` at `U` itself
applied to `t`; bilinearity from the linearity of `φ` and "restriction along `Over.mk (𝟙 U)` is the
identity", naturality from the compatibility of `φ` (between `Over.mk f` and `Over.mk (𝟙 U)`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.internalHomPresheafEval {X : AlgebraicGeometry.Scheme.{u}}
    (G H : X.Modules) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G) ⟶
      (SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj H where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (R := ((X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat).obj U : RingCat))
    (M₃ := ((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj H).obj U)
    (fun φ t => (φ.1 (CategoryTheory.Over.mk (𝟙 U.unop))) t)
    (fun _ _ _ => rfl)
    (fun a m n => by
      show ((X.presheaf.map (CategoryTheory.Over.mk (𝟙 U.unop)).hom.op) a) •
          ((m.1 (CategoryTheory.Over.mk (𝟙 U.unop))) n) = _
      rw [show ((CategoryTheory.Over.mk (𝟙 U.unop)).hom.op) = 𝟙 (Opposite.op U.unop) from rfl,
        X.presheaf.map_id]
      rfl)
    (fun m _ _ => (m.1 (CategoryTheory.Over.mk (𝟙 U.unop))).map_add _ _)
    (fun a m n => (m.1 (CategoryTheory.Over.mk (𝟙 U.unop))).map_smul a n)
  naturality := by
    intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro φ t
    exact φ.2 (CategoryTheory.Over.mk (𝟙 V.unop ≫ f.unop))
      (CategoryTheory.Over.mk (𝟙 U.unop)) (CategoryTheory.Over.homMk f.unop) t

/-- The evaluation morphism `𝓗om(G, H) ⊗ G ⟶ H`: `G ≅ L(G G)` (sheafification counit, invertible),
`μ : L Q ⊗ L P ≅ L(Q ⊗ P)`, then descend the presheaf evaluation along the sheafification adjunction. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.internalHomEval {X : AlgebraicGeometry.Scheme.{u}}
    (G H : X.Modules) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
      (AlgebraicGeometry.Scheme.Modules.internalHom G H) G ⟶ H :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  CategoryTheory.MonoidalCategoryStruct.whiskerLeft (C := X.Modules)
      (AlgebraicGeometry.Scheme.Modules.internalHom G H)
      ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app G) ≫
    (CategoryTheory.Localization.Monoidal.μ
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G)).hom ≫
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheafEval G H)

/-- Currying: pass from `Modules.tensor` to the monoidal `⊗`, curry openwise (`curryPresheafHom`), and
obtain a morphism of sheaves via `F ≅ L(G F)` and the sheafification functor. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorHomCurry {X : AlgebraicGeometry.Scheme.{u}}
    (F G H : X.Modules) (φ : AlgebraicGeometry.Scheme.Modules.tensor F G ⟶ H) :
    F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H :=
  (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app F ≫
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ))

/-- Uncurrying: `ψ ↦ (ψ ▷ G) ≫ ev`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorHomUncurry {X : AlgebraicGeometry.Scheme.{u}}
    (F G H : X.Modules) (ψ : F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :
    AlgebraicGeometry.Scheme.Modules.tensor F G ⟶ H :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).hom ≫
    CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) ψ G ≫
    AlgebraicGeometry.Scheme.Modules.internalHomEval G H

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}


/-- Section criterion for morphisms of sheaves: two morphisms `F ⊗ G ⟶ H` agreeing on all section
pairings `tensorSections F G U s t` are equal (`tensor F G = L(G F ⊗ G G)` is a sheafification; use the
sheafification adjunction and generation by pure tensors). -/
theorem tensorObj_hom_ext {F G H : X.Modules}
    {f g : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) F G ⟶ H}
    (h : ∀ (U : X.Opens) (s : Γ(F, U)) (t : Γ(G, U)),
      f.val.app (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections F G U s t) =
        g.val.app (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections F G U s t)) :
    f = g := by
  rw [← CategoryTheory.Iso.cancel_iso_hom_left (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G)]
  apply ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  apply _root_.PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

/-- The inverse of the sheafification counit is, on the presheaf level, the sheafification unit (right
triangle identity of the adjunction). -/
theorem forget_map_counit_inv (F : X.Modules) :
    (SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app F) =
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj F) := by
  have h2 : (SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app F) ≫
      (SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app F) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp,
      show ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app F ≫ (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app F) = 𝟙 _ from
        (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).hom_inv_id_app F]
    exact CategoryTheory.Functor.map_id _ _
  have h := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).right_triangle_components F
  have h3 := congrArg (fun k => k ≫ (SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
      ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app F)) h
  simp only [CategoryTheory.Category.assoc, h2, CategoryTheory.Category.id_comp] at h3
  exact h3.symm

/-- Sectionwise formula for currying: on sections, `tensorHomCurry` is the presheaf currying followed by
the sheafification unit. -/
theorem tensorHomCurry_val_app (F G H : X.Modules)
    (φ : AlgebraicGeometry.Scheme.Modules.tensor F G ⟶ H) (U : X.Opens) (s : Γ(F, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H φ).val.app (Opposite.op U) s =
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)).app (Opposite.op U)
        ((AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ)).app
            (Opposite.op U) s) := by
  have hcinv := congrArg (fun m => (_root_.PresheafOfModules.Hom.app m (Opposite.op U)) s)
    (AlgebraicGeometry.Scheme.Modules.forget_map_counit_inv F)
  have hnat := congrArg (fun m => (_root_.PresheafOfModules.Hom.app m (Opposite.op U)) s)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ)))
  simp only at hcinv hnat
  exact (congrArg (fun z => ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ))).val.app
          (Opposite.op U) z) hcinv).trans hnat.symm

/-- **The key step avoiding `μ`**: the value of `internalHomEval` on "image of the sheafification unit
`⊗` section" is the pure section computation "component of `χ` at `Over.mk (𝟙 U)` applied to `t`".

This eliminates `Localization.Monoidal.μ` (for which Mathlib provides naturality but no description of
values): the cancellation law `L(η ⊗ 𝟙) ≫ μ⁻¹ ≫ (ε ⊗ ε) ≫ (𝟙 ◁ ε⁻¹) ≫ μ = 𝟙` (`LocalizedDeltaCancel`)
shows that `L(η ⊗ 𝟙) ≫ sheafifyTensorTo ≫ internalHomEval` is exactly the adjoint transpose of the
presheaf evaluation. -/
theorem internalHomEval_tensorSections_unit (G H : X.Modules) (U : X.Opens)
    (χ : (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H).obj (Opposite.op U)) (t : Γ(G, U)) :
    (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app (Opposite.op U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (AlgebraicGeometry.Scheme.Modules.internalHom G H) G U
          (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)).app (Opposite.op U) χ) t)
      = (χ.1 (CategoryTheory.Over.mk (𝟙 U))) t := by
  have := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  have : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  have hdc := CategoryTheory.Localization.Monoidal.map_tensorHom_id_comp_μ_cancel (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (AlgebraicGeometry.Scheme.Modules.internalHom G H))
    ((CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app G)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components _)
  have h1 := congrArg (fun k => k.val.app (Opposite.op U)
      (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)
        ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G))).app (Opposite.op U) (TensorProduct.tmul _ χ t))) hdc
  have hnat := congrArg (fun m => (_root_.PresheafOfModules.Hom.app m (Opposite.op U))
      (show ↑((CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G)).obj (Opposite.op U)) from TensorProduct.tmul _ χ t))
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality (CategoryTheory.MonoidalCategoryStruct.tensorHom
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) (𝟙 ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G))))
  have h5 := congrArg (fun m => (_root_.PresheafOfModules.Hom.app m (Opposite.op U))
      (show ↑((CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G)).obj (Opposite.op U)) from TensorProduct.tmul _ χ t))
    (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).apply_symm_apply
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheafEval G H))
  simp only at h1 hnat h5
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op U) ((AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo
        (AlgebraicGeometry.Scheme.Modules.internalHom G H) G).val.app (Opposite.op U) z)) hnat).trans
    ((congrArg (fun z => (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm (AlgebraicGeometry.Scheme.Modules.internalHomPresheafEval G H)).val.app (Opposite.op U) z) h1).trans h5)

/-- The presheaf currying `c₀ : G(𝓗om(G,H)) ⟶ 𝓗om-presheaf` of the evaluation morphism. -/
noncomputable def internalHomEvalCurry (G H : X.Modules) :
    (SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ⟶ (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) :=
  AlgebraicGeometry.Scheme.Modules.curryPresheafHom
    (AlgebraicGeometry.Scheme.Modules.internalHom G H) G H
    (AlgebraicGeometry.Scheme.Modules.internalHomEval G H)

/-- `η ≫ c₀ = 𝟙`: a section of `internalHomPresheaf` sent through the sheafification unit and then the
curried evaluation comes back to itself. -/
theorem unit_comp_internalHomEvalCurry (G H : X.Modules) :
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) ≫
      AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H = 𝟙 _ := by
  apply _root_.PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro χ
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro t
  have hnat := _root_.PresheafOfModules.naturality_apply
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) V.hom.op χ
  exact ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op V.left) (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.internalHom G H) G V.left z t)) hnat).symm).trans
    (AlgebraicGeometry.Scheme.Modules.internalHomEval_tensorSections_unit G H V.left
      ((AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H).map V.hom.op χ) t)

/-- `c₀ ≫ η = 𝟙`: hence `internalHomPresheaf G H` is already a sheaf (`η` is an isomorphism).

No direct verification of the sheaf condition is needed: from `η ≫ c₀ = 𝟙` we get `L η ≫ L c₀ = 𝟙`,
the left triangle identity gives `L η ≫ ε = 𝟙` with `ε` invertible, so `L η = ε⁻¹` and `L c₀ = ε`;
injectivity of `homEquiv.symm k = L k ≫ ε` gives `c₀ ≫ η = 𝟙`. -/
theorem internalHomEvalCurry_comp_unit (G H : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H ≫
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) = 𝟙 _ := by
  show AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H ≫
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H) = 𝟙 ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)))
  have hiso : CategoryTheory.IsIso ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))) :=
    ⟨⟨(CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)),
      (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).hom_inv_id_app _,
      (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).inv_hom_id_app _⟩⟩
  have h1 : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ≫
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H) = 𝟙 _ :=
    ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_comp _ _).symm.trans
      ((congrArg (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (AlgebraicGeometry.Scheme.Modules.unit_comp_internalHomEvalCurry G H)).trans
          ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _))
  have h2 := (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)
  have hα : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) =
      CategoryTheory.inv ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))) :=
    CategoryTheory.IsIso.eq_inv_of_inv_hom_id h2
  have h3 : (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ≫ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) = 𝟙 _ :=
    (congrArg (fun k => (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ≫ k) hα).trans
      (CategoryTheory.IsIso.hom_inv_id _)
  have h4 : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H) =
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) :=
    (CategoryTheory.Category.id_comp _).symm.trans
      ((congrArg (fun k => k ≫ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H)) h3.symm).trans
        ((CategoryTheory.Category.assoc _ _ _).trans
          ((congrArg (fun k => (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ≫ k) h1).trans
            (CategoryTheory.Category.comp_id _))))
  have h5 : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H ≫
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) = (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (𝟙 ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)))) :=
    ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_comp _ _).trans
      ((congrArg (fun k => k ≫ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))) h4).trans
        ((congrArg (fun k => (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)) ≫ k) hα).trans
          ((CategoryTheory.IsIso.hom_inv_id _).trans ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _).symm)))
  apply (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv ((SheafOfModules.forget X.ringCatSheaf ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))) ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H))).symm).injective
  rw [CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.Adjunction.homEquiv_counit, h5]


/-- Presheaf-level formula for currying after uncurrying: `curryPresheafHom F G H (uncurry ψ) = G ψ ≫ c₀`
(sectionwise). -/
theorem curryPresheafHom_tensorHomUncurry (F G H : X.Modules)
    (ψ : F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) (U : X.Opens) (s : Γ(F, U)) :
    (AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫
          AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H ψ)).app (Opposite.op U) s =
      (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry G H).app (Opposite.op U)
        (ψ.val.app (Opposite.op U) s) := by
  rw [show (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫
      AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H ψ =
      CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) ψ (𝟙 G) ≫
        AlgebraicGeometry.Scheme.Modules.internalHomEval G H from by
    rw [CategoryTheory.MonoidalCategory.tensorHom_id]
    exact (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv_hom_id_assoc _]
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro t
  have hts := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections ψ (𝟙 G) V.left
    ((F.presheaf.map V.hom.op) s) t
  have hnat := _root_.PresheafOfModules.naturality_apply ψ.val V.hom.op s
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op V.left) z) hts).trans
    (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op V.left) (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.internalHom G H) G V.left z t)) hnat)

end AlgebraicGeometry.Scheme.Modules

/-- Stacks 01CM, first inverse law: currying after uncurrying gives back the original morphism.

Proof: both sides are morphisms `tensor F G ⟶ H`, and `tensor F G = L(G F ⊗ G G)` is a
sheafification, so by the sheafification adjunction (`PresheafOfModules.sheafificationAdjunction`) a
morphism of sheaves is determined by its composite with the sheafification unit (a presheaf morphism
`G F ⊗ G G ⟶ G H`); by `ModuleCat.MonoidalCategory.tensor_ext` the latter is determined by its values
on pure tensors `s ⊗ₜ t`. So it suffices to check, for every open `U`, `s ∈ Γ(F,U)`, `t ∈ Γ(G,U)`,
  `(tensorHomUncurry F G H (tensorHomCurry F G H φ)).val.app U (tensorSections F G U s t)
     = φ.val.app U (tensorSections F G U s t)`.
The right side is, by definition of `curryPresheafHom`, `φ` applied to `s|_U ⊗ t`
(i.e. `tensorSections F G U s t`). On the left, `whiskerRight ψ G` sends `s ⊗ t` to `ψ(s) ⊗ t`, and
`internalHomEval_tensorSections_unit` evaluates the result as the component of `ψ(s)` at
`Over.mk (𝟙 U)` applied to `t`, which by definition of `curryPresheafHom` is
`φ(tensorSections F G U s t)`. -/

theorem AlgebraicGeometry.Scheme.Modules.tensorHomUncurry_tensorHomCurry
    {X : AlgebraicGeometry.Scheme.{u}} (F G H : X.Modules)
    (φ : AlgebraicGeometry.Scheme.Modules.tensor F G ⟶ H) :
    AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H
        (AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H φ) = φ := by

  rw [← CategoryTheory.Iso.cancel_iso_inv_left
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G),
    show (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫
      AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H
        (AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H φ) =
      CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H φ) (𝟙 G) ≫
        AlgebraicGeometry.Scheme.Modules.internalHomEval G H from by
      rw [CategoryTheory.MonoidalCategory.tensorHom_id]
      exact (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv_hom_id_assoc _]
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
  intro U s t
  have h1 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H φ) (𝟙 G) U s t
  have h2 := AlgebraicGeometry.Scheme.Modules.tensorHomCurry_val_app F G H φ U s
  have h3 := AlgebraicGeometry.Scheme.Modules.internalHomEval_tensorSections_unit G H U
    ((AlgebraicGeometry.Scheme.Modules.curryPresheafHom F G H
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ)).app (Opposite.op U) s) t
  have hid : (F.presheaf.map (𝟙 U).op) s = s := by simp
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op U) z) h1).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.internalHomEval G H).val.app
      (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.internalHom G H) G U z t)) h2).trans ?_
  refine h3.trans ?_
  exact congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).inv ≫ φ).val.app
    (Opposite.op U) (AlgebraicGeometry.Scheme.Modules.tensorSections F G U z t)) hid

/-- Stacks 01CM, second inverse law: uncurrying after currying gives back the original morphism.

Proof: both sides are morphisms `F ⟶ internalHom G H = L(internalHomPresheaf G H)`. By the
sheafification adjunction, `Hom(F, L P) ≃ Hom(G F, P)` (`sheafificationAdjunction.homEquiv` and the
counit isomorphism), so it suffices to compare on the presheaf level: for every `U` and
`s ∈ Γ(F,U)`, both sides give the same element of `localHomSubmodule G H U`; the latter is a compatible
family over `Over U`, determined by its values at every `V ≤ U` and `t ∈ Γ(G,V)`. The value given by
`curryPresheafHom` is `(tensorHomUncurry F G H ψ)(s|_V ⊗ t)`, which by definition of `tensorHomUncurry`
is the component of `ψ(s)|_V` at `Over.mk (𝟙 V)` applied to `t`; by the restriction map
`localHomRestrict` of `internalHomPresheaf` (the component of `ψ(s)|_V` at `Over.mk (𝟙 V)` is the
component of `ψ(s)` at `Over.mk (V ⟶ U)`) this agrees with the component of `ψ(s)` at `V`. The last
step, that `ψ(s)` lies in the image of the sheafification unit, is `internalHomEvalCurry_comp_unit`
(`internalHomPresheaf` is a sheaf). -/

theorem AlgebraicGeometry.Scheme.Modules.tensorHomCurry_tensorHomUncurry
    {X : AlgebraicGeometry.Scheme.{u}} (F G H : X.Modules)
    (ψ : F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :
    AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H
        (AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H ψ) = ψ := by

  apply _root_.SheafOfModules.Hom.ext
  apply _root_.PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have h2 := AlgebraicGeometry.Scheme.Modules.tensorHomCurry_val_app F G H
    (AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H ψ) U.unop s
  have hD := AlgebraicGeometry.Scheme.Modules.curryPresheafHom_tensorHomUncurry F G H ψ U.unop s
  have hC := congrArg (fun m => (_root_.PresheafOfModules.Hom.app m U)
      (ψ.val.app U s))
    (AlgebraicGeometry.Scheme.Modules.internalHomEvalCurry_comp_unit G H)
  simp only at hC
  exact h2.trans ((congrArg (fun z =>
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G H)).app U z) hD).trans hC)

/-- Stacks 01CM: `Hom(F ⊗ G, H) ≃ Hom(F, 𝓗om(G, H))`. Forward: pass from `Modules.tensor` to the monoidal
`⊗`, curry openwise (`curryPresheafHom`), and use `F ≅ L(G F)` and the sheafification functor;
backward: `ψ ↦ (ψ ▷ G) ≫ ev`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorHomEquiv {X : AlgebraicGeometry.Scheme.{u}}
    (F G H : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.tensor F G ⟶ H) ≃
      (F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) where
  toFun := AlgebraicGeometry.Scheme.Modules.tensorHomCurry F G H
  invFun := AlgebraicGeometry.Scheme.Modules.tensorHomUncurry F G H
  left_inv := AlgebraicGeometry.Scheme.Modules.tensorHomUncurry_tensorHomCurry F G H
  right_inv := AlgebraicGeometry.Scheme.Modules.tensorHomCurry_tensorHomUncurry F G H

end
