import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebra

/-! # Functoriality of the pushforward algebra in morphisms, and multiplication by global functions

Functoriality in **morphisms** of the pushforward algebra `f_*O_T` of an affine morphism
(`QCAlgebra.pushforwardStructureSheaf`, the object part of Stacks 01S5), and the basic properties of a
global function `a ∈ Γ(X, O_X)` as the endomorphism `unitMul a` of `O_X`.

* `pushforwardStructureSheaf.unitMap g π : π_*O_T ⟶ (g ≫ π)_*O_W` (`g^♯` pushed forward along `π`, then
  `π_*g_* ≅ (g ≫ π)_*`);
* it preserves the unit (`unitToPushforwardObjUnit_comp_pushforward_map`) and the multiplication
  (`mul_comp_unitMap`, the morphism part of Stacks 01S5);
* `pushforwardCongr` is compatible with unit and multiplication (after `subst` it is the identity);
* `unitMul 1 = 𝟙`; `mul` is bilinear with respect to `unitMul` (`unitMul_tensor_comp_mul`).

Both multiplication identities are reduced to the presheaf level by the **transport lemma**
`tensorHom_comp_mul_eq_mul_comp`: `mul f = (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m_f) ≫ e`, and for morphisms of sheaves
`φ ψ χ`, if `(Gφ ⊗ Gψ) ≫ m_{f'} = m_f ≫ Gχ` (`G = forget ⋙ restrictScalars 𝟙` is the right adjoint of the
sheafification `L`), then `(φ ⊗ ψ) ≫ mul f' = mul f ≫ χ`. The transport uses only the naturality of the
counit `e` (`counitIso_hom_comp`) and the naturality of `μ` in `⊗ₘ`
(`Modules.sheafification_map_tensorHom_comp_μ`, assembled from Mathlib's `μ_natural_left/right`); no
general "sheafification sends presheaf monoids to sheaf monoids" lemma is needed. At the presheaf level,
`PresheafOfModules.hom_ext` + `ModuleCat.MonoidalCategory.tensor_ext` reduce to pure tensors, where the
identities are `map_mul` (`g^♯` is a ring homomorphism) and `mul_mul_mul_comm`.

Reference: Stacks 01S5 (morphisms-lemma-affine-equivalence-algebras); used by the grading construction
of the jet algebra (`GroupSchemeAction.weightPart_mul_condition`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- A global function `a ∈ Γ(X, O_X)` as the endomorphism `x ↦ a·x` of the structure sheaf (as a module over
itself): the morphism corresponding to `a` (restricted to each open) under `Hom(O_X, O_X) ≃ Γ(O_X)`
(Mathlib `unitHomEquiv`), `1 ↦ a`. The family of sections `U ↦ res^⊤_U a` is compatible with restriction
by functoriality of `X.presheaf` and since the hom-sets of `Opensᵒᵖ` are subsingletons. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.unitMul {X : AlgebraicGeometry.Scheme.{u}}
    (a : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unitHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
    (_root_.PresheafOfModules.sectionsMk
      (fun U => (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom a)
      (fun {U V} f => by
        show (X.presheaf.map f).hom
            ((X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom a) = _
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
        congr 1))

/-- `unitMul 1 = 𝟙`: the global function `1` as an endomorphism of `O_X` is the identity (under
`unitHomEquiv` both sides correspond to the family `U ↦ 1`). -/
theorem AlgebraicGeometry.Scheme.Modules.unitMul_one {X : AlgebraicGeometry.Scheme.{u}} :
    AlgebraicGeometry.Scheme.Modules.unitMul (X := X) (1 : Γ(X, ⊤)) = 𝟙 _ := by
  unfold AlgebraicGeometry.Scheme.Modules.unitMul
  rw [Equiv.symm_apply_eq]
  ext U
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  show (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom 1 = 1
  exact map_one _

set_option backward.isDefEq.respectTransparency.types false in
/-- The components of `pushforwardCongr rfl` are identities. -/
theorem AlgebraicGeometry.Scheme.Modules.pushforwardCongr_rfl_hom_app
    {W Y : AlgebraicGeometry.Scheme.{u}} (f : W ⟶ Y) (M : W.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.Hom.id_app, CategoryTheory.eqToHom_refl,
    CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport of the unit along an equality of morphisms: `unit_f ≫ pushforwardCongr h = unit_g`. -/
theorem SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr
    {W Y : AlgebraicGeometry.Scheme.{u}} {f g : W ⟶ Y} (h : f = g) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit W.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  subst h
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardCongr_rfl_hom_app]
  exact CategoryTheory.Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport of the multiplication along an equality of morphisms:
`mul_f ≫ pushforwardCongr h = (pushforwardCongr h ⊗ pushforwardCongr h) ≫ mul_g`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comp_pushforwardCongr
    {W Y : AlgebraicGeometry.Scheme.{u}} {f g : W ⟶ Y} (h : f = g) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit W.ringCatSheaf) =
      ((AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit W.ringCatSheaf) ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit W.ringCatSheaf)) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul g := by
  subst h
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardCongr_rfl_hom_app,
    CategoryTheory.MonoidalCategory.id_tensorHom_id, CategoryTheory.Category.id_comp]
  exact CategoryTheory.Category.comp_id _

/-- The morphism of algebra sheaves `g^♯ : π_*O_T ⟶ (g ≫ π)_*O_W` given by pushing `g : W ⟶ T` forward along
`π : T ⟶ S` (the morphism part of Stacks 01S5, "affine morphisms ↦ algebra sheaves"):
`π_*(unit O_T → g_*O_W)` followed by `π_*g_* ≅ (g ≫ π)_*`. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap
    {W T S : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) (π : T ⟶ S) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj π ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj (g ≫ π) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward π).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp g π).hom.app (SheafOfModules.unit W.ringCatSheaf)

set_option backward.isDefEq.respectTransparency.types false in
/-- `g^♯` preserves the unit: `unit_π ≫ π_*(unit_g) ≫ pushforwardComp = unit_{g ≫ π}` (both sides send `1` to
`1`). -/
theorem SheafOfModules.unitToPushforwardObjUnit_comp_pushforward_map
    {W T S : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) (π : T ⟶ S) :
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward π).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp g π).hom.app (SheafOfModules.unit W.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (g ≫ π).toRingCatSheafHom := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext X
  show ((g.app (π ⁻¹ᵁ X.unop)).hom ((π.app X.unop).hom 1)) = ((g ≫ π).app X.unop).hom 1
  rw [map_one, map_one, map_one]
  rfl

/-- The same, written with `unitMap`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.one_comp_unitMap
    {W T S : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) (π : T ⟶ S) :
    SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π =
      SheafOfModules.unitToPushforwardObjUnit (g ≫ π).toRingCatSheafHom :=
  SheafOfModules.unitToPushforwardObjUnit_comp_pushforward_map g π


/-! ### Transport through sheafification: reducing identities for `mul` to the presheaf level

`mul f = (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m_f) ≫ e`. For morphisms of sheaves `φ ψ χ : f_*O_T ⟶ f'_*O_{T'}`, if at the
presheaf level `(Gφ ⊗ Gψ) ≫ m_{f'} = m_f ≫ Gχ` (`G = forget ⋙ restrictScalars 𝟙` is the right adjoint of
sheafification), then `(φ ⊗ ψ) ≫ mul f' = mul f ≫ χ`. The proof uses only the naturality of the counit and
of `μ` (`μ_natural_left/right`); no general "sheafification preserves monoid objects" lemma is needed. -/

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the counit isomorphism `e`: `e_f ≫ φ = L(Gφ) ≫ e_{f'}`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso_hom_comp
    {X T T' : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (f' : T' ⟶ X)
    (φ : AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f') :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f).hom ≫ φ =
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ) ≫
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f').hom :=
  ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality φ).symm

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the counit isomorphism `e` (inverse direction): `φ ≫ e_{f'}⁻¹ = e_f⁻¹ ≫ L(Gφ)`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.comp_counitIso_inv
    {X T T' : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (f' : T' ⟶ X)
    (φ : AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f') :
    φ ≫ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f').inv =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f).inv ≫
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ) := by
  rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc,
    ← AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso_hom_comp,
    CategoryTheory.Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison isomorphism `μ` of the localized monoidal structure in `⊗ₘ`:
`(L a ⊗ L b) ≫ μ = μ ≫ L(a ⊗ b)` (from Mathlib's `μ_natural_left`, `μ_natural_right` and `tensorHom_def`). -/
@[reassoc]
theorem AlgebraicGeometry.Scheme.Modules.sheafification_map_tensorHom_comp_μ
    (X : AlgebraicGeometry.Scheme.{u})
    {P₁ P₂ Q₁ Q₂ : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj} (a : P₁ ⟶ Q₁) (b : P₂ ⟶ Q₂) :
    haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
    haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
        ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
          (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
    (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a)
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map b)) ≫
      (CategoryTheory.Localization.Monoidal.μ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
          (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) Q₁ Q₂).hom =
    (CategoryTheory.Localization.Monoidal.μ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
          (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
        (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) P₁ P₂).hom ≫
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (a ⊗ₘ b) := by
  rw [CategoryTheory.MonoidalCategory.tensorHom_def, CategoryTheory.MonoidalCategory.tensorHom_def,
    CategoryTheory.Functor.map_comp, CategoryTheory.Category.assoc]
  erw [CategoryTheory.Localization.Monoidal.μ_natural_right,
    CategoryTheory.Localization.Monoidal.μ_natural_left_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Transport lemma**: identities for `mul` reduce to the presheaf level. If `(Gφ ⊗ Gψ) ≫ m_{f'} = m_f ≫ Gχ`,
then `(φ ⊗ ψ) ≫ mul f' = mul f ≫ χ`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.tensorHom_comp_mul_eq_mul_comp
    {X T T' : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (f' : T' ⟶ X)
    (φ ψ χ : AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f')
    (h : ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ ⊗ₘ
          (SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map ψ) ≫
          AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f' =
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f ≫
          (SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map χ) :
    (φ ⊗ₘ ψ) ≫ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f' =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f ≫ χ := by
  unfold AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul
  rw [CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.comp_counitIso_inv,
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.comp_counitIso_inv,
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    AlgebraicGeometry.Scheme.Modules.sheafification_map_tensorHom_comp_μ_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp_assoc]
  simp only [CategoryTheory.Category.assoc]
  rw [AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso_hom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **Presheaf level** (the core of the morphism part of Stacks 01S5): on each open, `g^♯` is the ring
homomorphism `g.app (π⁻¹U)`, so `m_π ≫ G g^♯ = (G g^♯ ⊗ G g^♯) ≫ m_{g ≫ π}` (after `tensor_ext` reduces to pure
tensors this is `map_mul`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul_comp_forget_map_unitMap
    {W T S : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) (π : T ⟶ S) :
    ((SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π) ⊗ₘ
        (SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π)) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul (g ≫ π) =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul π ≫
        (SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π) := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  show (g.app (π ⁻¹ᵁ U.unop)).hom (show Γ(T, π ⁻¹ᵁ U.unop) from x) *
      (g.app (π ⁻¹ᵁ U.unop)).hom (show Γ(T, π ⁻¹ᵁ U.unop) from y) =
    (g.app (π ⁻¹ᵁ U.unop)).hom ((show Γ(T, π ⁻¹ᵁ U.unop) from x) * (show Γ(T, π ⁻¹ᵁ U.unop) from y))
  exact (map_mul _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Presheaf level**: on each open `U`, `f_*(unitMul a)` is multiplication by `a|_{f⁻¹U}` on `Γ(W, f⁻¹U)`, so
`(G f_*(a·) ⊗ G f_*(b·)) ≫ m_f = m_f ≫ G f_*((ab)·)` (on pure tensors this is `mul_mul_mul_comm`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.forget_map_unitMul_tensor_comp_presheafMul
    {W S : AlgebraicGeometry.Scheme.{u}} (f : W ⟶ S) (a b : Γ(W, ⊤)) :
    ((SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul a)) ⊗ₘ
        (SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul b))) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f ≫
        (SheafOfModules.forget S.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 S.ringCatSheaf.obj)).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul (a * b))) := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  show ((show Γ(W, f ⁻¹ᵁ U.unop) from x) *
        (W.presheaf.map (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ U.unop ≤ ⊤)).op).hom a) *
      ((show Γ(W, f ⁻¹ᵁ U.unop) from y) *
        (W.presheaf.map (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ U.unop ≤ ⊤)).op).hom b) =
    ((show Γ(W, f ⁻¹ᵁ U.unop) from x) * (show Γ(W, f ⁻¹ᵁ U.unop) from y)) *
      (W.presheaf.map (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ U.unop ≤ ⊤)).op).hom (a * b)
  rw [map_mul]
  exact mul_mul_mul_comm _ _ _ _

/-- (The morphism part of Stacks 01S5.) `g^♯ : π_*O_T ⟶ (g ≫ π)_*O_W` preserves multiplication:
`mul_π ≫ g^♯ = (g^♯ ⊗ g^♯) ≫ mul_{g ≫ π}`.

Proof: `mul_π` is defined as `(e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m_π) ≫ e` (`pushforwardStructureSheaf.mul`: `L` the
sheafification functor, `μ` the comparison isomorphism of the localized monoidal structure, `e` the counit
isomorphism, `m_π` the presheaf multiplication `presheafMul`, which on an open `U` is the ring
multiplication of `Γ(T, π⁻¹U)`). At the presheaf level, `g^♯` is on each open `U` the ring homomorphism
`g.app (π⁻¹U) : Γ(T, π⁻¹U) → Γ(W, g⁻¹π⁻¹U) = Γ(W, (g ≫ π)⁻¹U)` (`pushforward_map_app`,
`pushforwardComp_hom_app_app` is `𝟙`, `unitToPushforwardObjUnit_val_app_apply`, all by definition).
1. Presheaf level (`presheafMul_comp_forget_map_unitMap`): `(G g^♯ ⊗ G g^♯) ≫ m_{g ≫ π} = m_π ≫ G g^♯`; on each
   open, `PresheafOfModules.hom_ext` + `ModuleCat.MonoidalCategory.tensor_ext` reduce to pure tensors
   `a ⊗ₜ b`: the left side is `g^♯(a)·g^♯(b)`, the right side `g^♯(a·b)`, equal since `g.app _` is a ring
   homomorphism (`map_mul`).
2. Sheaf level (transport lemma `tensorHom_comp_mul_eq_mul_comp` with `φ = ψ = χ = g^♯`): naturality of the
   counit `e` writes `g^♯` as `e⁻¹ ≫ L(G g^♯) ≫ e`, and naturality of `μ` in `⊗ₘ`
   (`sheafification_map_tensorHom_comp_μ`) transports the identity of step 1 to `mul`.

Edge cases: for `g = 𝟙`, `unitMap` is a component of `π_*(𝟙 ≅)` and both sides are identities; for `W`
empty, `(g ≫ π)_*O_W = 0` and both sides are `0`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comp_unitMap
    {W T S : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) (π : T ⟶ S) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul π ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π ⊗ₘ
          AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap g π) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul (g ≫ π) :=
  (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.tensorHom_comp_mul_eq_mul_comp π (g ≫ π)
    _ _ _ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul_comp_forget_map_unitMap g π)).symm

/-- The multiplication of `f_*O_W` is bilinear with respect to multiplication by global functions `unitMul`:
`(f_*(a·) ⊗ f_*(b·)) ≫ mul_f = mul_f ≫ f_*((a·b)·)` for `a, b ∈ Γ(W, O_W)`.

Proof: on an open `U`, `f_*(unitMul a)` is "multiplication by `a|_{f⁻¹U}`" on `Γ(W, f⁻¹U)`
(`pushforward_map_app` + the definition of `unitMul`: `unitHomEquiv.symm` takes on `1` the family
`U ↦ res a`, so as an `O_W`-linear endomorphism it is `x ↦ x·(res a)`, by definition). At the presheaf level
(`forget_map_unitMul_tensor_comp_presheafMul`), `hom_ext` + `tensor_ext` reduce to pure tensors `x ⊗ₜ y`: the
left side is `(x·res a)(y·res b)`, the right side `(xy)·res(ab) = (xy)(res a · res b)` (`map_mul`), equal in a
commutative ring (`mul_mul_mul_comm`). At the sheaf level, apply the transport lemma
`tensorHom_comp_mul_eq_mul_comp` (`φ = f_*(a·)`, `ψ = f_*(b·)`, `χ = f_*((ab)·)`).

Edge case: for `a = b = 1` both sides are `mul_f` (`unitMul_one`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMul_tensor_comp_mul
    {W S : AlgebraicGeometry.Scheme.{u}} (f : W ⟶ S) (a b : Γ(W, ⊤)) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul a) ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul b)) ≫
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f =
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward f).map (AlgebraicGeometry.Scheme.Modules.unitMul (a * b)) :=
  AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.tensorHom_comp_mul_eq_mul_comp f f _ _ _
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.forget_map_unitMul_tensor_comp_presheafMul f a b)

end
