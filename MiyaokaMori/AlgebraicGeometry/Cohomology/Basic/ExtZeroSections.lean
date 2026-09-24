import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sx
import MiyaokaMori.CategoryTheory.ExtActionMayerVietoris

/-! # Degree-`0` cohomology of an object of a site is sections

**Degree-0 cohomology of an object of a site is sections, additively and naturally.**
For an abelian sheaf `F` on a site `(C, J)` and `U : C`, `Ext(ℤ[h_U]^#, F, 0) ≃+ F(U)`, where
`ℤ[h_U]^# = Stacks09sxAux.freeSheaf J U` is the free abelian sheaf on the representable presheaf of
`U` (the first variable of Mathlib's `Sheaf.H'`). The equivalence sends `x` to
`(Ext.addEquiv₀ x).hom.app (op U) (gen U)`, where `gen U = toSheafify (FreeAbelianGroup.of (𝟙 U))` is
the canonical generator; it is
* natural in `U` (`ext₀SectionsAddEquiv_precomp`): precomposition with `ℤ[h_W]^# → ℤ[h_U]^#`
  corresponds to the restriction `F(U) → F(W)`;
* natural in `F` (`ext₀SectionsAddEquiv_postcomp`): postcomposition with `μ : F ⟶ F'` corresponds to
  `μ.hom.app (op U)`.

With a ring action `[ExtAction R F]`, `F(U)` becomes an
`R`-module (`ExtAction.sectionsModule`, `r • s = (μ r).hom.app (op U) s`), the equivalence is
`R`-linear (`ext₀SectionsLinearEquiv`), restriction of sections is `R`-linear (`sectionsRes`) and
corresponds to `precompLinear`; hence a localization property of the restriction of sections in
degree `0` transfers to `precompLinear` (`isLocalizedModule_precompLinear_zero_of_sections`).

**Proof.** `Ext(-, -, 0) = Hom` (`Ext.homEquiv₀`, `Ext.addEquiv₀`), and
`Hom(ℤ[h_U]^#, F) ≃ F(U)` is `Stacks09sxAux.sectionsEquiv` (sheafification
adjunction, free–forgetful adjunction, Yoneda), which is *definitionally* evaluation at `gen U`
(`sectionsEquiv_apply_eq`). Additivity: evaluation of a sum of morphisms is the sum. Naturality in `U`:
`freeSheafMap m` maps `gen W` to the restriction of `gen U` (naturality of `toSheafify` and of the
free-abelian-group functor), then naturality of `φ.hom`. Naturality in `F`: composition. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace Stacks09sxAux

open CategoryTheory.Abelian

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]

/-- The presheaf `ℤ[h_U]` (free abelian presheaf on the representable presheaf of `U`). -/
abbrev freePresheaf (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).obj (yoneda.obj U)

/-- The canonical generator of `ℤ[h_U]^#` over `U`: the image of `𝟙 U`. -/
def gen (U : C) : (freeSheaf J U).obj.obj (op U) :=
  (toSheafify J (freePresheaf U)).app (op U) (FreeAbelianGroup.of (𝟙 U))

theorem sectionsEquiv_apply_eq (U : C) (F : Sheaf J AddCommGrpCat.{u}) (φ : freeSheaf J U ⟶ F) :
    sectionsEquiv U F φ = φ.hom.app (op U) (gen (J := J) U) := rfl

/-- `freeSheafMap m` sends `gen W` to the restriction of `gen U`. -/
theorem freeSheafMap_gen {W U : C} (m : W ⟶ U) :
    (freeSheafMap (J := J) m).hom.app (op W) (gen (J := J) W) =
      (freeSheaf J U).obj.map m.op (gen (J := J) U) := by
  let η : freePresheaf W ⟶ freePresheaf U :=
    ((Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free).map (yoneda.map m)
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J η) (op W))
    (FreeAbelianGroup.of (𝟙 W))
  have h2 := ConcreteCategory.congr_hom ((toSheafify J (freePresheaf U)).naturality m.op)
    (FreeAbelianGroup.of (𝟙 U))
  simp only [NatTrans.comp_app] at h1
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h1
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2
  show (sheafifyMap J η).app (op W) ((toSheafify J (freePresheaf W)).app (op W) (FreeAbelianGroup.of (𝟙 W))) =
    (sheafify J (freePresheaf U)).map m.op
      ((toSheafify J (freePresheaf U)).app (op U) (FreeAbelianGroup.of (𝟙 U)))
  rw [← h1, ← h2]
  congr 1
  show FreeAbelianGroup.map (fun g : W ⟶ W => g ≫ m) (FreeAbelianGroup.of (𝟙 W)) =
    FreeAbelianGroup.map (fun g : U ⟶ U => m ≫ g) (FreeAbelianGroup.of (𝟙 U))
  rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.map_of_apply, Category.id_comp, Category.comp_id]

variable (U : C) (F : Sheaf J AddCommGrpCat.{u}) [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- `Ext(ℤ[h_U]^#, F, 0) ≃+ F(U)`, evaluation at the canonical generator. -/
def ext₀SectionsAddEquiv : Ext (freeSheaf J U) F 0 ≃+ F.obj.obj (op U) where
  toFun x := (Ext.homEquiv₀ x).hom.app (op U) (gen (J := J) U)
  invFun s := Ext.mk₀ ((sectionsEquiv U F).symm s)
  left_inv x := by
    show Ext.mk₀ ((sectionsEquiv U F).symm ((Ext.homEquiv₀ x).hom.app (op U) (gen (J := J) U))) = x
    rw [← sectionsEquiv_apply_eq, Equiv.symm_apply_apply, Ext.mk₀_homEquiv₀_apply]
  right_inv s := by
    have : Ext.homEquiv₀ (Ext.mk₀ ((sectionsEquiv U F).symm s)) = (sectionsEquiv U F).symm s := by
      rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]
    show (Ext.homEquiv₀ (Ext.mk₀ ((sectionsEquiv U F).symm s))).hom.app (op U) (gen (J := J) U) = s
    rw [this, ← sectionsEquiv_apply_eq, Equiv.apply_symm_apply]
  map_add' x y := by
    show (Ext.addEquiv₀ (x + y)).hom.app (op U) (gen (J := J) U) =
      (Ext.addEquiv₀ x).hom.app (op U) (gen (J := J) U) + (Ext.addEquiv₀ y).hom.app (op U) (gen (J := J) U)
    rw [map_add]
    simp

theorem ext₀SectionsAddEquiv_apply (x : Ext (freeSheaf J U) F 0) :
    ext₀SectionsAddEquiv U F x = (Ext.homEquiv₀ x).hom.app (op U) (gen (J := J) U) := rfl

theorem homEquiv₀_mk₀_comp {A B : Sheaf J AddCommGrpCat.{u}} (f : B ⟶ A) (x : Ext A F 0) :
    Ext.homEquiv₀ ((Ext.mk₀ f).comp x (zero_add 0)) = f ≫ Ext.homEquiv₀ x := by
  conv_lhs => rw [← Ext.mk₀_homEquiv₀_apply x, Ext.mk₀_comp_mk₀]
  rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv₀_comp_mk₀ {A : Sheaf J AddCommGrpCat.{u}} {F' : Sheaf J AddCommGrpCat.{u}}
    (μ : F ⟶ F') (x : Ext A F 0) :
    Ext.homEquiv₀ (x.comp (Ext.mk₀ μ) (add_zero 0)) = Ext.homEquiv₀ x ≫ μ := by
  conv_lhs => rw [← Ext.mk₀_homEquiv₀_apply x, Ext.mk₀_comp_mk₀]
  rw [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]

/-- Naturality in `U`: precomposition with `ℤ[h_W]^# → ℤ[h_U]^#` is restriction of sections. -/
theorem ext₀SectionsAddEquiv_precomp {W : C} (m : W ⟶ U) (x : Ext (freeSheaf J U) F 0) :
    ext₀SectionsAddEquiv W F ((Ext.mk₀ (freeSheafMap (J := J) m)).comp x (zero_add 0)) =
      F.obj.map m.op (ext₀SectionsAddEquiv U F x) := by
  rw [ext₀SectionsAddEquiv_apply, ext₀SectionsAddEquiv_apply, homEquiv₀_mk₀_comp]
  show (Ext.homEquiv₀ x).hom.app (op W) ((freeSheafMap (J := J) m).hom.app (op W) (gen (J := J) W)) = _
  rw [freeSheafMap_gen]
  exact congrArg (fun α => α (gen (J := J) U)) ((Ext.homEquiv₀ x).hom.naturality m.op)

/-- Naturality in `F`: postcomposition with `μ : F ⟶ F'` is `μ` on sections. -/
theorem ext₀SectionsAddEquiv_postcomp {F' : Sheaf J AddCommGrpCat.{u}} (μ : F ⟶ F')
    (x : Ext (freeSheaf J U) F 0) :
    ext₀SectionsAddEquiv U F' (x.comp (Ext.mk₀ μ) (add_zero 0)) =
      μ.hom.app (op U) (ext₀SectionsAddEquiv U F x) := by
  rw [ext₀SectionsAddEquiv_apply, ext₀SectionsAddEquiv_apply, homEquiv₀_comp_mk₀]
  rfl


section Action

open CategoryTheory.Abelian.Ext

variable (R : Type*) [CommRing R] (F : Sheaf J AddCommGrpCat.{u}) [ExtAction R F]

/-- The `R`-module structure on the sections `F(U)` given by an `ExtAction`:
`r • s = (μ r).hom.app (op U) s`. Used as a local instance. -/
@[instance_reducible] def ExtAction.sectionsModule (U : C) : Module R (F.obj.obj (op U)) where
  smul r s := (ExtAction.μ (F := F) r).hom.app (op U) s
  one_smul s := by
    show (ExtAction.μ (F := F) (1 : R)).hom.app (op U) s = s
    rw [ExtAction.μ_one]
    rfl
  mul_smul r r' s := by
    show (ExtAction.μ (F := F) (r * r')).hom.app (op U) s =
      (ExtAction.μ (F := F) r).hom.app (op U) ((ExtAction.μ (F := F) r').hom.app (op U) s)
    rw [mul_comm, ExtAction.μ_mul]
    rfl
  smul_zero r := by
    show (ExtAction.μ (F := F) r).hom.app (op U) 0 = 0
    exact map_zero _
  smul_add r s t := by
    show (ExtAction.μ (F := F) r).hom.app (op U) (s + t) = _
    exact map_add _ _ _
  add_smul r r' s := by
    show (ExtAction.μ (F := F) (r + r')).hom.app (op U) s = _
    rw [ExtAction.μ_add]
    rfl
  zero_smul s := by
    show (ExtAction.μ (F := F) (0 : R)).hom.app (op U) s = 0
    rw [ExtAction.μ_zero]
    rfl

attribute [local instance] ExtAction.module ExtAction.sectionsModule

omit [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] in
theorem ExtAction.sectionsModule_smul_def (U : C) (r : R) (s : F.obj.obj (op U)) :
    r • s = (ExtAction.μ (F := F) r).hom.app (op U) s := rfl

/-- `Ext(ℤ[h_U]^#, F, 0) ≃ₗ[R] F(U)`. -/
def ext₀SectionsLinearEquiv (U : C) : Ext (freeSheaf J U) F 0 ≃ₗ[R] F.obj.obj (op U) :=
  { ext₀SectionsAddEquiv U F with
    map_smul' := fun r x => by
      show ext₀SectionsAddEquiv U F (x.comp (Ext.mk₀ (ExtAction.μ (F := F) r)) (add_zero 0)) =
        (ExtAction.μ (F := F) r).hom.app (op U) (ext₀SectionsAddEquiv U F x)
      exact ext₀SectionsAddEquiv_postcomp U F _ x }

theorem ext₀SectionsLinearEquiv_apply (U : C) (x : Ext (freeSheaf J U) F 0) :
    ext₀SectionsLinearEquiv R F U x = ext₀SectionsAddEquiv U F x := rfl

/-- Restriction of sections `F(U) → F(W)` along `m : W ⟶ U`, `R`-linear. -/
def sectionsRes {W U : C} (m : W ⟶ U) : F.obj.obj (op U) →ₗ[R] F.obj.obj (op W) where
  toFun s := F.obj.map m.op s
  map_add' s t := map_add _ s t
  map_smul' r s := by
    rw [RingHom.id_apply, ExtAction.sectionsModule_smul_def, ExtAction.sectionsModule_smul_def]
    exact (ConcreteCategory.congr_hom ((ExtAction.μ (F := F) r).hom.naturality m.op) s).symm

omit [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] in
theorem sectionsRes_apply {W U : C} (m : W ⟶ U) (s : F.obj.obj (op U)) :
    sectionsRes R F m s = F.obj.map m.op s := rfl

theorem ext₀SectionsLinearEquiv_precompLinear {W U : C} (m : W ⟶ U) (x : Ext (freeSheaf J U) F 0) :
    ext₀SectionsLinearEquiv R F W (precompLinear R F (freeSheafMap (J := J) m) 0 x) =
      sectionsRes R F m (ext₀SectionsLinearEquiv R F U x) :=
  ext₀SectionsAddEquiv_precomp U F m x

/-- If the restriction of sections `F(U) → F(W)` is a localization at `S`, so is the restriction
`Ext(ℤ[h_U]^#, F, 0) → Ext(ℤ[h_W]^#, F, 0)` in degree `0`. -/
theorem isLocalizedModule_precompLinear_zero_of_sections (S : Submonoid R) {W U : C} (m : W ⟶ U)
    (h : IsLocalizedModule S (sectionsRes R F m)) :
    IsLocalizedModule S (precompLinear R F (freeSheafMap (J := J) m) 0) := by
  have heq : precompLinear R F (freeSheafMap (J := J) m) 0 =
      (ext₀SectionsLinearEquiv R F W).symm.toLinearMap ∘ₗ
        (sectionsRes R F m ∘ₗ (ext₀SectionsLinearEquiv R F U).toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← ext₀SectionsLinearEquiv_precompLinear, LinearEquiv.symm_apply_apply]
  rw [heq]
  have h1 := IsLocalizedModule.of_linearEquiv_right S _ (ext₀SectionsLinearEquiv R F U) (hf := h)
  exact IsLocalizedModule.of_linearEquiv S _ (ext₀SectionsLinearEquiv R F W).symm (hf := h1)

end Action

end Stacks09sxAux

end
