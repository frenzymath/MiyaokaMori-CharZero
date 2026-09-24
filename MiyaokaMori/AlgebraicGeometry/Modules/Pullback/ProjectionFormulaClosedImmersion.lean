import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionProjectionFormula

/-! # Projection formula along a closed immersion, for an arbitrary module

**Projection formula along a closed immersion, for an arbitrary module `E`**:
`i_*(G ⊗ i^*E) ≅ (i_* G) ⊗ E` for a closed immersion `i : Z → X`, `G` on `Z`, `E` on `X`.

Stacks 01E8 states the projection formula for finite locally free `E` and any morphism; for a closed
immersion (more generally an affine morphism) no hypothesis on `E` is needed, because the comparison map
is an isomorphism on every stalk. The library has the case of a line bundle `E`
(`Scheme.Modules.projectionFormulaHom_isIso`, `pushforwardTensorPullbackIso`, both proved by an
invertibility argument that does not extend to higher rank). The Chern class computation needs the
case `E` locally free of rank `n` (including `n = 0` with `rankAtStalk = 0` but possibly infinite
rank), which is why the statement is for all `E`.

Route: stalkwise (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`).
* Outside the image (`x ∉ i(Z)`): `(i_*N)_x = 0` for every `N` (`subsingleton_stalk_pushforward_of_notMem_range`,
  the argument of Stacks 00AE), so both stalks of `θ` vanish (`tensorStalkEquiv` for the source).
* At `x = i z`: `σ_N : (i_*N)_{i z} → N_z` (Mathlib `stalkPushforward`) is bijective for a closed embedding
  (`stalkPushforward_iso_of_isInducing`) and semilinear along `i.stalkMap z` (`pushforwardStalkMap_smul`).
  On section pairs `θ(e ⊗ g) = η_E(e) ⊗ g` (unfold `θ = η ≫ i_*(δ ≫ (i^*E ◁ ε))`, evaluate `δ` with
  `pullbackTensorObjHom_app_unit_tensorSections`, cancel `ε ∘ η` by the triangle identity). Hence under
  `tensorStalkEquiv` (Stacks 01CB) the composite `σ ∘ θ_{i z}` is `e ⊗ g ↦ η_E(e) ⊗ σ_G(g)`
  (`projectionFormulaStalkAux`), a composite of the bijections `id ⊗ σ_G`, `TensorProduct.comm`,
  `AlgebraTensorModule.cancelBaseChange⁻¹` and `(i^*E)_z ≅ O_{Z,z} ⊗ E_{i z}`
  (`modulePullbackStalkTensorEquiv`).
The base-change description of the pullback stalk and the tensor-stalk formula are
`ModulePullbackStalkTensorBijective.lean` and `ModulesTensorStalk.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {Z X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of a sheaf of modules over `⊥` form a subsingleton. -/
private theorem subsingleton_sections_bot' (N : Z.Modules) : Subsingleton Γ(N, ⊥) := by
  have t : IsTerminal (N.val.presheaf.obj (op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Z)
  have h : (𝟙 (N.val.presheaf.obj (op (⊥ : Z.Opens)))) = 0 := t.hom_ext _ _
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Γ(N, ⊥), z = 0 := fun z => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) z) h
    exact this
  rw [hx x, hx y]

/-- The stalk of `i_* N` at a point outside the image of a closed immersion is zero. -/
theorem subsingleton_stalk_pushforward_of_notMem_range (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (N : Z.Modules) (x : X) (hx : x ∉ Set.range i.base) :
    Subsingleton (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.stalk x) := by
  refine ⟨fun a b => ?_⟩
  suffices hzero : ∀ t : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.stalk x, t = 0 by
    rw [hzero a, hzero b]
  intro t
  obtain ⟨U, hxU, s, rfl⟩ := ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.exists_germ_eq t
  let C : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hxV : x ∈ U ⊓ C := ⟨hxU, hx⟩
  have hVU : U ⊓ C ≤ U := inf_le_left
  have hpre : i ⁻¹ᵁ (U ⊓ C) = ⊥ := by
    ext z
    simp [C]
  have hsub : Subsingleton Γ(N, i ⁻¹ᵁ (U ⊓ C)) := by
    rw [hpre]
    exact subsingleton_sections_bot' N
  have hres : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.map (homOfLE hVU).op s = 0 :=
    hsub.elim _ _
  rw [← ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.germ_res_apply (homOfLE hVU) x hxV s,
    hres, map_zero]



/-- The stalk map `(i_* N)_{i z} → N_z` of the pushforward (Mathlib `stalkPushforward`), as an
additive map on the stalks of the module sheaves. -/
def pushforwardStalkMap (i : Z ⟶ X) (N : Z.Modules) (z : Z) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.stalk (i.base z) →+
      N.presheaf.stalk z :=
  (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.base N.presheaf z).hom

theorem pushforwardStalkMap_germ (i : Z ⟶ X) (N : Z.Modules) (z : Z) (U : X.Opens) (hx : i.base z ∈ U)
    (s : Γ(N, i ⁻¹ᵁ U)) :
    pushforwardStalkMap i N z
        (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.germ U (i.base z) hx s) =
      N.presheaf.germ (i ⁻¹ᵁ U) z hx s :=
  TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} i.base N.presheaf U z hx s

theorem pushforwardStalkMap_bijective (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (N : Z.Modules) (z : Z) : Function.Bijective (pushforwardStalkMap i N z) := by
  have hiso : IsIso (N.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
      i.isClosedEmbedding.isInducing N.presheaf z
  exact ConcreteCategory.bijective_of_isIso (N.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z)

/-- The pushforward stalk map is semilinear along the stalk map of `i`. -/
theorem pushforwardStalkMap_smul (i : Z ⟶ X) (N : Z.Modules) (z : Z)
    (r : X.presheaf.stalk (i.base z))
    (m : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.stalk (i.base z)) :
    pushforwardStalkMap i N z (r • m) = i.stalkMap z r • pushforwardStalkMap i N z m := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ :=
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i.base z) hxV a]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj N).val]
  erw [pushforwardStalkMap_germ, pushforwardStalkMap_germ, Scheme.Hom.germ_stalkMap_apply]
  change N.presheaf.germ (i ⁻¹ᵁ V) z hxV
    ((i.app V (X.presheaf.map (homOfLE hVU).op a)) • (id b : Γ(N, i ⁻¹ᵁ V))) = _
  erw [PresheafOfModules.germ_smul (R := Z.presheaf) N.val]
  rfl



/-- Triangle identity on sections: `ε_G (η_{i_*G} g) = g`. -/
private theorem counit_app_unit_app_pushforward (i : Z ⟶ X) (G : Z.Modules) (U : X.Opens)
    (g : Γ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G).app (i ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).app U g) = g := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).right_triangle_components G
  have h' := congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pushforward i).obj G ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward i).obj G => φ.app U g) h
  exact h'

/-- Left whiskering on section pairs. -/
private theorem whiskerLeft_app_tensorSections_pf (A : X.Modules) {B B' : X.Modules} (g : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ g).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (g.app U b) := by
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) g U a b

/-- **The comparison map on section pairs**: on `U ⊆ X`,
`θ (e ⊗ g) = η_E(e) ⊗ g` in `Γ(i^*E ⊗ G, i⁻¹U) = Γ(i_*(i^*E ⊗ G), U)`. -/
private theorem projectionFormulaHom_app_tensorSections_pf (i : Z ⟶ X) (E : X.Modules) (G : Z.Modules)
    (U : X.Opens) (e : Γ(E, U)) (g : Γ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G, U)) :
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) U e g) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G (i ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app E).app U e) g := by
  rw [AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_eq_unit_comp]
  change ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E ◁
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G).app (i ⁻¹ᵁ U)
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom i E
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).app (i ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G))).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) U e g))) = _
  rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections]
  erw [whiskerLeft_app_tensorSections_pf]
  erw [counit_app_unit_app_pushforward]
  rfl


section ImagePoint

attribute [local instance] AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra

variable (i : Z ⟶ X) (G : Z.Modules) (z : Z)

/-- `G_z` as a module over `O_{X, i z}` through the stalk map of `i`. -/
@[instance_reducible]
def pushforwardStalkModule : Module (X.presheaf.stalk (i.base z)) (G.presheaf.stalk z) :=
  Module.compHom _ (i.stalkMap z).hom

attribute [local instance] pushforwardStalkModule

theorem pushforwardStalkModule_isScalarTower :
    IsScalarTower (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) (G.presheaf.stalk z) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] pushforwardStalkModule_isScalarTower

/-- For a closed immersion, `(i_* G)_{i z} ≅ G_z` as `O_{X, i z}`-modules. -/
def pushforwardStalkLinearEquiv [AlgebraicGeometry.IsClosedImmersion i] :
    ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)
      ≃ₗ[X.presheaf.stalk (i.base z)] G.presheaf.stalk z :=
  LinearEquiv.ofBijective
    ({ toFun := pushforwardStalkMap i G z
       map_add' := map_add _
       map_smul' := by
         intro r m
         exact pushforwardStalkMap_smul i G z r m } :
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)
        →ₗ[X.presheaf.stalk (i.base z)] G.presheaf.stalk z)
    (pushforwardStalkMap_bijective i G z)

@[simp]
theorem pushforwardStalkLinearEquiv_apply [AlgebraicGeometry.IsClosedImmersion i]
    (m : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)) :
    pushforwardStalkLinearEquiv i G z m = pushforwardStalkMap i G z m := rfl

variable (E : X.Modules)

/-- The stalk-level model of `θ_{i z}`: `E_x ⊗_R (i_*G)_x → (i^*E)_z ⊗_S G_z`, `e ⊗ g ↦ η(e) ⊗ σ(g)`,
written as a composite of bijections. -/
def projectionFormulaStalkAux [AlgebraicGeometry.IsClosedImmersion i]
    (w : E.presheaf.stalk (i.base z) ⊗[X.presheaf.stalk (i.base z)]
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E).presheaf.stalk z ⊗[Z.presheaf.stalk z]
      G.presheaf.stalk z :=
  TensorProduct.comm (Z.presheaf.stalk z) _ _
    (TensorProduct.congr (LinearEquiv.refl (Z.presheaf.stalk z) (G.presheaf.stalk z))
      (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv i E z)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk (i.base z))
          (Z.presheaf.stalk z) (Z.presheaf.stalk z) (G.presheaf.stalk z)
          (E.presheaf.stalk (i.base z))).symm
        (TensorProduct.comm (X.presheaf.stalk (i.base z)) _ _
          (TensorProduct.congr (LinearEquiv.refl (X.presheaf.stalk (i.base z)) (E.presheaf.stalk (i.base z)))
            (pushforwardStalkLinearEquiv i G z) w))))

theorem projectionFormulaStalkAux_bijective [AlgebraicGeometry.IsClosedImmersion i] :
    Function.Bijective (projectionFormulaStalkAux i G z E) :=
  (TensorProduct.comm (Z.presheaf.stalk z) _ _).bijective.comp
    ((TensorProduct.congr (LinearEquiv.refl (Z.presheaf.stalk z) (G.presheaf.stalk z))
      (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv i E z)).bijective.comp
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk (i.base z))
          (Z.presheaf.stalk z) (Z.presheaf.stalk z) (G.presheaf.stalk z)
          (E.presheaf.stalk (i.base z))).symm.bijective.comp
        ((TensorProduct.comm (X.presheaf.stalk (i.base z)) _ _).bijective.comp
          (TensorProduct.congr (LinearEquiv.refl (X.presheaf.stalk (i.base z)) (E.presheaf.stalk (i.base z)))
            (pushforwardStalkLinearEquiv i G z)).bijective)))

theorem projectionFormulaStalkAux_zero [AlgebraicGeometry.IsClosedImmersion i] :
    projectionFormulaStalkAux i G z E 0 = 0 := by
  unfold projectionFormulaStalkAux
  simp only [map_zero]

theorem projectionFormulaStalkAux_add [AlgebraicGeometry.IsClosedImmersion i] (v w) :
    projectionFormulaStalkAux i G z E (v + w) =
      projectionFormulaStalkAux i G z E v + projectionFormulaStalkAux i G z E w := by
  unfold projectionFormulaStalkAux
  simp only [map_add]

theorem projectionFormulaStalkAux_tmul [AlgebraicGeometry.IsClosedImmersion i]
    (e : E.presheaf.stalk (i.base z))
    (g : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)) :
    projectionFormulaStalkAux i G z E (e ⊗ₜ g) =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit i E z e ⊗ₜ[Z.presheaf.stalk z] pushforwardStalkMap i G z g := by
  unfold projectionFormulaStalkAux
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.comm_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.comm_tmul, pushforwardStalkLinearEquiv_apply]
  congr 1
  change (1 : Z.presheaf.stalk z) • AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit i E z e = _
  rw [one_smul]

/-- **`θ` on the stalk at `i z`, under the stalk identifications**: `θ_{i z}` is the model map
`projectionFormulaStalkAux` (`e ⊗ g ↦ η(e) ⊗ σ(g)`). -/
theorem tensorStalkEquiv_pushforwardStalkMap_stalkMap_projectionFormulaHom
    [AlgebraicGeometry.IsClosedImmersion i]
    (w : E.presheaf.stalk (i.base z) ⊗[X.presheaf.stalk (i.base z)]
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk (i.base z)) :
    AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G z
        (pushforwardStalkMap i
          (CategoryTheory.MonoidalCategoryStruct.tensorObj
            ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G) z
          (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (i.base z)
            (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G)
            ((AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
              ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z)).symm w))) =
      projectionFormulaStalkAux i G z E w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, projectionFormulaStalkAux_zero]
  | add v w hv hw =>
      simp only [map_add, projectionFormulaStalkAux_add]
      rw [hv, hw]
  | tmul e g =>
      obtain ⟨U, hx, a, b, ha, hb⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_germ_pair E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z) e g
      subst ha
      subst hb
      have hsymm : (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z)).symm
          ((E.presheaf.germ U (i.base z) hx) a ⊗ₜ[X.presheaf.stalk (i.base z)]
            (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.germ U (i.base z) hx) b) =
          ((CategoryTheory.MonoidalCategoryStruct.tensorObj E
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).presheaf.germ U (i.base z) hx)
            (AlgebraicGeometry.Scheme.Modules.tensorSections E
              ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) U a b) :=
        (LinearEquiv.symm_apply_eq _).mpr
          (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv_germ_tensorSections E
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z) U hx a b).symm
      rw [hsymm, AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, projectionFormulaHom_app_tensorSections_pf]
      erw [pushforwardStalkMap_germ]
      rw [AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv_germ_tensorSections,
        projectionFormulaStalkAux_tmul]
      erw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ, pushforwardStalkMap_germ]

/-- `θ` is bijective on the stalk at a point `i z` of the image. -/
theorem stalkMap_projectionFormulaHom_bijective_image [AlgebraicGeometry.IsClosedImmersion i] :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (i.base z)
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G)) := by
  have hcomp : ∀ v, pushforwardStalkMap i
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G) z
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (i.base z)
        (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G) v) =
      (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G z).symm
        (projectionFormulaStalkAux i G z E
          (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z) v)) := by
    intro v
    have h := tensorStalkEquiv_pushforwardStalkMap_stalkMap_projectionFormulaHom i G z E
      (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z) v)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h, LinearEquiv.symm_apply_apply]
  have hfun : ⇑(pushforwardStalkMap i
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G) z) ∘
      ⇑(AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (i.base z)
        (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G)) =
      ⇑(AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G z).symm ∘
        (projectionFormulaStalkAux i G z E ∘
          ⇑(AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z))) :=
    funext hcomp
  have hbij : Function.Bijective (⇑(pushforwardStalkMap i
      (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G) z) ∘
      ⇑(AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (i.base z)
        (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G))) := by
    rw [hfun]
    exact (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G z).symm.bijective.comp
      ((projectionFormulaStalkAux_bijective i G z E).comp
        (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
          ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) (i.base z)).bijective)
  exact (Function.Bijective.of_comp_iff' (pushforwardStalkMap_bijective i _ z) _).mp hbij

end ImagePoint

/-- `θ` is bijective on the stalk at a point outside the image: both stalks vanish. -/
theorem stalkMap_projectionFormulaHom_bijective_of_notMem_range (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (E : X.Modules) (G : Z.Modules) (x : X)
    (hx : x ∉ Set.range i.base) :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G)) := by
  have hT := subsingleton_stalk_pushforward_of_notMem_range i
    (CategoryTheory.MonoidalCategoryStruct.tensorObj
      ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) G) x hx
  have hG := subsingleton_stalk_pushforward_of_notMem_range i G x hx
  have hS : Subsingleton ((CategoryTheory.MonoidalCategoryStruct.tensorObj E
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)).presheaf.stalk x) := by
    have hzero : ∀ w : E.presheaf.stalk x ⊗[X.presheaf.stalk x]
        ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).presheaf.stalk x, w = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rfl
      | tmul e g => rw [Subsingleton.elim g 0, TensorProduct.tmul_zero]
      | add v w hv hw => rw [hv, hw, add_zero]
    refine ⟨fun a b => ?_⟩
    apply (AlgebraicGeometry.Scheme.Modules.tensorStalkEquiv E
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) x).injective
    exact (hzero _).trans (hzero _).symm
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩


end AlgebraicGeometry.Scheme.Modules

/-- **Projection formula for closed immersions (all `E`).** The comparison map
`θ = projectionFormulaHom i E G : E ⊗ i_*G ⟶ i_*(i^*E ⊗ G)` is an isomorphism when `i` is a closed
immersion, for every `E : X.Modules` and `G : Z.Modules`.

Source: Stacks 01E8 (projection formula; there for finite locally free `E`), Stacks 01QY (modules on a
closed subscheme); for closed immersions the general statement follows from the stalk computation below
(Hartshorne II Ex. 5.1(d) is the finite locally free case).

Proof (self-contained, by stalks; `AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective` reduces to bijectivity
of `θ_x` for all `x : X`):
1. `x ∉ i(Z)`. `i(Z)` is closed, so `x` has an open neighbourhood `U` with `U ∩ i(Z) = ∅`; every
   pushforward `i_* N` has `(i_* N)(V) = N(i⁻¹ V) = N(∅) = 0` for `V ⊆ U`, hence `(i_* N)_x = 0` for all
   `N`. The stalk of a tensor product is the tensor product of stalks (`Scheme.Modules.tensorStalkEquiv`),
   so `(E ⊗ i_*G)_x = E_x ⊗ 0 = 0`, and `(i_*(i^*E ⊗ G))_x = 0`. Thus `θ_x : 0 → 0` is bijective.
2. `x = i(z)`. Since `i` is a closed embedding, `(i_* N)_x ≅ N_z` naturally in `N`
   (`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`; used in
   `Stacks0bemSupport.mem_support_pushforward_of_isClosedImmersion`). The stalk of the pullback is the base
   change `(i^*E)_z ≅ O_{Z,z} ⊗_{O_{X,x}} E_x` (`Scheme.Modules.pullback` is `sheafify (i⁻¹E ⊗_{i⁻¹O_X} O_Z)`;
   stalks commute with `i⁻¹` and with sheafification, and with the tensor product). Hence
   `(i_*(i^*E ⊗ G))_x ≅ (O_{Z,z} ⊗_{O_{X,x}} E_x) ⊗_{O_{Z,z}} G_z ≅ E_x ⊗_{O_{X,x}} G_z`
   (`TensorProduct.AlgebraTensorModule.cancelBaseChange`), and `(E ⊗ i_*G)_x ≅ E_x ⊗_{O_{X,x}} G_z`.
   Under these identifications `θ_x` is the canonical map `e ⊗ g ↦ e ⊗ g` — `θ` is defined as the
   adjunct of `δ_{E, i_*G} ≫ (i^*E ◁ ε_G)` (`projectionFormulaHom` = `Adjunction.homEquiv` of
   `pullbackTensorObjHom ≫ whiskerLeft counit`), and on stalks the unit `η : i_*G → i_*i^*i_*G`, the
   counit `ε : i^*i_*G → G` and `δ` (which is an iso, `pullbackTensorObjHom_isIso`) are the canonical
   base-change maps, whose composite is the identity of `E_x ⊗ G_z` (triangle identity). So `θ_x` is
   bijective.
3. Conclude with `moduleHom_isIso_iff_stalk_bijective`.

Formalized as stated: (a) is `subsingleton_stalk_pushforward_of_notMem_range`,
(b) is `modulePullbackStalkTensorEquiv` (for all `E` and all morphisms), (c) is
`tensorStalkEquiv_pushforwardStalkMap_stalkMap_projectionFormulaHom` (proved on section pairs, where the
identity `θ(e ⊗ g) = η_E(e) ⊗ g` is a one-line consequence of the definition and the triangle identity).

Edge cases: `Z = ∅` (both sides `0`); `E = 0` or `G = 0` (both sides `0`); `Z = X`, `i = 𝟙` (θ is the
identity up to unitors). -/
theorem AlgebraicGeometry.Scheme.Modules.isIso_projectionFormulaHom_of_isClosedImmersion
    {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (E : X.Modules) (G : Z.Modules) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G) := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro x
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    exact AlgebraicGeometry.Scheme.Modules.stalkMap_projectionFormulaHom_bijective_image i G z E
  · exact AlgebraicGeometry.Scheme.Modules.stalkMap_projectionFormulaHom_bijective_of_notMem_range i E G x hx

/-- **Projection formula for closed immersions, `Modules.tensor` form**:
`i_*(G ⊗ i^*E) ≅ (i_* G) ⊗ E` (compare `Scheme.Modules.pushforwardTensorPullbackIso`, which needs `E`
to be a line bundle). Assembled from `isIso_projectionFormulaHom_of_isClosedImmersion` exactly as
`pushforwardTensorPullbackIso` is assembled from `projectionFormulaIso`; kept as `Nonempty` (its user
`Stacks0ayt.lean` destructs it); the underlying `IsIso` is now proved. -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_tensor_pullback_iso_of_isClosedImmersion
    {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (G : Z.Modules) (E : X.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E)) ≅
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).tensor E) := by
  have := AlgebraicGeometry.Scheme.Modules.isIso_projectionFormulaHom_of_isClosedImmersion i E G
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pushforward i).mapIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E) ≪≫
        β_ G ((AlgebraicGeometry.Scheme.Modules.pullback i).obj E)) ≪≫
    (CategoryTheory.asIso (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i E G)).symm ≪≫
    β_ E ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) E).symm⟩


end
