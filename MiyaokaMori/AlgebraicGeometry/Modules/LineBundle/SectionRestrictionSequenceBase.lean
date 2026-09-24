import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionUnitEpi
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.RegularSection
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoSectionsGeneration
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.SectionRestrictionSequenceMono
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionRestrictionSequenceUnitCompat

/-! # Base case of the restriction sequence

**Base case of the restriction sequence** (Stacks 01WX / 0B90; the paper's sequence with `N = O_X`):
`M` a line bundle on a scheme `X`, `s ∈ Γ(X, M)` a regular section, `I` an ideal sheaf which is the zero
ideal of `(M, s)` (`IsZeroIdeal I M s`: on every affine open with a frame `e` of `M`, `I = (coord_e s)`;
`idealSheafOfSection M s` is such an `I`), `ι : D := V(I) → X` its closed immersion. Then
`0 → O_X →(σ_s) M →(η_M) ι_*ι^*M → 0` is short exact, where `σ_s = homOfTopSection M s` is `r ↦ r s`
and `η_M` is the unit of `ι^* ⊣ ι_*` (restriction of sections to `D`).

Proof (all steps formalized in this file):
1. `0 → I → O_X → ι_*O_D → 0` is short exact (`I.toModules` is by definition the kernel of
   `u := unitToPushforwardObjUnit`, and `u` is epi for a closed immersion: `shortExact_kernel_unit`).
2. `M ⊗ −` preserves short exactness (`− ⊗ M` is an equivalence for a line bundle,
   `isEquivalence_tensorRight_of_isLineBundle`; pass to `M ⊗ −` by the braiding), giving
   `0 → M ⊗ I →(M ◁ κ) M ⊗ O_X →(M ◁ u) M ⊗ ι_*O_D → 0` (`shortExact_whiskerLeft_kernel_unit`).
3. `e : M ⊗ ι_*O_D ≅ ι_*ι^*M` (projection formula, Stacks 01E8) satisfies `(M ◁ u) ≫ e = ρ_M ≫ η_M`
   (`whiskerLeft_unitToPushforwardObjUnit_comp_projectionFormulaHom`); hence `η_M` is epi.
4. `σ_s` is mono since `s` is regular (`mono_homOfTopSection_of_injective`).
5. Exactness in the middle, on sections (`exact_iff_locally_lift_sections`): if `x ∈ Γ(M, U)` has
   `η_M(x) = 0`, then by 3 `(M ◁ u)(ρ⁻¹ x) = 0`, so by 2 `ρ⁻¹ x = (M ◁ κ)(z)` for some `z ∈ Γ(M ⊗ I, U)`;
   near any point, `z` is the image of an element of `Γ(M, V₀) ⊗ Γ(I, V₀)` (sheafification), a finite
   sum of elementary tensors, so `x = Σ κ(a_j) m_j ∈ I(V)·Γ(M, V)` on an affine `V` with a frame `e` of
   `M`; there `I(V) = (f)` with `s|_V = f e`, so `x|_V = f g e = g s|_V = σ_s(g)`.
6. `σ_s ≫ η_M = 0`: it suffices that `η_M(s) = 0`, which is local; on an affine `V` with a frame,
   `s|_V = f e = ρ((M ◁ κ)(e ⊗ a))` with `κ(a) = f`, and `(M ◁ κ) ≫ (M ◁ u) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `u : O_X → ι_*O_{V(I)}` (`unitToPushforwardObjUnit`), typed in `X.Modules`. -/
abbrev unitHom (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶
    (AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- `κ : I → O_X`, the kernel of `u` (`I.toModules` is by definition this kernel). -/
abbrev kerι (I : X.IdealSheafData) : CategoryTheory.Limits.kernel (unitHom I) ⟶ 𝟙_ X.Modules :=
  CategoryTheory.Limits.kernel.ι (unitHom I)

/-- `η_M : M → ι_*ι^*M`, the unit of `ι^* ⊣ ι_*`. -/
abbrev adjUnit (I : X.IdealSheafData) (M : X.Modules) : M ⟶
    (AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M

/-- `σ_s : O_X → M`, `r ↦ r s` (`homOfTopSection`), typed in `X.Modules`. -/
abbrev sectionHom (M : X.Modules) (s : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  AlgebraicGeometry.Scheme.Modules.homOfTopSection M s

/-- Left whiskering on an elementary tensor of sections (`tensorHom_tensorSections` with `𝟙`). -/
theorem whiskerLeft_app_tensorSections {A B B' : X.Modules} (f : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ f).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (f.app U b) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) f U a b

variable (M : X.Modules) [M.IsLineBundle] (I : X.IdealSheafData)

/-- `e : M ⊗ ι_*O_D ≅ ι_*ι^*M`: the projection formula followed by `ι_*(ρ)`. -/
def unitTensorPushforwardIso :
    M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M) :=
  AlgebraicGeometry.Scheme.Modules.projectionFormulaIso I.subschemeι M _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).mapIso (ρ_ _)

/-- `(M ◁ u) ≫ e = ρ_M ≫ η_M`. -/
theorem whiskerLeft_unit_comp_unitTensorPushforwardIso_hom :
    (M ◁ unitHom I) ≫ (unitTensorPushforwardIso M I).hom = (ρ_ M).hom ≫ adjUnit I M :=
  whiskerLeft_unitToPushforwardObjUnit_comp_projectionFormulaHom I.subschemeι M

theorem whiskerLeft_kernel_comp_whiskerLeft_unit : (M ◁ kerι I) ≫ (M ◁ unitHom I) = 0 := by
  have := AlgebraicGeometry.Scheme.Modules.monoidalPreadditive X
  exact ((MonoidalCategory.whiskerLeft_comp M (kerι I) (unitHom I)).symm.trans
    (congrArg (fun f => M ◁ f) (kernel.condition (unitHom I)))).trans
    MonoidalPreadditive.whiskerLeft_zero

/-- The ideal-sheaf sequence tensored with `M`: `0 → M ⊗ I → M ⊗ O_X → M ⊗ ι_*O_D → 0`. -/
theorem shortExact_whiskerLeft_kernel_unit :
    (ShortComplex.mk (M ◁ kerι I) (M ◁ unitHom I)
      (whiskerLeft_kernel_comp_whiskerLeft_unit M I)).ShortExact := by
  have hS₀ : (ShortComplex.mk (kerι I) (unitHom I) (kernel.condition (unitHom I))).ShortExact :=
    I.shortExact_kernel_unit
  have : (CategoryTheory.MonoidalCategory.tensorRight M).IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle M
  have : CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})
      (CategoryTheory.MonoidalCategory.tensorRight M) := inferInstance
  have : (CategoryTheory.MonoidalCategory.tensorRight M).PreservesZeroMorphisms := inferInstance
  have hS₁ := hS₀.map_of_exact (CategoryTheory.MonoidalCategory.tensorRight M)
  refine ShortComplex.shortExact_of_iso ?_ hS₁
  exact ShortComplex.isoMk (β_ _ M) (β_ _ M) (β_ _ M)
    (BraidedCategory.braiding_naturality_left _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm

/-- `η_M : M → ι_*ι^*M` is an epimorphism. -/
theorem epi_unit_app : Epi (adjUnit I M) := by
  have hS := shortExact_whiskerLeft_kernel_unit M I
  have : Epi (M ◁ unitHom I) := hS.epi_g
  have h : adjUnit I M = (ρ_ M).inv ≫ (M ◁ unitHom I) ≫ (unitTensorPushforwardIso M I).hom := by
    rw [whiskerLeft_unit_comp_unitTensorPushforwardIso_hom, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The presheaf tensor product `G A ⊗ G B` of the underlying presheaves of modules (before
sheafification); `Modules.tensor A B` is its sheafification. -/
abbrev presheafTensor (A B : X.Modules) : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  CategoryTheory.MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)

/-- The elementary tensor `m ⊗ a ∈ Γ(M, V₀) ⊗ Γ(I, V₀)` is sent by `(M ◁ κ) ≫ ρ_M` to
`κ(a)|_V • m|_V ∈ I(V)·Γ(M, V)` on an affine `V ≤ V₀`. -/
theorem app_tmul_mem_ideal_smul_top {V₀ V : X.Opens} (hV : V ∈ X.affineOpens) (hVV₀ : V ≤ V₀)
    (m : Γ(M, V₀)) (a : Γ((CategoryTheory.Limits.kernel (unitHom I)), V₀)) :
    ((M ◁ kerι I) ≫ (ρ_ M).hom).app V
      ((M ⊗ (CategoryTheory.Limits.kernel (unitHom I))).presheaf.map (homOfLE hVV₀).op
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M (CategoryTheory.Limits.kernel (unitHom I))).hom.app V₀
          (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I)))).app (op V₀) (TensorProduct.tmul _ m a)))) ∈
      I.ideal ⟨V, hV⟩ • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M (CategoryTheory.Limits.kernel (unitHom I))).hom.app V₀
        (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I)))).app (op V₀) (TensorProduct.tmul _ m a)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M (CategoryTheory.Limits.kernel (unitHom I)) V₀ m a := rfl
  rw [h1, AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res ((M ◁ kerι I) ≫ (ρ_ M).hom) hVV₀
      (AlgebraicGeometry.Scheme.Modules.tensorSections M (CategoryTheory.Limits.kernel (unitHom I)) V₀ m a),
    AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.comp_app_apply (M ◁ kerι I) (ρ_ M).hom V₀
      (AlgebraicGeometry.Scheme.Modules.tensorSections M (CategoryTheory.Limits.kernel (unitHom I)) V₀ m a),
    whiskerLeft_app_tensorSections (A := M) (kerι I) V₀ m a,
    rightUnitor_app_tensorSections M V₀ m ((kerι I).app V₀ a),
    AlgebraicGeometry.Scheme.Modules.map_smul M (homOfLE hVV₀) ((kerι I).app V₀ a) m]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have hrange := I.range_toModules_ι_app ⟨V, hV⟩
  have hmem : X.presheaf.map (homOfLE hVV₀).op ((kerι I).app V₀ a) ∈
      Set.range ((CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        I.subschemeι.toRingCatSheafHom)).val.app (op V)) :=
    ⟨(CategoryTheory.Limits.kernel (unitHom I)).presheaf.map (homOfLE hVV₀).op a, AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res (kerι I) hVV₀ a⟩
  rw [hrange] at hmem
  exact hmem

/-- Elements of `Γ(M, V₀) ⊗ Γ(I, V₀)` are sent by `(M ◁ κ) ≫ ρ_M` into `I(V)·Γ(M, V)` for every
affine `V ≤ V₀` (elementary tensors `m ⊗ a ↦ κ(a)|_V • m|_V` with `κ(a)|_V ∈ I(V)`). -/
theorem app_mem_ideal_smul_top {V₀ V : X.Opens} (hV : V ∈ X.affineOpens) (hVV₀ : V ≤ V₀)
    (t : (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I))).obj (op V₀)) :
    ((M ◁ kerι I) ≫ (ρ_ M).hom).app V
      ((M ⊗ CategoryTheory.Limits.kernel (unitHom I)).presheaf.map (homOfLE hVV₀).op
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
            (CategoryTheory.Limits.kernel (unitHom I))).hom.app V₀
          (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I)))).app (op V₀) t))) ∈
      I.ideal ⟨V, hV⟩ • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  -- the composite as a single additive map
  let Ψ : (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I))).obj (op V₀) →+ Γ(M, V) :=
    (ConcreteCategory.hom (((M ◁ kerι I) ≫ (ρ_ M).hom).app V)).comp
      ((ConcreteCategory.hom
          ((M ⊗ CategoryTheory.Limits.kernel (unitHom I)).presheaf.map (homOfLE hVV₀).op)).comp
        ((ConcreteCategory.hom ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
            (CategoryTheory.Limits.kernel (unitHom I))).hom.app V₀)).comp
          (ConcreteCategory.hom
            (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I)))).app
                (op V₀))).toAddMonoidHom))
  induction t using TensorProduct.induction_on with
  | zero =>
    show Ψ (0 : (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I))).obj (op V₀)) ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    have h : Ψ (a + b) = Ψ a + Ψ b := map_add Ψ a b
    show Ψ (a + b) ∈ _
    rw [h]
    exact Submodule.add_mem _ ha hb
  | tmul m a => exact app_tmul_mem_ideal_smul_top M I hV hVV₀ m a

variable (s : Γ(M, ⊤))

/-- **Sections killed by restriction to `V(I)` are locally multiples of `s`** (step 5 of the module
docstring). Source: Stacks 01WX(3) (`I_D = O(−D)`, i.e. `ker(O_X → O_D) = (f)` locally) together with
the projection formula. -/
theorem exists_smul_eq_of_unit_app_eq_zero (hI : AlgebraicGeometry.Scheme.Modules.IsZeroIdeal I M s)
    (U : X.Opens) (x : Γ(M, U)) (hx : (adjUnit I M).app U x = 0) (p : X) (hp : p ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧ ∃ r : Γ(X, V),
      r • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s = M.presheaf.map (homOfLE hVU).op x := by
  have hS := shortExact_whiskerLeft_kernel_unit M I
  have hcompat := whiskerLeft_unit_comp_unitTensorPushforwardIso_hom M I
  -- (a) `(M ◁ u)(ρ⁻¹ x) = 0`
  have ha : (M ◁ unitHom I).app U ((ρ_ M).inv.app U x) = 0 := by
    have h1 : (unitTensorPushforwardIso M I).hom.app U ((M ◁ unitHom I).app U ((ρ_ M).inv.app U x)) =
        (adjUnit I M).app U ((ρ_ M).hom.app U ((ρ_ M).inv.app U x)) :=
      congrArg (fun φ => φ.app U ((ρ_ M).inv.app U x)) hcompat
    have h2 : (ρ_ M).hom.app U ((ρ_ M).inv.app U x) = x := by
      rw [← AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.comp_app_apply, Iso.inv_hom_id,
        AlgebraicGeometry.Scheme.Modules.Hom.id_app]
      rfl
    rw [h2, hx] at h1
    have h3 := congrArg ((unitTensorPushforwardIso M I).inv.app U) h1
    rw [← AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.comp_app_apply, Iso.hom_inv_id,
      AlgebraicGeometry.Scheme.Modules.Hom.id_app, map_zero] at h3
    exact h3
  -- (b) `ρ⁻¹ x = (M ◁ κ)(z)`
  have : Mono (M ◁ kerι I) := hS.mono_f
  obtain ⟨z, hz⟩ := (ModulesLocLiftAux.sections_of_exact_mono _ hS.exact U).2 _ ha
  have hz' : (M ◁ kerι I).app U z = (ρ_ M).inv.app U x := hz
  -- (c) `z` is locally an element of the presheaf tensor product
  obtain ⟨V₀, hV₀U, hpV₀, t, ht⟩ :=
    AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.exists_tensor_unit_app_eq_map
      M (CategoryTheory.Limits.kernel (unitHom I)) U
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
        (CategoryTheory.Limits.kernel (unitHom I))).inv.app U z) p hp
  -- (d) an affine `V ≤ V₀` with a frame of `M`
  obtain ⟨V, hV₀, hVV₀, hpV, e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le M hpV₀
  have hV : V ∈ X.affineOpens := hV₀
  have hVU : V ≤ U := hVV₀.trans hV₀U
  have hT := app_mem_ideal_smul_top M I hV hVV₀ t
  -- (f) the element in question is `x|_V`
  have hxV : ((M ◁ kerι I) ≫ (ρ_ M).hom).app V
      ((M ⊗ CategoryTheory.Limits.kernel (unitHom I)).presheaf.map (homOfLE hVV₀).op
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
            (CategoryTheory.Limits.kernel (unitHom I))).hom.app V₀
          (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (presheafTensor M (CategoryTheory.Limits.kernel (unitHom I)))).app (op V₀) t))) =
      M.presheaf.map (homOfLE hVU).op x := by
    rw [ht, AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M (CategoryTheory.Limits.kernel (unitHom I))).hom hV₀U
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M (CategoryTheory.Limits.kernel (unitHom I))).inv.app U z),
      AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.tensorIsoTensorObj_hom_app_inv_app U z, AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.map_map_res hVV₀ hV₀U z,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.comp_app_apply (M ◁ kerι I) (ρ_ M).hom V _, AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res (M ◁ kerι I) hVU z, hz',
      AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.app_map_res (ρ_ M).hom hVU ((ρ_ M).inv.app U x),
      ← AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux.comp_app_apply (ρ_ M).inv (ρ_ M).hom U x, Iso.inv_hom_id,
      AlgebraicGeometry.Scheme.Modules.Hom.id_app]
    rfl
  rw [hxV, hI ⟨V, hV⟩ e he, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hT
  obtain ⟨m, -, hm⟩ := hT
  -- (g) `x|_V = f • m = f • (g • e) = g • (f • e) = g • s|_V`
  have hfe : he.coord le_rfl (M.res le_top s) • e = M.res (le_top : V ≤ ⊤) s := by
    have := he.coord_smul_frame le_rfl (M.res le_top s)
    rwa [AlgebraicGeometry.Scheme.Modules.res_self] at this
  have hme : he.coord le_rfl m • e = m := by
    have := he.coord_smul_frame le_rfl m
    rwa [AlgebraicGeometry.Scheme.Modules.res_self] at this
  refine ⟨V, hVU, hpV, he.coord le_rfl m, ?_⟩
  have key : he.coord le_rfl m • M.res (le_top : V ≤ ⊤) s = M.presheaf.map (homOfLE hVU).op x := by
    rw [← hfe, smul_comm, hme, hm]
  exact key

/-- **`s` restricts to zero on its zero scheme**: `η_M(s) = 0` (step 6 of the module docstring).
Source: Stacks 01WX (the canonical section `1_D` of `O(D)` vanishes on `D`). -/
theorem unit_app_top_eq_zero (hI : AlgebraicGeometry.Scheme.Modules.IsZeroIdeal I M s) :
    (adjUnit I M).app ⊤ s = 0 := by
  -- on an affine open with a frame, `s|_V = ρ((M ◁ κ)(e ⊗ a))`, and `(M ◁ κ) ≫ ρ ≫ η = 0`
  have key : ∀ (V : X.Opens) (hV : V ∈ X.affineOpens) (e : Γ(M, V))
      (he : AlgebraicGeometry.Scheme.Modules.IsFrame M V e),
      (adjUnit I M).app V (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) = 0 := by
    intro V hV e he
    have hfe : he.coord le_rfl (M.res le_top s) • e = M.res (le_top : V ≤ ⊤) s := by
      have := he.coord_smul_frame le_rfl (M.res le_top s)
      rwa [AlgebraicGeometry.Scheme.Modules.res_self] at this
    have hfI : he.coord le_rfl (M.res le_top s) ∈ I.ideal ⟨V, hV⟩ := by
      rw [hI ⟨V, hV⟩ e he]
      exact Ideal.mem_span_singleton_self _
    have hrange := I.range_toModules_ι_app ⟨V, hV⟩
    have hmem : he.coord le_rfl (M.res le_top s) ∈
        Set.range ((CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          I.subschemeι.toRingCatSheafHom)).val.app (op V)) := by
      rw [hrange]; exact hfI
    obtain ⟨a, ha⟩ := hmem
    have ha' : (kerι I).app V a = he.coord le_rfl (M.res le_top s) := ha
    have h4 : M.res (le_top : V ≤ ⊤) s = (ρ_ M).hom.app V ((M ◁ kerι I).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections M
          (CategoryTheory.Limits.kernel (unitHom I)) V e a)) := by
      rw [whiskerLeft_app_tensorSections (A := M) (kerι I) V e a,
        rightUnitor_app_tensorSections M V e ((kerι I).app V a), ha', hfe]
    have hcomp : (M ◁ kerι I) ≫ (ρ_ M).hom ≫ adjUnit I M = 0 := by
      rw [← whiskerLeft_unit_comp_unitTensorPushforwardIso_hom, ← Category.assoc,
        whiskerLeft_kernel_comp_whiskerLeft_unit, zero_comp]
    have h5 := congrArg (fun φ => φ.app V (AlgebraicGeometry.Scheme.Modules.tensorSections M
      (CategoryTheory.Limits.kernel (unitHom I)) V e a)) hcomp
    change (adjUnit I M).app V (M.res le_top s) = 0
    rw [h4]
    exact h5
  choose V hV hVtop hpV e he using
    fun p : X => AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le M (U := ⊤) (p := p) trivial
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M)).presheaf,
      ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M)).isSheaf⟩
    V ⊤ (fun p => homOfLE le_top) ?_ _ _ fun p => ?_
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hpV x⟩
  · rw [map_zero]
    exact (_root_.PresheafOfModules.naturality_apply (adjUnit I M).val
      (homOfLE (le_top : V p ≤ ⊤)).op s).symm.trans (key (V p) (hV p) (e p) (he p))

/-- `σ_s ≫ η_M = 0`. -/
theorem homOfTopSection_comp_unit_app (hI : AlgebraicGeometry.Scheme.Modules.IsZeroIdeal I M s) :
    sectionHom M s ≫ adjUnit I M = 0 := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext r
  have h1 : (sectionHom M s).app U r =
      (show Γ(X, U) from r) • (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s :=
    homOfTopSection_val_app M s U r
  have h2 : ((adjUnit I M).val.app (op U)).hom ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) =
      ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op ((adjUnit I M).app ⊤ s) :=
    _root_.PresheafOfModules.naturality_apply (adjUnit I M).val (homOfLE (le_top : U ≤ ⊤)).op s
  have h3 := ((adjUnit I M).val.app (op U)).hom.map_smul (show Γ(X, U) from r)
    ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s)
  show (adjUnit I M).app U ((sectionHom M s).app U r) = 0
  rw [h1]
  refine h3.trans ?_
  rw [h2, unit_app_top_eq_zero M I s hI, map_zero]
  have h0 : ∀ y : X.ringCatSheaf.obj.obj (op U),
      y • (0 : ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj M)).val.obj (op U)) = 0 :=
    fun y => smul_zero y
  exact h0 _

/-- **Base case of the restriction sequence**: `0 → O_X →(σ_s) M →(η_M) ι_*ι^*M → 0` is short exact
for a regular section `s` of a line bundle `M`, `ι : V(I) → X` the zero scheme of `s`. -/
theorem shortExact_homOfTopSection_unit (hI : AlgebraicGeometry.Scheme.Modules.IsZeroIdeal I M s)
    (hs : ∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
      r • ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s : Γ(M, U)))) :
    (ShortComplex.mk (sectionHom M s) (adjUnit I M)
      (homOfTopSection_comp_unit_app M I s hI)).ShortExact := by
  have : Mono (sectionHom M s) := mono_homOfTopSection_of_injective M s hs
  have : Epi (adjUnit I M) := epi_unit_app M I
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [AlgebraicGeometry.Scheme.Modules.exact_iff_locally_lift_sections]
  intro U x hx p hp
  obtain ⟨V, hVU, hpV, r, hr⟩ := exists_smul_eq_of_unit_app_eq_zero M I s hI U x hx p hp
  exact ⟨V, hVU, hpV, r, (homOfTopSection_val_app M s V r).trans hr⟩

end AlgebraicGeometry.Scheme.Modules.SectionRestrictionSequenceAux

end
