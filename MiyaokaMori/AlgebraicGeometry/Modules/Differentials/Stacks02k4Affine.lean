import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02k4Alg
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.Stacks02k4Maps

/-! # The first fundamental sequence on a small affine open

Stacks 02K4 / 01UX on a small affine open. Fix `f : X ⟶ Y`, `g : Y ⟶ S` and affine opens
`W ⊆ S`, `V ⊆ g⁻¹W`, `U ⊆ f⁻¹V`; write `A = Γ(S, W)`, `B = Γ(Y, V)`, `C = Γ(X, U)`. Under the
identifications `Γ(U, Ω_{X/S}) ≅ Ω[C⁄A]`, `Γ(U, Ω_{X/Y}) ≅ Ω[C⁄B]`, `Γ(V, Ω_{Y/S}) ≅ Ω[B⁄A]`
(`Omega_appIso`, Stacks 01UT) and the base-change description of `Γ(U, f^*Ω_{Y/S})`
(`isIso_transpose_pullbackSectionsNative`, Stacks 01I9), the maps `α = Omega.baseChangeMap` and
`β = Omega.compMap` become `KaehlerDifferential.mapBaseChange A B C` and `KaehlerDifferential.map A B C C`.
Hence on sections over `U`:

* `β` is surjective (`KaehlerDifferential.map_surjective`);
* `ker β = im α` (`KaehlerDifferential.exact_mapBaseChange_map`, Stacks 00RS);
* if `f` is smooth, `α` is injective (`KaehlerDifferential.mapBaseChange_injective_of_formallySmooth`,
  because `B → C` is then a smooth ring map, `HasRingHomProperty.appLE`).

Source: Stacks 02K4 (proof: reduce to the affine statement 04B2 / 00TA); the tangent sequence
(2.2) in §2.1 of the paper. The surjectivity of
`C ⊗[B] Γ(V, Ω_{Y/S}) → Γ(U, f^*Ω_{Y/S})` uses `Scheme.Modules.isIso_transpose_pullbackSectionsNative`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry

local notation "dΩ[" f "]" => Omega.homEquivDerivation f (Omega f) (𝟙 (Omega f))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 01I9 on sections.** For `V ⊆ Y`, `U ⊆ f⁻¹V` affine and `M` quasi-coherent, every section of
`f^*M` over `U` is a `Γ(X, U)`-linear combination of restricted pullbacks `(f^*s)|_U` of sections `s` of
`M` over `V`. (Surjectivity half of `isIso_transpose_pullbackSectionsNative`.) -/
theorem Scheme.Modules.mem_span_range_pullbackSectionsOn (M : Y.Modules) [M.IsQuasicoherent]
    {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (x : Γ((Scheme.Modules.pullback f).obj M, U)) :
    x ∈ Submodule.span Γ(X, U) (Set.range (Scheme.Modules.pullbackSectionsOn f M V U e)) := by
  have := Scheme.Modules.isIso_transpose_pullbackSectionsNative f M V hV U hU e
  set T := ((ModuleCat.extendRestrictScalarsAdj (f.appLE V U e).hom).homEquiv _ _).symm
    (Scheme.Modules.pullbackSectionsNative f M V U e) with hT
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso T).2 x
  have h1 : ∀ s : Γ(M, V), T ((1 : Γ(X, U)) ⊗ₜ s) = Scheme.Modules.pullbackSectionsOn f M V U e s := by
    intro s
    have := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (f := (f.appLE V U e).hom) T s
    rw [hT, Equiv.apply_symm_apply] at this
    exact this.symm
  -- The `+`, `0`, `⊗ₜ` produced by `induction_on` and those expected by `map_add`/`map_smul` carry
  -- defeq but syntactically different instances (`ModuleCat` carrier vs `TensorProduct`), so every step
  -- below is a term (checked up to defeq) rather than a `rw`/`simp`.
  set N := Submodule.span Γ(X, U) (Set.range (Scheme.Modules.pullbackSectionsOn f M V U e)) with hN
  induction t using TensorProduct.induction_on with
  | zero => exact (congrArg (fun z => z ∈ N) (_root_.map_zero T.hom)).mpr (Submodule.zero_mem N)
  | tmul c s =>
    -- `c` comes with the `restrictScalars` carrier type; rename it to an element of `Γ(X, U)` so that
    -- ring instances are found, and take the tensors from Mathlib's statements (never write them by hand).
    obtain ⟨c', rfl⟩ : ∃ c' : Γ(X, U), c' = c := ⟨c, rfl⟩
    have h3 := ModuleCat.ExtendScalars.smul_tmul (f.appLE V U e).hom
      (M := ModuleCat.of Γ(Y, V) Γ(M, V)) c' 1 s
    rw [mul_one] at h3
    have hc := (congrArg T.hom h3.symm).trans (_root_.map_smul T.hom c' _)
    exact (congrArg (fun z => z ∈ N) hc).mpr
      (Submodule.smul_mem N c' (Submodule.subset_span ⟨s, (h1 s).symm⟩))
  | add a b ha hb =>
    exact (congrArg (fun z => z ∈ N) (_root_.map_add T.hom a b)).mpr (Submodule.add_mem N ha hb)

variable {S : Scheme.{u}} (g : Y ⟶ S)
variable {W : S.Opens} (hW : IsAffineOpen W) {V : Y.Opens} (hV : IsAffineOpen V)
  {U : X.Opens} (hU : IsAffineOpen U)

/-- `U ⊆ (f ≫ g)⁻¹W` from `U ⊆ f⁻¹V`, `V ⊆ g⁻¹W`. -/
theorem Omega.le_comp_preimage (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) : U ≤ (f ≫ g) ⁻¹ᵁ W :=
  e₁.trans ((Opens.map f.base).map (homOfLE e₀)).le

/-- `β = Omega.compMap` on sections over `U` is `KaehlerDifferential.map A B C C` under `Omega_appIso`. -/
theorem Omega.appIso_compMap_app (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) (x : Γ(Omega (f ≫ g), U)) :
    letI := (g.appLE W V e₀).hom.toAlgebra
    letI := (f.appLE V U e₁).hom.toAlgebra
    letI := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
    haveI : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
    Omega_appIso f hV hU e₁ ((Omega.compMap f g).app U x) =
      KaehlerDifferential.map Γ(S, W) Γ(Y, V) Γ(X, U) Γ(X, U)
        (Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) x) := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  set ι₂ := Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) with hι₂
  set ι₁ := Omega_appIso f hV hU e₁ with hι₁
  obtain ⟨ω, rfl⟩ := ι₂.symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D Γ(S, W) Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨a, rfl⟩ := hω
    have h1 : ι₂.symm (KaehlerDifferential.D Γ(S, W) Γ(X, U) a) = (dΩ[f ≫ g]).d (X := op U) a :=
      (LinearEquiv.symm_apply_eq ι₂).mpr
        (Omega_appIso_d (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) a).symm
    refine (congrArg ι₁ ((congrArg ((Omega.compMap f g).app U) h1).trans
      (Omega.compMap_app_d f g U a))).trans ?_
    refine (Omega_appIso_d f hV hU e₁ a).trans ?_
    exact (KaehlerDifferential.map_D Γ(S, W) Γ(Y, V) Γ(X, U) Γ(X, U) a).symm
  | zero => simp only [map_zero]
  | add ω₁ ω₂ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul c ω _ h => rw [map_smul, Scheme.Modules.Hom.app_smul, map_smul, h, map_smul]

/-- `Ω[B⁄A] → Γ(U, f^*Ω_{Y/S})`, `ω ↦ (f^*(ι₀⁻¹ ω))|_U` where `ι₀ : Γ(V, Ω_{Y/S}) ≅ Ω[B⁄A]`; it is
`B`-linear for the `B`-module structure on the target obtained through `f.appLE V U e₁ : B → C`. -/
def Omega.pullbackSectionsKaehler (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) :
    letI := (g.appLE W V e₀).hom.toAlgebra
    letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
      Module.compHom _ (f.appLE V U e₁).hom
    Ω[Γ(Y, V)⁄Γ(S, W)] →ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
  letI := (g.appLE W V e₀).hom.toAlgebra
  letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    Module.compHom _ (f.appLE V U e₁).hom
  { toFun := fun ω =>
      Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁ ((Omega_appIso g hW hV e₀).symm ω)
    map_add' := fun ω₁ ω₂ =>
      (congrArg (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁)
        (_root_.map_add (Omega_appIso g hW hV e₀).symm ω₁ ω₂)).trans (_root_.map_add _ _ _)
    map_smul' := fun b ω =>
      (congrArg (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁)
        (_root_.map_smul (Omega_appIso g hW hV e₀).symm b ω)).trans
        (Scheme.Modules.pullbackSectionsOn_smul_native f (Omega g) V U e₁ b _) }

/-- `α = Omega.baseChangeMap` on `(f^*(ι₀⁻¹ ω))|_U` is `KaehlerDifferential.map A A B C ω` under `ι₂`
(generator form of "`α` is the base-change map `mapBaseChange`"). -/
theorem Omega.appIso_baseChangeMap_app_pullbackSectionsOn (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V)
    (ω : letI := (g.appLE W V e₀).hom.toAlgebra; Ω[Γ(Y, V)⁄Γ(S, W)]) :
    letI := (g.appLE W V e₀).hom.toAlgebra
    letI := (f.appLE V U e₁).hom.toAlgebra
    letI := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
    haveI : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
    Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁)
        ((Omega.baseChangeMap f g).app U
          (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁ ((Omega_appIso g hW hV e₀).symm ω))) =
      KaehlerDifferential.map Γ(S, W) Γ(S, W) Γ(Y, V) Γ(X, U) ω := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  set ι₂ := Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) with hι₂
  set ι₀ := Omega_appIso g hW hV e₀ with hι₀
  have hω : ω ∈ Submodule.span Γ(Y, V) (Set.range (KaehlerDifferential.D Γ(S, W) Γ(Y, V))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨b, rfl⟩ := hω
    have h1 : ι₀.symm (KaehlerDifferential.D Γ(S, W) Γ(Y, V) b) = (dΩ[g]).d (X := op V) b :=
      (LinearEquiv.symm_apply_eq ι₀).mpr (Omega_appIso_d g hW hV e₀ b).symm
    refine (congrArg ι₂ ((congrArg ((Omega.baseChangeMap f g).app U)
      (congrArg (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁) h1)).trans
        (Omega.baseChangeMap_app_pullbackSectionsOn_d f g V U e₁ b))).trans ?_
    refine (Omega_appIso_d (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) _).trans ?_
    exact (KaehlerDifferential.map_D Γ(S, W) Γ(S, W) Γ(Y, V) Γ(X, U) b).symm
  | zero => simp only [map_zero]
  | add ω₁ ω₂ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul b ω _ h =>
    have h2 : Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁ (ι₀.symm (b • ω)) =
        (f.appLE V U e₁).hom b • Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁ (ι₀.symm ω) :=
      (congrArg (Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁) (_root_.map_smul ι₀.symm b ω)).trans
        (Scheme.Modules.pullbackSectionsOn_smul_native f (Omega g) V U e₁ b _)
    rw [h2, Scheme.Modules.Hom.app_smul, _root_.map_smul, h, _root_.map_smul]
    exact (algebraMap_smul Γ(X, U) b _).symm

/-- The base-change lift `C ⊗[B] Ω[B⁄A] → Γ(U, f^*Ω_{Y/S})` of `Omega.pullbackSectionsKaehler`. -/
def Omega.baseChangeSections (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) :
    letI := (g.appLE W V e₀).hom.toAlgebra
    letI := (f.appLE V U e₁).hom.toAlgebra
    TensorProduct Γ(Y, V) Γ(X, U) Ω[Γ(Y, V)⁄Γ(S, W)] →ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
  letI := (g.appLE W V e₀).hom.toAlgebra
  letI := (f.appLE V U e₁).hom.toAlgebra
  letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    Module.compHom _ (f.appLE V U e₁).hom
  haveI : IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange Γ(X, U) (Omega.pullbackSectionsKaehler f g hW hV e₀ e₁)

/-- `ι₂ ∘ α ∘ Ψ = mapBaseChange A B C`: under the affine identifications, `α` is the base-change map of
Kähler differentials (Stacks 01UX / 00RS). -/
theorem Omega.appIso_baseChangeMap_app_baseChangeSections (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V)
    (t : letI := (g.appLE W V e₀).hom.toAlgebra; letI := (f.appLE V U e₁).hom.toAlgebra
      TensorProduct Γ(Y, V) Γ(X, U) Ω[Γ(Y, V)⁄Γ(S, W)]) :
    letI := (g.appLE W V e₀).hom.toAlgebra
    letI := (f.appLE V U e₁).hom.toAlgebra
    letI := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
    haveI : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
    Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁)
        ((Omega.baseChangeMap f g).app U (Omega.baseChangeSections f g hW hV e₀ e₁ t)) =
      KaehlerDifferential.mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U) t := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  let _ : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    Module.compHom _ (f.appLE V U e₁).hom
  have : IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c ω =>
    have h1 : Omega.baseChangeSections f g hW hV e₀ e₁ (c ⊗ₜ ω) =
        c • Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁ ((Omega_appIso g hW hV e₀).symm ω) :=
      LinearMap.liftBaseChange_tmul _ _ c ω
    rw [h1, Scheme.Modules.Hom.app_smul, _root_.map_smul,
      Omega.appIso_baseChangeMap_app_pullbackSectionsOn f g hW hV hU e₀ e₁ ω,
      KaehlerDifferential.mapBaseChange_tmul]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

include hU in
/-- `Ψ = Omega.baseChangeSections` is surjective: by Stacks 01I9 every section of `f^*Ω_{Y/S}` over `U` is
a `C`-combination of restricted pullbacks `(f^*s)|_U`, and `(f^*s)|_U = Ψ(1 ⊗ ι₀ s)`. -/
theorem Omega.baseChangeSections_surjective (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) :
    Function.Surjective (Omega.baseChangeSections f g hW hV e₀ e₁) := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    Module.compHom _ (f.appLE V U e₁).hom
  have : IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj (Omega g), U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hqc : (Omega g).IsQuasicoherent := Omega_isQuasicoherent g
  intro x
  have hx := Scheme.Modules.mem_span_range_pullbackSectionsOn f (Omega g) hV hU e₁ x
  rw [← LinearMap.mem_range]
  refine (Submodule.span_le.mpr ?_) hx
  rintro _ ⟨s, rfl⟩
  refine ⟨(1 : Γ(X, U)) ⊗ₜ (Omega_appIso g hW hV e₀ s), ?_⟩
  have h1 : Omega.baseChangeSections f g hW hV e₀ e₁ ((1 : Γ(X, U)) ⊗ₜ (Omega_appIso g hW hV e₀ s)) =
      (1 : Γ(X, U)) • Scheme.Modules.pullbackSectionsOn f (Omega g) V U e₁
        ((Omega_appIso g hW hV e₀).symm (Omega_appIso g hW hV e₀ s)) :=
    LinearMap.liftBaseChange_tmul _ _ _ _
  rw [h1, one_smul, LinearEquiv.symm_apply_apply]

section Conclusions

include hW hV hU in
/-- **Stacks 01UX on sections over a small affine `U`: `β : Ω_{X/S} → Ω_{X/Y}` is surjective.**
Under `ι₁ : Γ(U, Ω_{X/Y}) ≅ Ω[C⁄B]`, `ι₂ : Γ(U, Ω_{X/S}) ≅ Ω[C⁄A]`, `β` is `KaehlerDifferential.map A B C C`
(`appIso_compMap_app`), which is surjective (`KaehlerDifferential.map_surjective`, Stacks 00RS). -/
theorem Omega.compMap_app_surjective_affine (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) :
    Function.Surjective ((Omega.compMap f g).app U).hom := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  set ι₂ := Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) with hι₂
  intro z
  obtain ⟨ω, hω⟩ := KaehlerDifferential.map_surjective Γ(S, W) Γ(Y, V) Γ(X, U)
    (Omega_appIso f hV hU e₁ z)
  refine ⟨ι₂.symm ω, (Omega_appIso f hV hU e₁).injective ?_⟩
  have h := Omega.appIso_compMap_app f g hW hV hU e₀ e₁ (ι₂.symm ω)
  exact h.trans ((congrArg (KaehlerDifferential.map Γ(S, W) Γ(Y, V) Γ(X, U) Γ(X, U))
    (ι₂.apply_symm_apply ω)).trans hω)

include hW hV hU in
/-- **Stacks 01UX on sections over a small affine `U`: `ker β ⊆ im α`.** Under the identifications
`ι₁, ι₂`, `β` is `KaehlerDifferential.map A B C C`; if `β x = 0` then `ι₂ x` lies in the kernel of that map,
hence (Stacks 00RS, `KaehlerDifferential.exact_mapBaseChange_map`) in the image of `mapBaseChange A B C`,
`ι₂ x = mapBaseChange t`; and `mapBaseChange t = ι₂ (α (Ψ t))` (`appIso_baseChangeMap_app_baseChangeSections`),
so `x = α (Ψ t)`. -/
theorem Omega.compMap_app_exact_affine (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V)
    (x : Γ(Omega (f ≫ g), U)) (hx : (Omega.compMap f g).app U x = 0) :
    ∃ y, (Omega.baseChangeMap f g).app U y = x := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  set ι₂ := Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) with hι₂
  have h1 : KaehlerDifferential.map Γ(S, W) Γ(Y, V) Γ(X, U) Γ(X, U) (ι₂ x) = 0 := by
    have h := Omega.appIso_compMap_app f g hW hV hU e₀ e₁ x
    exact h.symm.trans ((congrArg (Omega_appIso f hV hU e₁) hx).trans
      (_root_.map_zero (Omega_appIso f hV hU e₁)))
  obtain ⟨t, ht⟩ := (KaehlerDifferential.exact_mapBaseChange_map Γ(S, W) Γ(Y, V) Γ(X, U) (ι₂ x)).mp h1
  refine ⟨Omega.baseChangeSections f g hW hV e₀ e₁ t, ι₂.injective ?_⟩
  exact (Omega.appIso_baseChangeMap_app_baseChangeSections f g hW hV hU e₀ e₁ t).trans ht

include hW hV hU in
/-- **Stacks 02K4 on sections over a small affine `U`: for `f` smooth, `α : f^*Ω_{Y/S} → Ω_{X/S}` is
injective.** `B → C` is `f.appLE V U e₁`, a smooth ring map because `f` is smooth
(`HasRingHomProperty.appLE`), hence formally smooth; every section of `f^*Ω_{Y/S}` over `U` is `Ψ t` for some
`t ∈ C ⊗[B] Ω[B⁄A]` (`baseChangeSections_surjective`, Stacks 01I9); `ι₂ (α (Ψ t)) = mapBaseChange A B C t`
and `mapBaseChange` is injective for formally smooth `B → C`
(`KaehlerDifferential.mapBaseChange_injective_of_formallySmooth`, Stacks 00S2 + 031J), so `α (Ψ t) = 0`
forces `t = 0`. -/
theorem Omega.baseChangeMap_app_injective_affine [Smooth f] (e₀ : V ≤ g ⁻¹ᵁ W) (e₁ : U ≤ f ⁻¹ᵁ V) :
    Function.Injective ((Omega.baseChangeMap f g).app U).hom := by
  let _ := (g.appLE W V e₀).hom.toAlgebra
  let _ := (f.appLE V U e₁).hom.toAlgebra
  let _ := ((f ≫ g).appLE W U (Omega.le_comp_preimage f g e₀ e₁)).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.appLE_comp_appLE f g W V U e₀ e₁)).symm
  have hsm : Algebra.FormallySmooth Γ(Y, V) Γ(X, U) :=
    (HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ e₁).formallySmooth
  set ι₂ := Omega_appIso (f ≫ g) hW hU (Omega.le_comp_preimage f g e₀ e₁) with hι₂
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := Omega.baseChangeSections_surjective f g hW hV hU e₀ e₁ x
  have h1 : KaehlerDifferential.mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U) t = 0 :=
    (Omega.appIso_baseChangeMap_app_baseChangeSections f g hW hV hU e₀ e₁ t).symm.trans
      ((congrArg ι₂ hx).trans (_root_.map_zero ι₂))
  have h2 : t = 0 :=
    KaehlerDifferential.mapBaseChange_injective_of_formallySmooth Γ(S, W) Γ(Y, V) Γ(X, U)
      (h1.trans (_root_.map_zero _).symm)
  rw [h2, _root_.map_zero]

end Conclusions

end AlgebraicGeometry

end
