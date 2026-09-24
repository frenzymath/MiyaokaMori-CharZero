import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionConstructions
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear

/-! # The functional of a section, on sections

Glue for the frame coordinate on a fibre of a total space (`totalSpace_exists_coordinate_of_isFrame`).
Everything here is at the variable level (`g : T ⟶ X` a morphism, `V` a module, `Tv : Over X`).

* `homEquiv_symm_app_unit`: the adjoint transpose `g^*M → N` of `φ : M → g_*N` sends the unit section
  `η(m)` to `φ(m)` (`Adjunction.homEquiv_unit`).
* `pullback_map_app_unit`: `g^*(ψ)` on unit sections is `η(ψ m)` (naturality of the unit).
* `pullbackUnitIso_hom_app_unit_one'`: `g^*O_X ≅ O_T` sends `η(1)` to `1` over any `g⁻¹U`
  (`homEquiv_pullbackUnitIso_hom_app_one`).
* `totalSpace.functionalOfSection_app`: on sections, the functional `ψ_s : g^*(V^∨) → O_T` of
  `s ∈ Γ(T, g^*V)` is `φ ↦ (g^*O ≅ O)(g^*(ev)(δ⁻¹(φ ⊗ s|)))` (unfolding `ρ⁻¹` and the whiskering with
  `homOfTopSection s`: `rightUnitor_inv_app_eq_tensorSections`, `whiskerLeft_app_tensorSections`,
  `homOfTopSection_app_one`).
* `totalSpace.functionalOfSection_app_unit_of_res_eq_smul`: if `⟨t, e⟩ = 1` on `U` (`t ∈ Γ(V^∨, U)`,
  `e ∈ Γ(V, U)`) and `s|_{g⁻¹U} = c • η(e)`, then `ψ_s(η(t)) = c`.
* `totalSpace.functionalOfSection_tautologicalSection`: the functional of the tautological section
  `totalSpaceHomEquiv V (Tot V) (𝟙)` is `tautologicalFunctional V` (the two triangle identities of
  `TotalSpaceSectionConstructions`; `structureHom` is `toAlgebraMap` at `𝟙`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The adjoint transpose of `φ : M ⟶ g_*N` on unit sections: `(φ^♭)(η(m)) = φ(m)`. -/
theorem homEquiv_symm_app_unit (g : T ⟶ X) {M : X.Modules} {N : T.Modules}
    (φ : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj N) (U : X.Opens) (m : Γ(M, U)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm φ).app (g ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) =
      (show Γ(N, g ⁻¹ᵁ U) from φ.app U m) := by
  have h := CategoryTheory.Adjunction.homEquiv_unit
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g) M N
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm φ)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun ψ : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj N => ψ.app U m) h).symm

/-- `g^*ψ` on unit sections: `g^*ψ (η(m)) = η(ψ m)` (naturality of the unit). -/
theorem pullback_map_app_unit (g : T ⟶ X) {M N : X.Modules} (ψ : M ⟶ N) (U : X.Opens) (m : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).map ψ).app (g ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app U (ψ.app U m) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality ψ
  exact (congrArg (fun χ : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N) => χ.app U m) h).symm

/-- `g^*O_X ≅ O_T` sends `η(1)` to `1`, over any `g⁻¹U`. -/
theorem pullbackUnitIso_hom_app_unit_one' (g : T ⟶ X) (U : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (SheafOfModules.unit X.ringCatSheaf)).app U (1 : Γ(X, U))) = (1 : Γ(T, g ⁻¹ᵁ U)) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom_app_one g U
  have h2 := homEquiv_symm_app_unit g
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom) U (1 : Γ(X, U))
  rw [Equiv.symm_apply_apply] at h2
  exact h2.trans h1

/-- **Evaluation of `(g^*O ≅ O) ∘ g^*(ev) ∘ δ⁻¹` on `η(t) ⊗ (c • η(e))`** (variable level, plain morphism
`g : T ⟶ X`): if `⟨t, e⟩ = 1` on `U`, the result is `c`. -/
theorem pullbackUnitIso_pullback_dualEv_tensorObjIso_inv_unit_smul_unit (g : T ⟶ X) (V : X.Modules) (U : X.Opens)
    (t : Γ(AlgebraicGeometry.Scheme.Modules.dual V, U)) (e : Γ(V, U))
    (hte : (AlgebraicGeometry.Scheme.Modules.dualEv V).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual V) V U t e) =
        (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U))))
    (c : Γ(T, g ⁻¹ᵁ U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullback g).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app (g ⁻¹ᵁ U)
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g
            (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app (g ⁻¹ᵁ U)
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.dual V))
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj V) (g ⁻¹ᵁ U)
            (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              (AlgebraicGeometry.Scheme.Modules.dual V)).app U t)
            (c • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj V, g ⁻¹ᵁ U) from
              ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app V).app U e))))) = c := by
  -- step 1: the tensor section is `c • δ(η(t ⊗ e))`
  have h1 : AlgebraicGeometry.Scheme.Modules.tensorSections
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.dual V))
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj V) (g ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (AlgebraicGeometry.Scheme.Modules.dual V)).app U t)
      (c • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj V, g ⁻¹ᵁ U) from
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app V).app U e)) =
      c • (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g
        (AlgebraicGeometry.Scheme.Modules.dual V) V).app (g ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V)).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual V) V U t e)) := by
    refine (AlgebraicGeometry.Scheme.Modules.tensorSections_smul_right _ _ _ c _ _ _ rfl).trans ?_
    exact congrArg (fun y : Γ(CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.dual V))
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj V), g ⁻¹ᵁ U) => c • y)
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections g
        (AlgebraicGeometry.Scheme.Modules.dual V) V U t e).symm
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
    (((AlgebraicGeometry.Scheme.Modules.pullback g).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app (g ⁻¹ᵁ U)
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g
        (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app (g ⁻¹ᵁ U) z))) h1).trans ?_
  -- step 2: `δ⁻¹ ∘ δ = id`
  have hinv : ∀ z, (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g
      (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app (g ⁻¹ᵁ U)
        ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g
          (AlgebraicGeometry.Scheme.Modules.dual V) V).app (g ⁻¹ᵁ U) z) = z := fun z =>
    congrArg (fun ψ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V) ⟶ _ =>
      ψ.app (g ⁻¹ᵁ U) z)
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g
        (AlgebraicGeometry.Scheme.Modules.dual V) V).hom_inv_id
  have h2 : ∀ z, (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso g
      (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app (g ⁻¹ᵁ U)
        (c • (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g
          (AlgebraicGeometry.Scheme.Modules.dual V) V).app (g ⁻¹ᵁ U) z) = c • z := fun z =>
    (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ c _).trans (congrArg (fun y => c • y) (hinv z))
  refine (congrArg (fun y => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
    (((AlgebraicGeometry.Scheme.Modules.pullback g).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app (g ⁻¹ᵁ U) y))
    (h2 _)).trans ?_
  -- step 3: `g^*(ev)(c • η(t ⊗ e)) = c • η(⟨t, e⟩) = c • η(1)`
  have h3 : ∀ z : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V), g ⁻¹ᵁ U),
      z = ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V)).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual V) V U t e) →
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app (g ⁻¹ᵁ U)
        (c • z) =
      c • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf), g ⁻¹ᵁ U) from
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (SheafOfModules.unit X.ringCatSheaf)).app U (1 : Γ(X, U))) := by
    intro z hz
    subst hz
    exact (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ c _).trans (congrArg
      (fun y : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf), g ⁻¹ᵁ U) =>
        c • y)
      ((AlgebraicGeometry.Scheme.Modules.pullback_map_app_unit g (AlgebraicGeometry.Scheme.Modules.dualEv V) U _).trans
        (congrArg (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (SheafOfModules.unit X.ringCatSheaf)).app U) hte)))
  refine (congrArg (fun y => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U) y)
    (h3 _ rfl)).trans ?_
  -- step 4: `(g^*O ≅ O)(c • η(1)) = c • 1 = c` (read in `Γ(T, g⁻¹U)`, where `•` is `*`)
  refine (AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ c _).trans ?_
  have h4 : (show Γ(T, g ⁻¹ᵁ U) from (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).app U (1 : Γ(X, U)))) = 1 :=
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_unit_one' g U
  exact (congrArg (fun y : Γ(T, g ⁻¹ᵁ U) => c * y) h4).trans (mul_one c)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.totalSpace

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The functional of a section, on sections**: `ψ_s(φ) = (g^*O ≅ O)(g^*(ev)(δ⁻¹(φ ⊗ s|_W)))`. -/
theorem functionalOfSection_app (V : X.Modules) (Tv : CategoryTheory.Over X)
    (s : Γ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V, ⊤)) (W : Tv.left.Opens)
    (φ : Γ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V), W)) :
    (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V Tv s).app W φ =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso Tv.hom).hom.app W
        (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app W
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso Tv.hom
              (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app W
            (AlgebraicGeometry.Scheme.Modules.tensorSections
              ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))
              ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) W φ
              (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V).res le_top s)))) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.rightUnitor_inv_app_eq_tensorSections
    ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V)) W φ
  have h2 := AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections
    ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) s)
    W φ (1 : Γ(Tv.left, W))
  have h3 := AlgebraicGeometry.Scheme.Modules.DualZigzag.homOfTopSection_app_one
    ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) s W
  have h12 : ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ◁
      AlgebraicGeometry.Scheme.Modules.homOfTopSection ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) s).app W
        ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))).inv.app W φ) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))
        ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) W φ
        (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V).res le_top s) :=
    (congrArg (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V) ◁
      AlgebraicGeometry.Scheme.Modules.homOfTopSection ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) s).app W)
      h1).trans (h2.trans (congrArg (AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))
        ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) W φ) h3))
  exact congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso Tv.hom).hom.app W
    (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app W
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso Tv.hom
        (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app W z))) h12

/-- **Evaluating the functional on a pulled-back dual frame.** If `⟨t, e⟩ = 1` on `U` and
`s|_{g⁻¹U} = c • η(e)`, then `ψ_s(η(t)) = c`. -/
theorem functionalOfSection_app_unit_of_res_eq_smul (V : X.Modules) (Tv : CategoryTheory.Over X)
    (s : Γ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V, ⊤)) (U : X.Opens)
    (t : Γ(AlgebraicGeometry.Scheme.Modules.dual V, U)) (e : Γ(V, U))
    (hte : (AlgebraicGeometry.Scheme.Modules.dualEv V).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual V) V U t e) =
        (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U))))
    (c : Γ(Tv.left, Tv.hom ⁻¹ᵁ U))
    (hs : ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V).res le_top s =
      c • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V, Tv.hom ⁻¹ᵁ U) from
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction Tv.hom).unit.app V).app U e)) :
    (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V Tv s).app (Tv.hom ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction Tv.hom).unit.app
          (AlgebraicGeometry.Scheme.Modules.dual V)).app U t) = c := by
  refine (functionalOfSection_app V Tv s (Tv.hom ⁻¹ᵁ U) _).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso Tv.hom).hom.app (Tv.hom ⁻¹ᵁ U)
    (((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).map (AlgebraicGeometry.Scheme.Modules.dualEv V)).app
      (Tv.hom ⁻¹ᵁ U)
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso Tv.hom
        (AlgebraicGeometry.Scheme.Modules.dual V) V).inv.app (Tv.hom ⁻¹ᵁ U)
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj (AlgebraicGeometry.Scheme.Modules.dual V))
          ((AlgebraicGeometry.Scheme.Modules.pullback Tv.hom).obj V) (Tv.hom ⁻¹ᵁ U)
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction Tv.hom).unit.app
            (AlgebraicGeometry.Scheme.Modules.dual V)).app U t) z)))) hs).trans ?_
  exact AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_pullback_dualEv_tensorObjIso_inv_unit_smul_unit
    Tv.hom V U t e hte c

/-- **The functional of the tautological section** `ξ = totalSpaceHomEquiv V (Tot V) (𝟙)` is the degree-one
part of the algebra map of `𝟙`, transposed: `ψ_ξ = (symGen ≫ ι_1 ≫ toAlgebraMap 𝟙)^♭ = functionalOfHomCore 𝟙`.
(`toAlgebraMap … 𝟙` is `relativeSpec.structureHom` by definition, so this is
`totalSpace.tautologicalFunctional V` of `TotLineAffineOverBaseDefs`, not imported here.) Proof: `ξ` is
`sectionOfFunctionalCore (functionalOfHomCore 𝟙)` by definition and `functionalOfSectionCore ∘
sectionOfFunctionalCore = id` (`functionalOfSectionCore_sectionOfFunctionalCore`). -/
theorem functionalOfSection_totalSpaceHomEquiv_id (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V (AlgebraicGeometry.Scheme.totalSpace V)
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
          (CategoryTheory.CategoryStruct.id _)) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.Scheme.totalSpace V).hom).homEquiv _ _).symm
        (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫
          AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total
            (AlgebraicGeometry.Scheme.totalSpace V) (CategoryTheory.CategoryStruct.id _)) := by
  change AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V (AlgebraicGeometry.Scheme.totalSpace V)
    (AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore V (AlgebraicGeometry.Scheme.totalSpace V)
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _))) = _
  rw [AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore_sectionOfFunctionalCore]
  rfl

end AlgebraicGeometry.Scheme.totalSpace

end
