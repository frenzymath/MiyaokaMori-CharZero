import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionUnitEpi
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorLineBundleExact
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # The restriction sequence of an effective Cartier divisor

Let `X` be a scheme, `D` an effective Cartier divisor on `X` with closed immersion `i : D → X`, and `M`
a line bundle on `X`. Then there is `f : M ⊗ O_X(D)^∨ → M` such that
`0 → M ⊗ O_X(D)^∨ →(f) M →(η) i_*i^*M → 0` is short exact, where `η` is the unit of the
pullback–pushforward adjunction.

Proof:
1. The ideal sheaf sequence `0 → I_D → O_X → i_*O_D → 0` is short exact: `I_D.toModules` is by
   definition the kernel of `O_X → i_*O_D`, which is an epimorphism for a closed immersion
   (`Scheme.IdealSheafData.shortExact_kernel_unit`).
2. Tensoring with the line bundle `M` preserves short exactness (`M` is invertible in the monoidal
   category `X.Modules`, so `− ⊗ M` is an autoequivalence), giving
   `0 → I_D ⊗ M → O_X ⊗ M → i_*O_D ⊗ M → 0`.
3. Left term: `O_X(D) = I_D^∨` by definition, the double dual `(I_D^∨)^∨ ≅ I_D` (`dual_dual`, valid for
   locally free sheaves of finite type; `I_D` is a line bundle), and the braiding give
   `I_D ⊗ M ≅ M ⊗ O_X(D)^∨`.
4. Middle term: `O_X ⊗ M ≅ M` (`unitTensorIso`, `tensorIsoTensorObj`).
5. Right term: the projection formula `i_*O_D ⊗ M ≅ i_*(i^*M)`, under which `O_X ⊗ M → i_*O_D ⊗ M`
   corresponds to the adjunction unit `η_M` (`exists_pushforwardUnit_tensor_iso_compat`: the
   isomorphism is braiding ≫ the canonical projection formula isomorphism `θ_{M,O_D}` ≫ `i_*(ρ)`, and
   compatibility is the categorical identity `projFormulaHom_tensorUnit_right_unit_compat`).
6. Transport the short exact sequence of step 2 along the three isomorphisms of steps 3–5
   (`ShortComplex.isoMk`, `shortExact_of_iso`); `f` is the transported left morphism.
Sources: Stacks 01WV, 01X0, 01E8.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace
open CategoryTheory.Functor.OplaxMonoidal
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [instF : F.OplaxMonoidal]

/-- **The projection formula comparison map at `N = 𝟙` is compatible with the adjunction unit** (pure
category theory; a property of `projFormulaHom`).
Let `F ⊣ G` with `F` oplax monoidal (unit `η_F : F 𝟙 ⟶ 𝟙`) and `u := η_𝟙 ≫ G η_F : 𝟙 ⟶ G 𝟙`. Then
`(M ◁ u) ≫ θ_{M,𝟙} ≫ G(ρ_{F M}) = ρ_M ≫ η_M`.
Proof: take adjoint transposes. The left side transposes to `F(M ◁ u) ≫ δ_{M,G𝟙} ≫ (F M ◁ ε_𝟙) ≫ ρ`;
naturality of `δ` in the second variable gives `δ_{M,𝟙} ≫ (F M ◁ (F u ≫ ε_𝟙)) ≫ ρ`;
`F u ≫ ε_𝟙 = F η_𝟙 ≫ ε_{F 𝟙} ≫ η_F = η_F` (naturality of the counit and the triangle identity); finally
`δ_{M,𝟙} ≫ (F M ◁ η_F) ≫ ρ_{F M} = F(ρ_M)` is the oplax right unit law. The right side transposes to
`F(ρ_M)`. -/
theorem projFormulaHom_tensorUnit_right_unit_compat (M : C) :
    (M ◁ (adj.unit.app (𝟙_ C) ≫ G.map (η F))) ≫ adj.projFormulaHom M (𝟙_ D) ≫
        G.map (ρ_ (F.obj M)).hom =
      (ρ_ M).hom ≫ adj.unit.app M := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm,
    homEquiv_symm_projFormulaHom, homEquiv_naturality_left_symm, homEquiv_symm_unit, comp_id,
    assoc, ← δ_natural_right_assoc, ← whiskerLeft_comp_assoc, F.map_comp, assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [adj.counit_naturality, adj.left_triangle_components_assoc]
  have h : δ F M (𝟙_ C) ≫ F.obj M ◁ η F = F.map (ρ_ M).hom ≫ (ρ_ (F.obj M)).inv := by
    rw [oplax_right_unitality F M, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, id_comp]
  rw [← assoc, h, assoc, Iso.inv_hom_id, comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- `O_X ⊗ M ≅ M`, written with the monoidal structure. -/
def Scheme.Modules.unitTensorMonoidalIso (M : X.Modules) :
    MonoidalCategoryStruct.tensorObj (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (Scheme.Modules.tensorIsoTensorObj (SheafOfModules.unit X.ringCatSheaf) M).symm ≪≫
    Scheme.Modules.unitTensorIso M

namespace Scheme.Modules

/-- The `hom` of `unitTensorMonoidalIso M` is the left unitor `λ_ M` of the monoidal category (the
`eqToHom (unit_eq_tensorUnit X)` inside `unitTensorIso` is the identity). -/
theorem unitTensorMonoidalIso_hom_eq (M : X.Modules) :
    (Scheme.Modules.unitTensorMonoidalIso M).hom = (λ_ M).hom := by
  simp only [Scheme.Modules.unitTensorMonoidalIso, Scheme.Modules.unitTensorIso, Iso.trans_hom,
    Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [whiskerRightIso_hom, eqToIso.hom]
  have : eqToHom (Scheme.Modules.unit_eq_tensorUnit X) = 𝟙 _ := by with_unfolding_all rfl
  erw [this, id_whiskerRight, id_comp]

/-- Mathlib's `unitToPushforwardObjUnit` (`O_X → i_*O_Z`, given by `i^♯` on sections) equals the unit
`η_{O_X} : O_X → i_*i^*O_X` of the pullback–pushforward adjunction followed by `i_*` of the unit
`i^*O_X → O_Z` of the oplax monoidal structure of the pullback.
Proof: `pullback_η` identifies the oplax unit with `pullbackObjUnitToUnit`, and Mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` says its adjoint transpose is
`unitToPushforwardObjUnit`; then unfold `homEquiv_unit`. -/
theorem unitToPushforwardObjUnit_eq_unit_comp {Z : Scheme.{u}} (i : Z ⟶ X) :
    SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pushforward i).map (η (Scheme.Modules.pullback i)) := by
  have h : (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
      (η (Scheme.Modules.pullback i)) =
        SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := by
    have : (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).isRightAdjoint
    rw [Scheme.Modules.pullback_η]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  exact h.symm.trans ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv_unit _ _ _)

end Scheme.Modules


/-- The projection formula is compatible with the adjunction unit: there is an isomorphism
`e : i_*O_D ⊗ M ≅ i_*i^*M` under which `O_X → i_*O_D` tensored with `M` corresponds to the unit
`η_M : M ⟶ i_*i^*M`.
Proof: `e :=` braiding `(i_*O_D ⊗ M ≅ M ⊗ i_*O_D)` ≫ the canonical projection formula isomorphism
`θ_{M,O_D} : M ⊗ i_*O_D ≅ i_*(i^*M ⊗ O_D)` (`projectionFormulaIso`, which needs `M` to be a line bundle)
≫ `i_*`(right unitor). Compatibility: `unitToPushforwardObjUnit = η_{O_X} ≫ i_*(η_oplax)`
(`unitToPushforwardObjUnit_eq_unit_comp`), naturality of the braiding replaces `u ▷ M` by
`β_{O_X,M} ≫ (M ◁ u)`, then the categorical identity `projFormulaHom_tensorUnit_right_unit_compat`,
`braiding_rightUnitor` (`β ≫ ρ = λ`) and `unitTensorMonoidalIso_hom_eq` (`= λ`).
Source: Stacks 01E8 (projection formula). The hypothesis `[M.IsLineBundle]` is what the available
projection formula needs; the statement holds for arbitrary `M`. -/
theorem EffectiveCartierDivisor.exists_pushforwardUnit_tensor_iso_compat
    (D : EffectiveCartierDivisor X) (M : X.Modules) [M.IsLineBundle] :
    ∃ e : (MonoidalCategoryStruct.tensorObj (C := X.Modules)
            ((SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom D.idealSheaf.subschemeι)).obj
              (SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf)) M
          ≅ (Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
              ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)),
      (MonoidalCategoryStruct.whiskerRight (C := X.Modules)
          (SheafOfModules.unitToPushforwardObjUnit
            (Scheme.Hom.toRingCatSheafHom D.idealSheaf.subschemeι)) M) ≫ e.hom
        = (Scheme.Modules.unitTensorMonoidalIso M).hom ≫
          (Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app M := by
  have key : (((Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app
          (𝟙_ X.Modules) ≫
        (Scheme.Modules.pushforward D.idealSheaf.subschemeι).map
          (η (Scheme.Modules.pullback D.idealSheaf.subschemeι))) ▷ M) ≫
      (β_ ((Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
        (𝟙_ D.idealSheaf.subscheme.Modules)) M).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).projFormulaHom M
        (𝟙_ D.idealSheaf.subscheme.Modules) ≫
      (Scheme.Modules.pushforward D.idealSheaf.subschemeι).map
        (ρ_ ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)).hom =
      (λ_ M).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app M := by
    rw [BraidedCategory.braiding_naturality_left_assoc, ← braiding_rightUnitor, assoc]
    congr 1
    exact (Scheme.Modules.pullbackPushforwardAdjunction
      D.idealSheaf.subschemeι).projFormulaHom_tensorUnit_right_unit_compat M
  refine ⟨β_ _ M ≪≫
    Scheme.Modules.projectionFormulaIso D.idealSheaf.subschemeι M (𝟙_ _) ≪≫
    (Scheme.Modules.pushforward D.idealSheaf.subschemeι).mapIso (ρ_ _), ?_⟩
  rw [Scheme.Modules.unitTensorMonoidalIso_hom_eq,
    Scheme.Modules.unitToPushforwardObjUnit_eq_unit_comp]
  exact key

theorem EffectiveCartierDivisor.exists_shortExact_restriction {X : Scheme.{u}}
    (D : EffectiveCartierDivisor X) (M : X.Modules) [M.IsLineBundle] :
    ∃ (f : Scheme.Modules.tensor M (Scheme.Modules.dual D.lineBundle) ⟶ M)
      (w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app M = 0),
      (ShortComplex.mk f
        ((Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app M) w).ShortExact := by
  -- step 1: the ideal sheaf short exact sequence
  have hS := Scheme.IdealSheafData.shortExact_kernel_unit D.idealSheaf
  -- step 2: tensor with the line bundle M
  obtain ⟨T, e₁, e₂, e₃, h₁, h₂, hT⟩ :=
    Scheme.Modules.shortExact_tensor_lineBundle M _ hS
  -- step 3: left term I_D ⊗ M ≅ M ⊗ O(D)^∨
  have : (Scheme.IdealSheafData.toModules D.idealSheaf).IsLineBundle := D.isLineBundle
  obtain ⟨dd⟩ := Scheme.Modules.dual_dual (Scheme.IdealSheafData.toModules D.idealSheaf)
  -- O_X(D) is `EffCartier.sheaf = dualSheaf I_D` (not sheafified), so `Modules.dual O_X(D)` is not
  -- definitionally `(I_D^∨)^∨`; insert the isomorphism `dualDualSheafIsoOld`
  let dd' : Scheme.IdealSheafData.toModules D.idealSheaf ≅ Scheme.Modules.dual D.lineBundle :=
    dd.symm ≪≫ (Scheme.Modules.dualDualSheafIsoOld
      (Scheme.IdealSheafData.toModules D.idealSheaf)).symm
  let a₁ : T.X₁ ≅ Scheme.Modules.tensor M (Scheme.Modules.dual D.lineBundle) :=
    e₁ ≪≫ β_ _ _ ≪≫ whiskerLeftIso M dd' ≪≫ (Scheme.Modules.tensorIsoTensorObj M _).symm
  -- step 4: middle term O_X ⊗ M ≅ M
  let a₂ : T.X₂ ≅ M := e₂ ≪≫ Scheme.Modules.unitTensorMonoidalIso M
  -- step 5: right term
  obtain ⟨ee, hee⟩ := EffectiveCartierDivisor.exists_pushforwardUnit_tensor_iso_compat D M
  let a₃ : T.X₃ ≅ (Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
      ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M) := e₃ ≪≫ ee
  -- right square: T.g ≫ a₃.hom = a₂.hom ≫ η
  have hcomm : a₂.hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction D.idealSheaf.subschemeι).unit.app M
        = T.g ≫ a₃.hom := by
    dsimp only [a₂, a₃, Iso.trans_hom]
    rw [Category.assoc, ← hee, ← Category.assoc, ← h₂, Category.assoc]
  refine ⟨a₁.inv ≫ T.f ≫ a₂.hom, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hcomm, ← Category.assoc T.f T.g, T.zero,
      Limits.zero_comp, Limits.comp_zero]
  · refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk a₁ a₂ a₃ ?_ ?_) hT
    · exact a₁.hom_inv_id_assoc _
    · exact hcomm

end AlgebraicGeometry

end
