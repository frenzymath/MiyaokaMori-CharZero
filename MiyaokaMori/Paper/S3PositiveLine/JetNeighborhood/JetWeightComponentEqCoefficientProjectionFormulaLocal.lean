import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroSection

/-! # The projection formula on a local section times a frame (helper of `JetWeightComponentEqCoefficient`)

Everything here is stated at the variable level (`g : T ⟶ X` a morphism of schemes, `M` a module on `X`,
`N` a module on `T`).

* `projectionFormulaHom_app_tensorSections`: on sections over `U ⊆ X`, the projection-formula map
  `θ_g : M ⊗ g_*N ⟶ g_*(g^*M ⊗ N)` sends `a ⊗ c` (`a ∈ Γ(M, U)`, `c ∈ Γ(N, g⁻¹U)`) to `η(a) ⊗ c`.
  Proof: `θ_g = η_{M ⊗ g_*N} ≫ g_*(δ ≫ (g^*M ◁ ε))` (`Adjunction.homEquiv_unit`); the unit sends `a ⊗ c` to
  `η(a ⊗ c)`, `δ` sends it to `η(a) ⊗ η(c)` (`pullbackTensorObjHom_app_unit_tensorSections`), and the counit sends
  `η(c)` back to `c` (`pushforward_counit_app_unit_app`).
* `pullbackSectionToPushforward_res_eq_tensorSections`: if `P ∈ Γ(T, g^*M)` restricts on `g⁻¹U` to `c • η(a)`,
  then `pullbackSectionToPushforward g M P` (the section of `M ⊗ g_*O_T` attached to `P` by the inverse of the
  projection formula) restricts on `U` to `a ⊗ c`.
  Proof: `pullbackSectionToPushforward` is `θ_g⁻¹ ∘ (ρ_)⁻¹` on global sections; both commute with restriction
  (`Hom.app_res`); `(ρ_)⁻¹(c • η(a)) = c • (η(a) ⊗ 1) = η(a) ⊗ c` (`rightUnitor_inv_app_eq_tensorSections`,
  `tensorSections_smul_right`); and `θ_g(a ⊗ c) = η(a) ⊗ c` by the first lemma.

This is step (4) of the docstring of `BasedJet.exists_pieceSection_generatesAt` at the variable level
(the coefficient `c_{ℓ,q}` is read off in the frame `a`; proof of Lemma 3.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T X : AlgebraicGeometry.Scheme.{u}}

/-- **The inverse projection formula on a multiple of a frame.** If `P|_{g⁻¹U} = c • η(a)` then
`(pullbackSectionToPushforward g M P)|_U = a ⊗ c`. (`θ_g(a ⊗ c) = η(a) ⊗ c` is
`projectionFormulaHom_app_tensorSections`, `TotLineMonomialZeroSection.lean`.) -/
theorem pullbackSectionToPushforward_res_eq_tensorSections (g : T ⟶ X) (M : X.Modules) [M.IsLineBundle]
    (P : Γ((pullback g).obj M, ⊤)) (U : X.Opens) (a : Γ(M, U)) (c : Γ(T, g ⁻¹ᵁ U))
    (hP : ((pullback g).obj M).res (le_top : g ⁻¹ᵁ U ≤ ⊤) P =
      c • (show Γ((pullback g).obj M, g ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction g).unit.app M).app U a)) :
    (M ⊗ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)).res (le_top : U ≤ ⊤)
        (pullbackSectionToPushforward g M P) =
      tensorSections M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) U a
        (show Γ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf), U) from c) := by
  -- the section `η(a) ⊗ c` of `g^*M ⊗ O_T` over `g⁻¹U`
  have h1 : ((ρ_ ((pullback g).obj M)).inv.app (g ⁻¹ᵁ U))
      (c • (show Γ((pullback g).obj M, g ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction g).unit.app M).app U a)) =
      tensorSections ((pullback g).obj M) (SheafOfModules.unit T.ringCatSheaf) (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U a) c := by
    rw [Hom.app_smul, rightUnitor_inv_app_eq_tensorSections]
    have h3 := tensorSections_smul_right ((pullback g).obj M) (SheafOfModules.unit T.ringCatSheaf) (g ⁻¹ᵁ U) c
      (((pullbackPushforwardAdjunction g).unit.app M).app U a) (1 : Γ(T, g ⁻¹ᵁ U)) _ rfl
    exact h3.symm.trans (congrArg (fun z : Γ(T, g ⁻¹ᵁ U) =>
      tensorSections ((pullback g).obj M) (SheafOfModules.unit T.ringCatSheaf) (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U a) z) ((smul_eq_mul c 1).trans (mul_one c)))
  have h2 := projectionFormulaHom_app_tensorSections g M (SheafOfModules.unit T.ringCatSheaf) U a c
  have h4 := Hom.app_res (projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).inv (le_top : U ≤ ⊤)
    ((ρ_ ((pullback g).obj M)).inv.app ⊤ P)
  have h5 := Hom.app_res (ρ_ ((pullback g).obj M)).inv (le_top : g ⁻¹ᵁ U ≤ ⊤) P
  have h6 : ((pullback g).obj M ⊗ SheafOfModules.unit T.ringCatSheaf).res (le_top : g ⁻¹ᵁ U ≤ ⊤)
      ((ρ_ ((pullback g).obj M)).inv.app ⊤ P) =
      tensorSections ((pullback g).obj M) (SheafOfModules.unit T.ringCatSheaf) (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U a) c := by
    refine h5.symm.trans ?_
    rw [hP]
    exact h1
  have h7 : (projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).inv.app U
      ((projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).hom.app U
        (tensorSections M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) U a c)) =
      tensorSections M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) U a c :=
    congrArg (fun φ : M ⊗ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      M ⊗ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) => φ.app U
      (tensorSections M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) U a c))
    (projectionFormulaIso g M (SheafOfModules.unit T.ringCatSheaf)).hom_inv_id
  unfold pullbackSectionToPushforward
  refine Eq.trans ?_ h7
  refine Eq.trans h4.symm ?_
  refine congrArg _ ?_
  exact h6.trans h2.symm

end AlgebraicGeometry.Scheme.Modules

end
