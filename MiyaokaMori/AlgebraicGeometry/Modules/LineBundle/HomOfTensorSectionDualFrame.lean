import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.LineBundleDualEvalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pwUniformExponent
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.DenominatorMapsOnTensor
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple

/-! # Sections of `F ⊗ L^{⊗n}` as morphisms `L^{⊗-n} ⟶ F`

**A global section of `F ⊗ L^{⊗n}` gives a morphism `L^{⊗-n} ⟶ F`, and on an open `U` where a
section `e` of `L^{⊗n}` is a frame it sends the dual frame `e^∨` to the `F`-coefficient of the
section.** This is step 4 of Stacks 01Q3 (1)⇒(5)⇒(7) as used for the finite type quotient on a
nonvanishing locus: there `e = θ(s^{⊗k})`, `U = X_s`, `σ_j|_U = t_j ⊗ e|_U`, and the morphisms
`φ_j := φ_{σ_j} : L^{⊗-n} ⟶ F` with `φ_j(e^∨|_W) = t_j|_W` (`W ≤ U`) are the ones whose direct sum is
surjective on `U`.

Here `L ^ (-(n : ℤ))` is the integer tensor power `zpow`: for `n = 0` it is the structure sheaf `O_X`
(`-(0 : ℤ)` reduces to `Int.ofNat 0`), for `n ≥ 1` it is
`moduleNegativePower L n = moduleTensorPower (moduleSheafDual L) n` (the `n`-th power of the dual,
left-recursive), while `tensorPow L n` is the right-recursive tensor power.

Route: the dual frame is taken in the internal Hom `𝓗om(P, O_X)` (`IsFrame.dualFrameSheaf`, whose
evaluation on `e` is `1`), and transported to `L^{⊗-n}` along an isomorphism `L^{⊗-n} ≅ 𝓗om(P, O_X)`
built purely from the cancellation `P ⊗ L^{⊗-n} ≅ O_X` and the evaluation isomorphism
`𝓗om(P, O_X) ⊗ P ≅ O_X` (Stacks 01CT, `isIso_internalHomEval_unit`). Steps:
1. `DualFrameHom.tensorPowCancelIso`: `tensorPow L k ⊗ moduleTensorPower D k ≅ 𝟙_` for any
   `c : L ⊗ D ≅ 𝟙_`, by induction on `k` (middle swap `(P ⊗ L) ⊗ (D_k ⊗ D) ≅ (P ⊗ D_k) ⊗ (L ⊗ D)` and
   the braiding); with `D = L^∨` and `c` from `SheafOfModules.IsLineBundle.tensor_dual_iso` this is the
   cancellation `L^{⊗n} ⊗ L^{⊗-n} ≅ O_X` (the two cases `n = 0`, `n = k + 1` of `zpow` are definitional).
2. `DualFrameHom.exists_pairing_section_eq_one`: for a line bundle `P`, `c₀ : P ⊗ Q ≅ 𝟙_`, and
   `U ≤ X_e`, there are a pairing `c : tensor P Q ⟶ O_X` and `ε ∈ Γ(U, Q)` with `c(e|_U ⊗ ε) = 1`.
   `e|_U` is a frame on `U` (`isFrame_res_nonvanishingLocus`, Stacks 01CY), `ε_D := e^∨` in
   `𝓗om(P, O_X)`, `θ : Q ≅ 𝓗om(P, O_X)` as above, `ε := θ⁻¹(ε_D)`,
   `c := (P ◁ θ) ≫ β_ ≫ ev`; then `c(e ⊗ ε) = ev(e^∨ ⊗ e) = coord_e(e) = 1`.
3. `DualFrameHom.homOfTensorSection`: for `σ ∈ Γ(X, F ⊗ P)` let `σ̂ : O_X ⟶ F ⊗ P` be
   `AlgebraicGeometry.Scheme.Modules.homOfSection` (`r ↦ r • σ|_W`); the morphism is
   `Q ≅ O_X ⊗ Q → (F ⊗ P) ⊗ Q ≅ F ⊗ (P ⊗ Q) → F ⊗ O_X ≅ F`. On sections over `W` with
   `σ|_W = t' ⊗ e'` it is `y ↦ c(e' ⊗ y) • t'` (`homOfTensorSection_app_of_res_eq`), tracking a pure
   tensor through `unitTensorIso_hom_app_moduleTensorSection`, `whiskerRight_app_tensorSections''`,
   `homOfSection_app_one`, `tensorAssocIso_hom_app_moduleTensorSection`,
   `whiskerLeft_app_tensorSections''` and `rightUnitor_app_tensorSections`.
4. `exists_hom_of_pairing_section_eq_one` assembles 3 with `c(e|_W ⊗ ε|_W) = (c(e|_U ⊗ ε))|_W = 1`
   (`moduleTensorSection_restrict`, naturality `Hom.app_map'`), and the main theorem specialises to
   `P = tensorPow L n`, `Q = L ^ (-(n : ℤ))`.

Edge cases: `n = 0` (`L^{⊗0} = O_X`, `e` a unit on `U`, `ε = (e|_U)^{-1}`, `φ_σ(r) = r • (coefficient)`);
`U = ∅` (all section modules are zero; any `ε`, any `φ`); `F = 0` (`φ = 0`); `X_e = ∅` forces `U = ∅`.
The statement does not need `F` quasi-coherent, `X` quasi-compact, or `U` affine. The factor order
`F ⊗ L^{⊗n}` (`F` on the left) is that of Stacks 01Q3, proof of (1)⇒(5), and of
`exists_tensorPow_section_restrict_eq`.

References: Stacks 01Q3 (`properties-proposition-characterize-ample`), proof of (1)⇒(5): "the sections
`σ_j` of `F ⊗ L^{⊗n}` define a map `⊕ L^{⊗-n} → F` which is surjective on `X_s`"; Stacks 01CT
(invertible sheaves, `L ⊗ L^{⊗-1} ≅ O_X`, `𝓗om(L, O_X) ⊗ L ≅ O_X`); Stacks 01CY (nonvanishing locus
of a section of an invertible sheaf). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.DualFrameHom

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restriction of `1 ∈ Γ(O_X, W)` in the structure sheaf viewed as a module. -/
theorem unit_res_one {W W' : X.Opens} (h : W' ≤ W) :
    AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit X.ringCatSheaf : X.Modules) h
      (1 : Γ(X, W)) = (1 : Γ(X, W')) := by
  change (X.presheaf.map (homOfLE h).op).hom (1 : Γ(X, W)) = 1
  exact map_one _

/-- Morphisms of `O_X`-modules commute with restriction (`res` spelling of `Hom.app_map'`). -/
theorem hom_app_res {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  AlgebraicGeometry.Scheme.Modules.Hom.app_map' φ h x

/-- Restriction of a pure tensor section of `Modules.tensor` (restatement of
`moduleTensorSection_restrict` with `res`). -/
theorem tensor_res_moduleTensorSection {A B : X.Modules} {V U : X.Opens} (h : V ≤ U)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensor A B).res h (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (A.res h a) (B.res h b) :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (homOfLE h) a b

/-- `tensorUnitIso` on a pure tensor section: `t ⊗ r ↦ r • t`. -/
theorem tensorUnitIso_hom_app_moduleTensorSection (F : X.Modules) (U : X.Opens)
    (t : Γ(F, U)) (r : Γ(X, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso F).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (N := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) t r) =
      r • t := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorUnitIso F).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (N := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) t r) =
      (ρ_ F).hom.app U
        ((F ◁ CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections F
            (SheafOfModules.unit X.ringCatSheaf : X.Modules) U t r)) := by
    show ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F _).hom ≫
      (F ◁ CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) ≫
      (ρ_ F).hom).app U _ = _
    erw [DenominatorMaps.comp_app_apply, DenominatorMaps.comp_app_apply]
  have h3 : (F ◁ CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections F
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) U t r) =
      AlgebraicGeometry.Scheme.Modules.tensorSections F (𝟙_ X.Modules) U t r :=
    whiskerLeft_app_tensorSections''
      (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) U t r
  rw [h1, h3]
  exact AlgebraicGeometry.Scheme.Modules.rightUnitor_app_tensorSections F U t r

/-- **Cancellation of tensor powers**: for `c : L ⊗ D ≅ 𝟙_`, `tensorPow L k ⊗ moduleTensorPower D k ≅ 𝟙_`
(right-recursive power of `L` against left-recursive power of `D`). Induction on `k`: the step is
`(P ⊗ L) ⊗ (D ⊗ D_k) ≅ (P ⊗ L) ⊗ (D_k ⊗ D) ≅ (P ⊗ D_k) ⊗ (L ⊗ D) ≅ 𝟙_ ⊗ 𝟙_ ≅ 𝟙_`. -/
def tensorPowCancelIso {L D : X.Modules} (c : L ⊗ D ≅ 𝟙_ X.Modules) :
    (k : ℕ) → (AlgebraicGeometry.Scheme.Modules.tensorPow L k ⊗ AlgebraicGeometry.Scheme.Modules.moduleTensorPower D k ≅
      𝟙_ X.Modules)
  | 0 =>
    AlgebraicGeometry.Scheme.Modules.unitTensorUnitIso X ≪≫
      CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)
  | k + 1 =>
    CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D k)) ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso _ (β_ D (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D k)) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorMiddleSwapIso
        (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D k) D ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (tensorPowCancelIso c k) c ≪≫
      λ_ (𝟙_ X.Modules)

/-- **The dual frame, transported to `Q`.** For a line bundle `P`, an isomorphism `c₀ : P ⊗ Q ≅ 𝟙_`,
`e ∈ Γ(X, P)` and `U ≤ X_e`, there are a pairing `c : tensor P Q ⟶ O_X` and a section `ε ∈ Γ(U, Q)`
with `c(e|_U ⊗ ε) = 1`. Proof: `e|_U` is a frame on `U` (Stacks 01CY, `isFrame_res_nonvanishingLocus`);
its dual frame `e^∨ ∈ Γ(U, 𝓗om(P, O_X))` (`IsFrame.dualFrameSheaf`) satisfies `ev(e^∨ ⊗ e|_U) = 1`;
`ev : 𝓗om(P, O_X) ⊗ P ⟶ O_X` is an isomorphism (Stacks 01CT, `isIso_internalHomEval_unit`), so
`θ := Q ≅ 𝟙_ ⊗ Q ≅ (𝓗om ⊗ P) ⊗ Q ≅ 𝓗om ⊗ (P ⊗ Q) ≅ 𝓗om ⊗ 𝟙_ ≅ 𝓗om`; put `ε := θ⁻¹(e^∨)` and
`c := (P ◁ θ) ≫ β_ ≫ ev`. -/
theorem exists_pairing_section_eq_one {P Q : X.Modules} [P.IsLineBundle]
    (c₀ : P ⊗ Q ≅ 𝟙_ X.Modules) (e : Γ(P, ⊤)) {U : X.Opens} (hU : U ≤ P.nonvanishingLocus e) :
    ∃ (c : AlgebraicGeometry.Scheme.Modules.tensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
      (ε : Γ(Q, U)),
      c.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) ε) = (1 : Γ(X, U)) := by
  have hf : IsFrame P U (P.res le_top e) := by
    have h := (AlgebraicGeometry.Scheme.Modules.isFrame_res_nonvanishingLocus P e).restrict hU
    rwa [res_res] at h
  have := AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_unit P
  let D : X.Modules := AlgebraicGeometry.Scheme.Modules.internalHom P (SheafOfModules.unit X.ringCatSheaf)
  let ev : D ⊗ P ⟶ SheafOfModules.unit X.ringCatSheaf :=
    AlgebraicGeometry.Scheme.Modules.internalHomEval P (SheafOfModules.unit X.ringCatSheaf)
  let evIso : D ⊗ P ≅ 𝟙_ X.Modules :=
    CategoryTheory.asIso ev ≪≫ CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)
  let θ : Q ≅ D :=
    (λ_ Q).symm ≪≫ CategoryTheory.MonoidalCategory.whiskerRightIso evIso.symm Q ≪≫ α_ D P Q ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso D c₀ ≪≫ ρ_ D
  let εD : Γ(D, U) := hf.dualFrameSheaf
  refine ⟨(AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj P Q).hom ≫ (P ◁ θ.hom) ≫ (β_ P D).hom ≫ ev,
    θ.inv.app U εD, ?_⟩
  have h1 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj P Q).hom ≫ (P ◁ θ.hom) ≫ (β_ P D).hom ≫
      ev).app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) (θ.inv.app U εD)) =
      ev.app U ((β_ P D).hom.app U ((P ◁ θ.hom).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections P Q U (P.res le_top e) (θ.inv.app U εD)))) := by
    rfl
  rw [h1, whiskerLeft_app_tensorSections'', DenominatorMaps.iso_hom_app_inv_app,
    AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections]
  have h2 := AlgebraicGeometry.Scheme.Modules.internalHomEval_tensorSections_unit P
    (SheafOfModules.unit X.ringCatSheaf) U hf.dualFrameLocal (P.res le_top e)
  refine h2.trans ?_
  have h3 := hf.localHomEval_dualFrameLocal (1 : Γ(X, U))
  rw [one_smul] at h3
  exact h3

/-- **The morphism `Q ⟶ F` defined by a section `σ ∈ Γ(X, F ⊗ P)` and a pairing `c : P ⊗ Q ⟶ O_X`**:
`Q ≅ O_X ⊗ Q → (F ⊗ P) ⊗ Q ≅ F ⊗ (P ⊗ Q) → F ⊗ O_X ≅ F`, the middle arrow being `σ̂ ▷ Q` with
`σ̂ = AlgebraicGeometry.Scheme.Modules.homOfSection _ σ : O_X ⟶ F ⊗ P`, `r ↦ r • σ|`. -/
def homOfTensorSection {P Q F : X.Modules}
    (c : AlgebraicGeometry.Scheme.Modules.tensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F P, ⊤)) : Q ⟶ F :=
  (AlgebraicGeometry.Scheme.Modules.unitTensorIso Q).inv ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ Q).hom ≫
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
      (AlgebraicGeometry.Scheme.Modules.homOfSection (AlgebraicGeometry.Scheme.Modules.tensor F P) σ) Q) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensor F P) Q).inv ≫
    (AlgebraicGeometry.Scheme.Modules.tensorAssocIso F P Q).hom ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F (AlgebraicGeometry.Scheme.Modules.tensor P Q)).hom ≫
    CategoryTheory.MonoidalCategoryStruct.whiskerLeft (C := X.Modules) F c ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F _).inv ≫
    (AlgebraicGeometry.Scheme.Modules.tensorUnitIso F).hom

/-- `(unitTensorIso Q).inv y = 1 ⊗ y`. -/
theorem unitTensorIso_inv_app (Q : X.Modules) (W : X.Opens) (y : Γ(Q, W)) :
    (AlgebraicGeometry.Scheme.Modules.unitTensorIso Q).inv.app W y =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (1 : Γ(X, W)) y := by
  have h := AlgebraicGeometry.Scheme.Modules.unitTensorIso_hom_app_moduleTensorSection Q W (1 : Γ(X, W)) y
  rw [one_smul] at h
  conv_lhs => rw [← h]
  exact DenominatorMaps.iso_inv_app_hom_app _ W _

/-- **Value of `homOfTensorSection c σ` on sections over `W`** where `σ|_W = t' ⊗ e'` is a pure tensor:
`y ↦ c(e' ⊗ y) • t'`. -/
theorem homOfTensorSection_app_of_res_eq {P Q F : X.Modules}
    (c : AlgebraicGeometry.Scheme.Modules.tensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F P, ⊤)) {W : X.Opens} (t' : Γ(F, W)) (e' : Γ(P, W))
    (h : (AlgebraicGeometry.Scheme.Modules.tensor F P).res le_top σ = AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' e')
    (y : Γ(Q, W)) :
    (homOfTensorSection c σ).app W y =
      (show Γ(X, W) from c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) • t' := by
  have s0 : (homOfTensorSection c σ).app W y =
      (AlgebraicGeometry.Scheme.Modules.tensorUnitIso F).hom.app W
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F (SheafOfModules.unit X.ringCatSheaf)).inv.app W
          ((CategoryTheory.MonoidalCategoryStruct.whiskerLeft (C := X.Modules) F c).app W
            ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F
                (AlgebraicGeometry.Scheme.Modules.tensor P Q)).hom.app W
              ((AlgebraicGeometry.Scheme.Modules.tensorAssocIso F P Q).hom.app W
                ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
                    (AlgebraicGeometry.Scheme.Modules.tensor F P) Q).inv.app W
                  ((CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
                      (AlgebraicGeometry.Scheme.Modules.homOfSection
                        (AlgebraicGeometry.Scheme.Modules.tensor F P) σ) Q).app W
                    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
                        (SheafOfModules.unit X.ringCatSheaf) Q).hom.app W
                      ((AlgebraicGeometry.Scheme.Modules.unitTensorIso Q).inv.app W y)))))))) := by
    unfold homOfTensorSection
    simp only [DenominatorMaps.comp_app_apply]
  have s1 : (AlgebraicGeometry.Scheme.Modules.unitTensorIso Q).inv.app W y =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (1 : Γ(X, W)) y :=
    unitTensorIso_inv_app Q W y
  have s2 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (SheafOfModules.unit X.ringCatSheaf) Q).hom.app W
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (1 : Γ(X, W)) y) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (SheafOfModules.unit X.ringCatSheaf) Q W (1 : Γ(X, W)) y :=
    rfl
  have s3 : (CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.homOfSection (AlgebraicGeometry.Scheme.Modules.tensor F P) σ) Q).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (SheafOfModules.unit X.ringCatSheaf) Q W (1 : Γ(X, W)) y) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.tensor F P) Q W
        (AlgebraicGeometry.Scheme.Modules.Hom.app
          (AlgebraicGeometry.Scheme.Modules.homOfSection (AlgebraicGeometry.Scheme.Modules.tensor F P) σ) W
          (1 : Γ(X, W))) y :=
    whiskerRight_app_tensorSections'' _ W _ y
  have s4 : AlgebraicGeometry.Scheme.Modules.Hom.app
        (AlgebraicGeometry.Scheme.Modules.homOfSection (AlgebraicGeometry.Scheme.Modules.tensor F P) σ) W
        (1 : Γ(X, W)) = AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' e' := by
    rw [← h]
    exact AlgebraicGeometry.Scheme.Modules.homOfSection_app_one (AlgebraicGeometry.Scheme.Modules.tensor F P) σ W
  have s5 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensor F P) Q).inv.app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.tensor F P) Q W
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' e') y) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' e') y :=
    tensorIsoTensorObj_inv_app_tensorSections' _ _ W _ y
  have s6 : (AlgebraicGeometry.Scheme.Modules.tensorAssocIso F P Q).hom.app W
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := AlgebraicGeometry.Scheme.Modules.tensor F P)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' e') y) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y) :=
    tensorAssocIso_hom_app_moduleTensorSection F P Q W t' e' y
  have s7 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F (AlgebraicGeometry.Scheme.Modules.tensor P Q)).hom.app W
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t' (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections F (AlgebraicGeometry.Scheme.Modules.tensor P Q) W t'
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y) :=
    rfl
  have s8 : (CategoryTheory.MonoidalCategoryStruct.whiskerLeft (C := X.Modules) F c).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections F (AlgebraicGeometry.Scheme.Modules.tensor P Q) W t'
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections F (SheafOfModules.unit X.ringCatSheaf) W t'
        (c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) :=
    whiskerLeft_app_tensorSections'' c W t' _
  have s9 : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F (SheafOfModules.unit X.ringCatSheaf)).inv.app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections F (SheafOfModules.unit X.ringCatSheaf) W t'
          (c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y))) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (N := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) t'
        (c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) :=
    tensorIsoTensorObj_inv_app_tensorSections' F _ W t' _
  have s10 : (AlgebraicGeometry.Scheme.Modules.tensorUnitIso F).hom.app W
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (N := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) t'
          (c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y))) =
      (show Γ(X, W) from c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e' y)) • t' :=
    tensorUnitIso_hom_app_moduleTensorSection F W t' _
  rw [s0, s1, s2, s3, s4, s5]
  erw [s6, s7, s8, s9, s10]

/-- **Assembly (variable level).** Given a pairing `c : tensor P Q ⟶ O_X`, `e ∈ Γ(X, P)` and
`ε ∈ Γ(U, Q)` with `c(e|_U ⊗ ε) = 1`, every `σ ∈ Γ(X, F ⊗ P)` with `σ|_U = t ⊗ e|_U` gives a morphism
`φ : Q ⟶ F` with `φ(ε|_W) = t|_W` for all `W ≤ U`: `φ := homOfTensorSection c σ`, and
`c(e|_W ⊗ ε|_W) = (c(e|_U ⊗ ε))|_W = 1`. -/
theorem exists_hom_of_pairing_section_eq_one {P Q F : X.Modules}
    (c : AlgebraicGeometry.Scheme.Modules.tensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : Γ(P, ⊤)) {U : X.Opens} (ε : Γ(Q, U))
    (hc : c.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) ε) = (1 : Γ(X, U)))
    (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F P, ⊤)) (t : Γ(F, U))
    (hσ : (AlgebraicGeometry.Scheme.Modules.tensor F P).res le_top σ =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection t (P.res le_top e)) :
    ∃ φ : Q ⟶ F, ∀ (W : X.Opens) (hW : W ≤ U), φ.app W (Q.res hW ε) = F.res hW t := by
  refine ⟨homOfTensorSection c σ, fun W hW => ?_⟩
  have hres : (AlgebraicGeometry.Scheme.Modules.tensor F P).res le_top σ =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res hW t) (P.res hW (P.res le_top e)) := by
    rw [← res_res _ hW le_top, hσ, tensor_res_moduleTensorSection]
  rw [homOfTensorSection_app_of_res_eq c σ (F.res hW t) (P.res hW (P.res le_top e)) hres]
  have hpair : c.app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res hW (P.res le_top e)) (Q.res hW ε)) =
      (1 : Γ(X, W)) := by
    have e1 : AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res hW (P.res le_top e)) (Q.res hW ε) =
        (AlgebraicGeometry.Scheme.Modules.tensor P Q).res hW
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) ε) :=
      (tensor_res_moduleTensorSection hW _ _).symm
    have e2 := hom_app_res c hW (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) ε)
    have e3 : AlgebraicGeometry.Scheme.Modules.res (SheafOfModules.unit X.ringCatSheaf : X.Modules) hW
        (c.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P.res le_top e) ε)) = (1 : Γ(X, W)) := by
      rw [hc]
      exact unit_res_one hW
    rw [e1]
    exact e2.trans e3
  rw [hpair, one_smul]

end AlgebraicGeometry.Scheme.Modules.DualFrameHom

/-- **Sections of `F ⊗ L^{⊗n}` as morphisms `L^{⊗-n} ⟶ F`, evaluated on the dual frame.** Let
`e ∈ Γ(X, L^{⊗n})` and let `U` be an open contained in the nonvanishing locus `X_e`. Then there is a
section `ε ∈ Γ(U, L^{⊗-n})` (the dual frame of `e|_U`) such that for every global section `σ` of
`F ⊗ L^{⊗n}` and every `t ∈ Γ(U, F)` with `σ|_U = t ⊗ e|_U` there is a morphism `φ : L^{⊗-n} ⟶ F` with
`φ(ε|_W) = t|_W` for every open `W ≤ U`. See the module docstring for the proof. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_zpow_neg_section_hom_of_tensor_section
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (F : X.Modules) (n : ℕ)
    (e : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) {U : X.Opens}
    (hU : U ≤ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus e) :
    ∃ ε : Γ(L ^ (-(n : ℤ)), U),
      ∀ (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n), ⊤)) (t : Γ(F, U)),
        (AlgebraicGeometry.Scheme.Modules.tensor F
            (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).presheaf.map
            (homOfLE (le_top : U ≤ ⊤)).op σ =
          AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
            ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.map
              (homOfLE (le_top : U ≤ ⊤)).op e) →
        ∃ φ : L ^ (-(n : ℤ)) ⟶ F, ∀ (W : X.Opens) (hW : W ≤ U),
          φ.app W ((L ^ (-(n : ℤ))).presheaf.map (homOfLE hW).op ε) =
            F.presheaf.map (homOfLE hW).op t := by
  obtain ⟨c₀⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso L
  let c : L ⊗ AlgebraicGeometry.Scheme.Modules.dual L ≅ 𝟙_ X.Modules :=
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L (AlgebraicGeometry.Scheme.Modules.dual L)).symm ≪≫
      c₀ ≪≫ CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)
  have hiso : Nonempty (AlgebraicGeometry.Scheme.Modules.tensorPow L n ⊗ L ^ (-(n : ℤ)) ≅ 𝟙_ X.Modules) := by
    cases n with
    | zero => exact ⟨AlgebraicGeometry.Scheme.Modules.DualFrameHom.tensorPowCancelIso c 0⟩
    | succ k => exact ⟨AlgebraicGeometry.Scheme.Modules.DualFrameHom.tensorPowCancelIso c (k + 1)⟩
  obtain ⟨ciso⟩ := hiso
  obtain ⟨c', ε, hc⟩ :=
    AlgebraicGeometry.Scheme.Modules.DualFrameHom.exists_pairing_section_eq_one ciso e hU
  exact ⟨ε, fun σ t hσ =>
    AlgebraicGeometry.Scheme.Modules.DualFrameHom.exists_hom_of_pairing_section_eq_one c' e ε hc σ t hσ⟩

end
