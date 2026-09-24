import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsoluteTheta
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsolutePullbackMul
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The morphisms `θ_n : O(n) ⟶ φ_*O_Y` and their transposes `χ_n : φ^*O(n) ⟶ O_Y` (Stacks 01O4 (2))

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean` (existence of the twist family). Setting: `𝒜` a graded ring, `Φ : A →+* Γ(Y, O)` with
`Φ(irrelevant) = (1)`, `φ := Proj.fromOfGlobalSections 𝒜 Φ hΦ : Y ⟶ Proj 𝒜`.

* `thetaHom n : O(n) ⟶ φ_*O_Y`: the section maps `θ_n` of `…AbsoluteTheta.lean` (additive, `φ^♯`-linear, natural),
  packaged with `PresheafOfModules.homMk`.
* `chi n : φ^*O(n) ⟶ O_Y`: the adjoint transpose of `thetaHom n`; `chi_app_pullbackUnitHom`:
  `χ_n(η g) = θ_n g` and `chi_app_pullbackSectionsOn`: `χ_n(η g|_B) = θ_n(g)|_B`.
* `chi_app_pullbackUnitHom_twistSection`: (F') at the level of `η`: `χ_n(η(a/1)) = Φ(a)`.
* `mulHom_comp_chi`: (M') as an equality of morphisms out of `φ^*O(a) ⊗ φ^*O(b)`:
  `(δ⁻¹ ≫ φ^*(twistMul)) ≫ χ_{a+b} = (χ_a ⊗ χ_b) ≫ λ`, where `λ : O_Y ⊗ O_Y ≅ O_Y` is multiplication.
  Proof: cancel the isomorphism `δ`, transpose along `φ^* ⊣ φ_*`, and compare on pure tensors `g ⊗ h`
  (`tensorObj_hom_ext`): both sides give `θ_a(g)·θ_b(h)` (`thetaSection_mul`; `δ(η(g ⊗ h)) = η g ⊗ η h`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Proj.TwistFamily

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y : AlgebraicGeometry.Scheme.{u}} (Φ : A →+* Γ(Y, ⊤))
  (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤)

/-- `θ_n` as an additive map `Γ(U, O(n)) →+ Γ(φ⁻¹U, O_Y)`. -/
def thetaAddHom (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U) →+ Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) where
  toFun := thetaSection 𝒜 Φ hΦ n U
  map_zero' := thetaSection_zero n U
  map_add' := thetaSection_add n U

/-- **`θ_n : O(n) ⟶ φ_*O_Y`** as a morphism of `O_{Proj}`-modules: the section maps `θ_n`
(`thetaSection`), which are additive, natural (`thetaSection_res`) and `φ^♯`-linear (`thetaSection_smul`). -/
def thetaHom (n : ℕ) :
    AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj
        (𝟙_ Y.Modules) :=
  let ψ : (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf ⟶ ((AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (𝟙_ Y.Modules)).presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (thetaAddHom 𝒜 Φ hΦ n U.unop)
      naturality := by
        intro U V i
        ext g
        exact thetaSection_res n (leOfHom i.unop) g }
  SheafOfModules.Hom.mk (PresheafOfModules.homMk ψ (fun U r g => thetaSection_smul n U.unop r g))

theorem thetaHom_app (n : ℕ) (U : (AlgebraicGeometry.Proj 𝒜).Opens) (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) :
    (thetaHom 𝒜 Φ hΦ n).app U g = thetaSection 𝒜 Φ hΦ n U g := rfl

/-- **`χ_n : φ^*O(n) ⟶ O_Y`**, the adjoint transpose of `θ_n`. -/
def chi (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⟶ 𝟙_ Y.Modules :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).homEquiv _ _).symm (thetaHom 𝒜 Φ hΦ n)

/-- Evaluating the adjoint transpose on a pulled-back section: `(homEquiv k)(w) = k(η w)`. -/
theorem homEquiv_app (M : (AlgebraicGeometry.Proj 𝒜).Modules)
    (k : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj M ⟶
      𝟙_ Y.Modules) (V : (AlgebraicGeometry.Proj 𝒜).Opens) (w : Γ(M, V)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).homEquiv _ _ k).app V w :
        Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)) =
      k.app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) M V w) := by
  have h := Adjunction.homEquiv_unit (adj := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)) (f := k)
  exact congrArg (fun q : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (𝟙_ Y.Modules) =>
      q.app V w) h

/-- `χ_n(η g) = θ_n g` on `φ⁻¹V`. -/
theorem chi_app_pullbackUnitHom (n : ℕ) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), V)) :
    (chi 𝒜 Φ hΦ n).app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V g) =
      thetaSection 𝒜 Φ hΦ n V g := by
  have h := homEquiv_app 𝒜 Φ hΦ (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) (chi 𝒜 Φ hΦ n) V g
  rw [← h]
  show ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).homEquiv _ _)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).homEquiv _ _).symm (thetaHom 𝒜 Φ hΦ n))).app V g :
      Γ(Y, AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- `χ_n(η g|_B) = θ_n(g)|_B` for `B ≤ φ⁻¹V`. -/
theorem chi_app_pullbackSectionsOn (n : ℕ) (V : (AlgebraicGeometry.Proj 𝒜).Opens) (B : Y.Opens)
    (h : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), V)) :
    (chi 𝒜 Φ hΦ n).app B (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V B h g) =
      Y.presheaf.map (homOfLE h).op (thetaSection 𝒜 Φ hΦ n V g) := by
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_apply]
  refine (AlgebraicGeometry.Scheme.Modules.hom_app_res_tfa (chi 𝒜 Φ hΦ n) h _).trans ?_
  exact congrArg (fun z => Y.presheaf.map (homOfLE h).op z) (chi_app_pullbackUnitHom 𝒜 Φ hΦ n V g)

/-- **(F') at the level of `η`**: `χ_n(η(a/1)) = Φ(a)|_{φ⁻¹⊤}` for `a ∈ 𝒜 n`. -/
theorem chi_app_pullbackUnitHom_twistSection (n : ℕ) (a : A) (ha : a ∈ 𝒜 n) :
    (chi 𝒜 Φ hΦ n).app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ ⊤)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⊤ (AlgebraicGeometry.Proj.twistSection 𝒜 a ha)) =
      Y.presheaf.map (homOfLE le_top).op (Φ a) := by
  exact (chi_app_pullbackUnitHom 𝒜 Φ hΦ n ⊤ _).trans (thetaSection_twistSection n a ha)

/-- **(M') as an equality of morphisms (Stacks 01O4 (2), 01MO).** With `δ` the comparison isomorphism of the
strong monoidal pullback and `m := (tensorIsoTensorObj).inv ≫ twistMul ≫ eqToHom` (the shape of
`Proj.TwistFamily.mulHom`), `(δ⁻¹ ≫ φ^*m) ≫ χ_{a+b} = (χ_a ⊗ χ_b) ≫ λ_{O_Y}`. -/
theorem mulHom_comp_chi (a b : ℕ) :
    (CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
          AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
          CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm))) ≫
      chi 𝒜 Φ hΦ (a + b) =
    (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)) ≫
      (λ_ (𝟙_ Y.Modules)).hom := by
  apply (cancel_epi (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
    (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)))).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).homEquiv _ _).injective
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
  intro V g h
  -- both sides evaluated on `η(g ⊗ h)`
  have hL := homEquiv_app 𝒜 Φ hΦ _
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
          AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
          CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)) ≫
      chi 𝒜 Φ hΦ (a + b)) V (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h)
  have hR := homEquiv_app 𝒜 Φ hΦ _
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)) ≫
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)) ≫
      (λ_ (𝟙_ Y.Modules)).hom) V (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h)
  refine hL.trans (Eq.trans ?_ hR.symm)
  -- abbreviations
  have L1 := AlgebraicGeometry.Scheme.Modules.comp_app_apply'
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
          AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
          CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)))
    (chi 𝒜 Φ hΦ (a + b)) (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h))
  have L2 := AlgebraicGeometry.Scheme.Modules.pullbackUnitHom_map_app
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
      AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)) V
    (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h)
  have L3 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
      AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h) =
      AlgebraicGeometry.Proj.twistSectionMul 𝒜 (a : ℤ) (b : ℤ) V g h := by
    refine (AlgebraicGeometry.Scheme.Modules.comp_app_apply' _ _ _ _).trans ?_
    have e1 := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections_tfa
      (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)) V g h
    have e2 := congrArg (fun z => (AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)).app V z) e1
    refine e2.trans ?_
    refine (AlgebraicGeometry.Scheme.Modules.comp_app_apply' _ _ _ _).trans ?_
    have e3 := congrArg (fun z => (CategoryTheory.eqToHom
      (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm)).app V z)
      (AlgebraicGeometry.Proj.twistMul_app_moduleTensorSection_tfa 𝒜 (a : ℤ) (b : ℤ) V g h)
    exact e3
  have L4 := chi_app_pullbackUnitHom 𝒜 Φ hΦ (a + b) V
    (AlgebraicGeometry.Proj.twistSectionMul 𝒜 (a : ℤ) (b : ℤ) V g h)
  have L5 := thetaSection_mul (𝒜 := 𝒜) (Φ := Φ) (hΦ := hΦ) a b V g h
  have L23 := congrArg (fun z => (chi 𝒜 Φ hΦ (a + b)).app
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) z)
    (L2.trans (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.pullbackUnitHom
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) (AlgebraicGeometry.Proj.twist 𝒜 ((a + b : ℕ) : ℤ)) V z) L3))
  -- right side
  have R1 : (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)) ≫
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)) ≫
      (λ_ (𝟙_ Y.Modules)).hom).app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h)) =
      (λ_ (𝟙_ Y.Modules)).hom.app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)).app
          (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
            (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).app
            (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
            (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V
              (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h)))) := rfl
  have R2 := AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ))
    (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)) V g h
  have R3 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V g)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V h)
  have R4 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ Y.Modules)
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
    (thetaSection 𝒜 Φ hΦ a V g) (thetaSection 𝒜 Φ hΦ b V h)
  have Ca := chi_app_pullbackUnitHom 𝒜 Φ hΦ a V g
  have Cb := chi_app_pullbackUnitHom 𝒜 Φ hΦ b V h
  have R23 : (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)).app
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).app
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) _ V
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V g h))) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) (𝟙_ Y.Modules)
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V)
        (thetaSection 𝒜 Φ hΦ a V g) (thetaSection 𝒜 Φ hΦ b V h) := by
    have e := congrArg (fun z => (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules)
      (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b)).app (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) z) R2
    refine e.trans (R3.trans ?_)
    have e' := congrArg₂ (fun x y => AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) (𝟙_ Y.Modules)
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) x y) Ca Cb
    exact e'
  have R234 := (congrArg (fun z => (λ_ (𝟙_ Y.Modules)).hom.app
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) z) R23).trans R4
  exact (L1.trans (L23.trans (L4.trans L5))).trans (R1.trans R234).symm

end AlgebraicGeometry.Proj.TwistFamily

end
