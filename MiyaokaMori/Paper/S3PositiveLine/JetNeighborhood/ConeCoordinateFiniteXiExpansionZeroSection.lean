import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionProjectionFormulaPullback
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection

/-! # The zeroth `ξ`-coefficient on the thickening is the restriction to the zero section

The restriction `jetNeighborhood.restrictToZeroSection` of a section on the thickening `C̃_(κ)(L)` along the zero
section `σ₀ : C̃ → C̃_(κ)(L)` (`σ₀^*p_κ^*M ≅ (σ₀ ≫ p_κ)^*M = (𝟙)^*M ≅ M`, the same construction as
`Scheme.restrictToZeroSection`), and the fact that the `0`-th `ξ`-coefficient of a section is its restriction along
the zero section (through `coefficientZeroIso`). This is the analogue on the thickening of
`xiCoefficient_zero_eq_zeroSection` (the version on `Tot(L)`, `TotSectionsPolynomial.lean`).

Source: §3 of the paper and Lemma 4.1 ("`ȷ` restricts to `s ∘ ρ` on the zero section"
gives the constant term of the expansion).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- Restriction of a global section of `p_κ^*M` on the thickening along the zero section
`σ₀ = jetNeighborhood.zeroSection L κ` back to `C̃`:
`σ₀^*(p_κ^*M) ≅ (σ₀ ≫ p_κ)^*M` (`pullbackComp`) `= (𝟙)^*M` (`pullbackCongr (zeroSection_proj)`) `≅ M` (`pullbackId`),
applied to `sectionPullbackAlong σ₀ P`. Literally the same construction as
`AlgebraicGeometry.Scheme.restrictToZeroSection`. -/
noncomputable def jetNeighborhood.restrictToZeroSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    (M.toModules.val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp (jetNeighborhood.zeroSection L κ)
        (jetNeighborhood.proj L κ)).app M.toModules ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (jetNeighborhood.zeroSection_proj L κ)).app M.toModules ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId C.toScheme).app M.toModules).hom.app ⊤
    (sectionPullbackAlong (jetNeighborhood.zeroSection L κ) P)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 01LQ, "morphism ↦ algebra map" for an `X`-point given by `σ` with `σ ≫ p = g`**:
`toAlgebraMap A (Over.mk g) (homMk σ) = structureHom A ≫ p_*(σ^♯) ≫ pushforwardComp ≫ pushforwardCongr`
(`toAlgebraMap_precomp` with `T = Spec_X A`, `m = 𝟙`; `toAlgebraMap A _ 𝟙 = structureHom A` by definition). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_homMk_eq {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) {S : AlgebraicGeometry.Scheme.{u}}
    (σ : S ⟶ (AlgebraicGeometry.Scheme.relativeSpec A).left) {g : S ⟶ X}
    (hg : σ ≫ (AlgebraicGeometry.Scheme.relativeSpec A).hom = g) :
    AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A (CategoryTheory.Over.mk g)
        (CategoryTheory.Over.homMk σ hg) =
      AlgebraicGeometry.Scheme.relativeSpec.structureHom A ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeSpec A).hom).map
          (SheafOfModules.unitToPushforwardObjUnit σ.toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp σ (AlgebraicGeometry.Scheme.relativeSpec A).hom).hom.app
          (𝟙_ S.Modules) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr hg).hom.app (𝟙_ S.Modules) := by
  subst hg
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardCongr_rfl_hom_app_unit, Category.comp_id]
  have h := AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_precomp A
    (AlgebraicGeometry.Scheme.relativeSpec A) σ (𝟙 _)
  rw [Category.comp_id] at h
  exact h

/-- The algebra map of the zero section is the augmentation (`right_inv` of `relativeSpecHomEquiv`). -/
theorem jetNeighborhood.toAlgebraMap_zeroSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (κ : ℕ) :
    AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap (truncatedJetAlgebra L κ)
        (CategoryTheory.Over.mk (𝟙 C.toScheme))
        (CategoryTheory.Over.homMk (jetNeighborhood.zeroSection L κ) (jetNeighborhood.zeroSection_proj L κ)) =
      jetNeighborhood.augmentation L κ := by
  have h : (CategoryTheory.Over.homMk (jetNeighborhood.zeroSection L κ) (jetNeighborhood.zeroSection_proj L κ) :
        CategoryTheory.Over.mk (𝟙 C.toScheme) ⟶ AlgebraicGeometry.Scheme.relativeSpec (truncatedJetAlgebra L κ)) =
      (AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
        (CategoryTheory.Over.mk (𝟙 C.toScheme))).symm
        ⟨jetNeighborhood.augmentation L κ, jetNeighborhood.augmentation_isAlgebraMap L κ⟩ :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [h]
  exact congrArg Subtype.val ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
    (CategoryTheory.Over.mk (𝟙 C.toScheme))).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
/-- `σ_A⁻¹ ≫ π₀ = p_*(σ^♯) ≫ C` : the degree-0 projection of the truncated jet algebra, read through
`structureIso`, is "restrict functions along the zero section" (`C` the pseudofunctor identification
`p_*σ_*O ≅ O`). -/
theorem jetNeighborhood.structureIso_inv_comp_π_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (κ : ℕ) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩ =
      (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).map
          (SheafOfModules.unitToPushforwardObjUnit (jetNeighborhood.zeroSection L κ).toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCompCongrIdIso (jetNeighborhood.zeroSection L κ)
          (jetNeighborhood.proj L κ) (jetNeighborhood.zeroSection_proj L κ) (𝟙_ C.toScheme.Modules)).hom := by
  have hε : jetNeighborhood.augmentation L κ =
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩ ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId C.toScheme).inv.app (𝟙_ C.toScheme.Modules) := rfl
  have h := jetNeighborhood.toAlgebraMap_zeroSection L κ
  rw [AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_homMk_eq (truncatedJetAlgebra L κ)
    (jetNeighborhood.zeroSection L κ) (jetNeighborhood.zeroSection_proj L κ), hε] at h
  have h' : AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).map
        (SheafOfModules.unitToPushforwardObjUnit (jetNeighborhood.zeroSection L κ).toRingCatSheafHom) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (jetNeighborhood.zeroSection L κ)
        (jetNeighborhood.proj L κ)).hom.app (𝟙_ C.toScheme.Modules) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (jetNeighborhood.zeroSection_proj L κ)).hom.app
        (𝟙_ C.toScheme.Modules) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardId C.toScheme).hom.app (𝟙_ C.toScheme.Modules) =
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩ := by
    have := congrArg (fun φ => φ ≫ (AlgebraicGeometry.Scheme.Modules.pushforwardId C.toScheme).hom.app
      (𝟙_ C.toScheme.Modules)) h
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj] at this
    exact this.trans (Category.comp_id _)
  show (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩ =
    (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).map
        (SheafOfModules.unitToPushforwardObjUnit (jetNeighborhood.zeroSection L κ).toRingCatSheafHom) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp (jetNeighborhood.zeroSection L κ)
        (jetNeighborhood.proj L κ)).hom.app (𝟙_ C.toScheme.Modules) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (jetNeighborhood.zeroSection_proj L κ)).hom.app
        (𝟙_ C.toScheme.Modules) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardId C.toScheme).hom.app (𝟙_ C.toScheme.Modules)
  rw [← h', ← Category.assoc]
  have hσ : (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ) = 𝟙 _ :=
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv_hom_id
  rw [hσ, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Unfolding `xiCoefficientThickening` at `q = 0` through `coefficientZeroIso`:
`coefficientZeroIso.hom (ξ-coefficient₀ P) = ρ((M ◁ (σ_A⁻¹ ≫ π₀)) (pull P))`
(`pieceIso L 0`, `monoidalPowIsoTensorPower _ 0`, `zpowNegIso 0` are `Iso.refl` by definition, and
`coefficientModuleIso ≫ coefficientZeroIso` cancels to the right unitor). -/
theorem coefficientZeroIso_hom_xiCoefficientThickening_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom (xiCoefficientThickening L M κ 0 P) =
      ((ρ_ M.toModules).hom.val.app (Opposite.op ⊤)).hom
        (((M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
            CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨0, Nat.succ_pos κ⟩)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ) M.toModules P)) := by
  have hmor : ((M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.lt_succ_of_le (Nat.zero_le κ)⟩ ≫
        (truncatedJetAlgebra.pieceIso L 0).hom ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0).hom)) ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0)).inv ≫
      (L.coefficientModuleIso M 0).hom) ≫ (coefficientZeroIso L M).hom =
      (M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩)) ≫ (ρ_ M.toModules).hom := by
    show ((M.toModules ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩ ≫ (Iso.refl _).hom ≫ (Iso.refl _).hom)) ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules 0)).inv ≫
      (L.coefficientModuleIso M 0).hom) ≫ (coefficientZeroIso L M).hom = _
    unfold LineBundle.coefficientModuleIso coefficientZeroIso
    simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, MonoidalCategory.tensorIso_hom]
    show (M.toModules ◁ _) ≫ (M.zpowOneIso.inv ⊗ₘ 𝟙 (L.zpow (-((0 : ℕ) : ℤ))).toModules) ≫
      (M.zpowOneIso.hom ⊗ₘ 𝟙 (L.zpow (-((0 : ℕ) : ℤ))).toModules) ≫ (ρ_ M.toModules).hom = _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id]
    slice_lhs 2 3 => rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight]
    rw [Category.id_comp]
  unfold xiCoefficientThickening
  rw [dif_pos (Nat.zero_le κ)]
  exact congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ) M.toModules P)) hmor

/-- **The `0`-th `ξ`-coefficient is the restriction along the zero section**:
`xiCoefficientThickening L M κ 0 P = coefficientZeroIso⁻¹ (restrictToZeroSection P)`.

Source: §3 of the paper and Lemma 4.1. The same fact on `Tot(L)` is
`xiCoefficient_zero_eq_zeroSection` (`TotSectionsPolynomial.lean`, provable by the same route).

## Proof (notation)
`p := jetNeighborhood.proj L κ`, `A := truncatedJetAlgebra L κ`, `σ_A := relativeSpec.structureIso A`,
`σ₀ := jetNeighborhood.zeroSection L κ` (`σ₀ ≫ p = 𝟙`), `ε := augmentation L κ = π₀ ≫ pushforwardId.inv`,
`Q := pullbackSectionToPushforward p M P`, `C := pushforwardCompCongrIdIso σ₀ p _ 𝟙` (`p_*σ₀_*O ≅ O`),
`Φ := pullbackComp ≫ pullbackCongr ≫ pullbackId` (`σ₀^*p^*M ≅ M`; `restrictToZeroSection P = Φ(σ₀^*P)` by definition).
1. Unfold (`coefficientZeroIso_hom_xiCoefficientThickening_zero`): `pieceIso L 0`, `monoidalPowIsoTensorPower _ 0`
   and `zpowNegIso 0` are `Iso.refl`, and `coefficientModuleIso L M 0 ≫ coefficientZeroIso` cancels to the right
   unitor, so `coefficientZeroIso.hom (xiCoefficientThickening L M κ 0 P) = ρ((M ◁ (σ_A⁻¹ ≫ π₀)) Q)`.
2. `σ_A⁻¹ ≫ π₀ = p_*(σ₀^♯) ≫ C.hom` (`jetNeighborhood.structureIso_inv_comp_π_zero`): the algebra map of the zero
   section is `ε` (`right_inv` of `relativeSpecHomEquiv`, `toAlgebraMap_zeroSection`), while
   `toAlgebraMap (homMk σ₀) = structureHom ≫ p_*(σ₀^♯) ≫ pushforwardComp ≫ pushforwardCongr`
   (`toAlgebraMap_precomp`, `toAlgebraMap_homMk_eq`); compose with `pushforwardId.hom` and use
   `σ_A⁻¹ ≫ structureHom = 𝟙`.
3. The general lemma `rightUnitor_whiskerLeft_eq_pullback_section_of_comp_eq_id`
   (`ConeCoordinateFiniteXiExpansionProjectionFormulaPullback`, variable level, for any section `j` of `p`):
   `ρ((M ◁ (p_*(j^♯) ≫ C.hom)) Q) = Φ(j^*(pushforwardSectionToPullback p M Q))`, and
   `pushforwardSectionToPullback p M Q = P` (`pushforwardSectionToPullback_pullbackSectionToPushforward`).
4. Hence `coefficientZeroIso.hom (LHS) = restrictToZeroSection P`; conclude since `coefficientZeroIso` is an
   isomorphism.

Edge cases: for `κ = 0`, `A = piece_0 = O` and `σ₀` is an isomorphism; the proof is unchanged. For `P = 0` both
sides are `0`. -/
theorem xiCoefficientThickening_zero_eq_restrictToZeroSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficientThickening L M κ 0 P
      = ((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom
          (jetNeighborhood.restrictToZeroSection L M κ P) := by
  -- apply the iso `coefficientZeroIso` to both sides
  have hU := coefficientZeroIso_hom_xiCoefficientThickening_zero L M κ P
  rw [jetNeighborhood.structureIso_inv_comp_π_zero L κ] at hU
  have hK := AlgebraicGeometry.Scheme.Modules.rightUnitor_whiskerLeft_eq_pullback_section_of_comp_eq_id
    (jetNeighborhood.zeroSection L κ) (jetNeighborhood.proj L κ) (jetNeighborhood.zeroSection_proj L κ)
    M.toModules
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ) M.toModules P)
  rw [AlgebraicGeometry.Scheme.Modules.pushforwardSectionToPullback_pullbackSectionToPushforward] at hK
  calc xiCoefficientThickening L M κ 0 P
      = ((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom
          (((coefficientZeroIso L M).hom.val.app (Opposite.op ⊤)).hom (xiCoefficientThickening L M κ 0 P)) :=
        (AlgebraicGeometry.Scheme.Modules.app_top_hom_inv _ _).symm
    _ = _ := congrArg (fun z => ((coefficientZeroIso L M).inv.val.app (Opposite.op ⊤)).hom z) (hU.trans hK)

end
