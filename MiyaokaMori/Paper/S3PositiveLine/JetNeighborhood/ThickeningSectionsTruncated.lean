import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowNegIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningCoefficientNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.ThickeningSectionsTruncatedAux
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # Sections on the thickening are truncated sections on the total space

Global sections of `p_L^*M` on `C̃_(κ)(L)` are `⊕_{q≤κ} H^0(C̃, M ⊗ L^{-q})`, and restriction from `Tot(L)` is just
truncation (the coefficients with `q ≤ κ` are unchanged); §3 of the paper and equation (4.1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- **Global sections on the thickening decompose by ξ-degree**:
`Γ(C̃_(κ)(L), p_κ^*M) ≃ₗ[k] ⊕_{q ≤ κ} H^0(C̃, M ⊗ L^{-q})`.

Source: §3 of the paper (`C̃_(k)(L) = Spec_{C̃}(⊕_{q=0}^k L^{-q})`, locally `O(V)[t]/(t^{k+1})`) and
Lemma 4.1 ((4.1): `P_ℓ^{(k)} = ρ^*f_ℓ + Σ_{q=1}^k c_{ℓ,q} ξ^q`,
`c_{ℓ,q} ∈ H^0(C̃, ρ^*A ⊗ L^{-q})`).
Stacks 01E8 (projection formula), 01LQ (`p_*O_{Spec_X A} = A`).

**Usage**: no Lean declaration uses this theorem (it is only mentioned in comments of
`ConeCoordinateFiniteXiExpansion*.lean`); the coefficient-level statement actually used downstream is
`xiCoefficient_restrictToThickening` below.

---
## Natural-language proof (complete)

Write `A = truncatedJetAlgebra L κ` (so `p_κ : C̃_(κ)(L) = Spec_{C̃} A → C̃`), `σ_κ = structureHom A`
(an isomorphism `A.carrier ≅ (p_κ)_*O`, `structureIso`), `N_q := (M.zpow 1) ⊗ L^{-q}`.

1. **Projection formula.** `pullbackSectionToPushforward p_κ M : Γ(C̃_(κ), p_κ^*M) → Γ(C̃, M ⊗ (p_κ)_*O)` is
   `θ⁻¹ ∘ ρ⁻¹` on global sections with `θ = projectionFormulaIso p_κ M O` and `ρ` the right unitor; both are
   isomorphisms of sheaves of modules, so this map is an additive bijection (inverse:
   `pushforwardSectionToPullback`).
2. **Structure sheaf.** `M ◁ σ_κ⁻¹ : M ⊗ (p_κ)_*O ≅ M ⊗ A.carrier` is an isomorphism; take global sections.
3. **Tensor distributes over the finite biproduct.** `A.carrier = ⨁_{q : Fin (κ+1)} piece_q` and
   `M ⊗ ⨁_q piece_q ≅ ⨁_q (M ⊗ piece_q)`; this needs that `M ⊗ -` is an additive functor on `X.Modules`
   (`MonoidalPreadditive`: `M ◁ (f + g) = M ◁ f + M ◁ g`), which follows from bilinearity of the presheaf
   tensor product and additivity of sheafification; then `Functor.mapBiproduct`.
4. **Global sections of a finite biproduct.** For `N : Fin (κ+1) → X.Modules`,
   `Γ(⊤, ⨁ N) ≃ ∏_q Γ(⊤, N q)`, `x ↦ (π_q x)_q`, inverse `(c_q) ↦ Σ_q ι_q c_q`: this is
   `AlgebraicGeometry.Scheme.Modules.biproduct_section_eq_sum` (`JetWeightComponentEqCoefficient.lean`)
   together with `biproduct.ι_π` on sections.
5. **Identify the pieces.** `M ⊗ piece_q ≅ M ⊗ (L^∨)^{⊗q} ≅ coefficientLineModule M L q ≅ N_q` via
   `pieceIso`, `monoidalPowIsoTensorPower`, `tensorIsoTensorObj.inv`, `coefficientModuleIso` — all isomorphisms,
   take global sections.
6. **Finite product = direct sum.** `∏_{q : Fin (κ+1)} ≃ₗ ⊕_q` is `DirectSum.linearEquivFunOnFintype`
   (`directSum_of_fintype_linearEquiv`, `FiniteBiproductSectionsDirectSum.lean`).
7. **k-linearity.** Every map in 2–5 is `Γ(C̃, O)`-linear on global sections (`Hom.app_smul`), hence
   `k`-linear for `globalSectionsModuleOver (C̃ → Spec k)` (scalars restricted along `k → Γ(C̃, O)`). For step 1
   the source carries `globalSectionsModuleOver (p_κ ≫ (C̃ → Spec k))`, i.e. `k → Γ(C̃, O) → Γ(C̃_(κ), O)`
   (`Scheme.Hom.comp_appTop`), and `Γ(C̃, (p_κ)_*N) = Γ(C̃_(κ), N)` with the `Γ(C̃,O)`-action through
   `p_κ^♯` (the module structure of `pushforward` is restriction of scalars along `p_κ.toRingCatSheafHom`);
   so `pullbackSectionToPushforward` is `k`-linear. ∎

## Formalization (auxiliary module `ThickeningSectionsTruncatedAux`)
The abstract situation "`p : T → X`, `M` a line bundle, `σ : ⨁_q N_q ≅ p_*O_T`, `g_q : M ⊗ N_q ≅ W_q`" is
handled once by `Modules.affineSectionsLinearEquiv p M N σ W g s : Γ(T, p^*M) ≃ₗ[k] ∏_q Γ(X, W_q)`
(forward map `affineSectionsCoeff` = steps 1–5, inverse `affineSectionsAssemble`; steps 3–4 are
`app_top_whiskerLeft_biproduct_eq_sum` via `Modules.tensorLeft_additive` + `biproduct.total`; step 7 is
`pullbackSectionToPushforward_smul`, semilinearity along `p^♯`, which is definitional for the pushforward
module structure). Here `N_q = truncatedJetAlgebra.piece L q`, `σ = relativeSpec.structureIso`,
`g_q = whiskerLeftIso M (pieceIso ≪≫ monoidalPowIsoTensorPower) ≪≫ tensorIsoTensorObj⁻¹ ≪≫ coefficientModuleIso`;
step 6 is `DirectSum.linearEquivFunOnFintype`. -/
theorem jetNeighborhood_globalSections_decomp {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ) :
    letI := AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver
      (jetNeighborhood.proj L κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj M.toModules)
    letI := fun q : Fin (κ + 1) => AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules
    Nonempty
      ((((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
          M.toModules).val.obj (Opposite.op ⊤) : Type u)
        ≃ₗ[k] DirectSum (Fin (κ + 1)) (fun q : Fin (κ + 1) =>
          ((((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules.val.obj
            (Opposite.op ⊤)) : Type u))) := by
  let _ := AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver
      (jetNeighborhood.proj L κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj M.toModules)
  let _ := fun q : Fin (κ + 1) => AlgebraicGeometry.Scheme.Modules.globalSectionsModuleOver
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules
  -- `p_*O ≅ ⨁_{q ≤ κ} piece_q` (Stacks 01LQ) and `M ⊗ piece_q ≅ M ⊗ (L^∨)^{⊗q} ≅ N_q`.
  let σ : CategoryTheory.Limits.biproduct (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
        (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)
  let g : ∀ q : Fin (κ + 1), M.toModules ⊗ truncatedJetAlgebra.piece L q ≅
      ((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules := fun q =>
    CategoryTheory.MonoidalCategory.whiskerLeftIso M.toModules
        (truncatedJetAlgebra.pieceIso L q ≪≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).symm ≪≫
      L.coefficientModuleIso M q
  have e : ((((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
          M.toModules).val.obj (Opposite.op ⊤) : Type u)
        ≃ₗ[k] ∀ q : Fin (κ + 1),
          ((((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules.val.obj
            (Opposite.op ⊤)) : Type u)) :=
    AlgebraicGeometry.Scheme.Modules.affineSectionsLinearEquiv (jetNeighborhood.proj L κ) M.toModules
      (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) σ
      (fun q : Fin (κ + 1) => ((M.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules) g
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  exact ⟨e.trans (DirectSum.linearEquivFunOnFintype k (Fin (κ + 1)) _).symm⟩

/-- Restriction to the thickening: pull a section back along the closed immersion `i : C̃_(κ)(L) ↪ Tot(L)`
(`jetNeighborhood.toTotalSpace`), then apply `i^*p^*M ≅ (i ≫ p)^*M = p_κ^*M` (`pullbackComp` and `i ≫ p = p_κ`).
Written as an instance of `restrictSectionAlong` (`ThickeningCoefficientNaturality`), so that the instance
`pullbackSectionToPushforward_comp'` of the naturality lemma agrees with this definition literally (one delta step). -/

noncomputable def restrictToThickening {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.Modules.restrictSectionAlong (jetNeighborhood.toTotalSpace L κ).left
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (g' := jetNeighborhood.proj L κ) M.toModules
    (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
      (jetNeighborhood.toTotalSpace_proj L κ)) P

/-- The `q`-th coefficient on the thickening: `Γ(C̃_(κ), p_κ^*M) → Γ(C̃, M ⊗ (p_κ)_*O)` (inverse projection formula)
`→ M ⊗ ⊕_{q ≤ κ} (L^{-1})^{⊗q}` (inverse of `relativeSpec.structureIso`) `→` the `q`-th piece `→ M ⊗ (L^∨)^{⊗q}`, then
`coefficientModuleIso`; `0` for `q > κ`. -/

noncomputable def xiCoefficientThickening {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ q : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u) :=
  if h : q ≤ κ then
    (((CategoryTheory.MonoidalCategoryStruct.whiskerLeft M.toModules
          ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
            CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨q, Nat.lt_succ_of_le h⟩ ≫
            (truncatedJetAlgebra.pieceIso L q).hom ≫
            (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)).inv ≫
        (L.coefficientModuleIso M q).hom).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ) M.toModules P))
  else 0

theorem xiCoefficient_restrictToThickening {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ q : ℕ)
    (hq : q ≤ κ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiCoefficientThickening L M κ q (restrictToThickening L M κ P)
      = xiCoefficient L M P q := by
  -- Leaf B (algebra-map form, `ThickeningCoefficientNaturality`) and Leaf B' with free target
  -- `totalSpace L.toModules`: `σ ≫ ψ = truncation ≫ σ_κ` for the `ψ` attached to `toTotalSpace L κ`.
  have h2 := jetNeighborhood.toAlgebraMap_toTotalSpace L κ
  have h3 := AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap_eq' (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
    (jetNeighborhood L κ) (AlgebraicGeometry.Scheme.totalSpace L.toModules) rfl
    (jetNeighborhood.toTotalSpace L κ)
  erw [CategoryTheory.eqToHom_refl, Category.id_comp] at h3
  rw [h3] at h2
  -- Name that `ψ` once. (Its spelling produced by the universal property and the one produced by Leaf A
  -- below are definitionally equal but differ in implicit arguments; comparing them definitionally
  -- inside composites does not terminate in practice, so from here on only the variable `ψ` occurs.)
  obtain ⟨ψ, hB, hψeq⟩ : ∃ ψ : (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ⟶
        (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf),
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total ≫ ψ =
        truncatedJetAlgebra.truncation L κ ≫
          AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ) ∧ ψ = _ :=
    ⟨_, h2, rfl⟩
  -- Leaf A (`pullbackSectionToPushforward_comp`) at the data of `restrictToThickening`
  -- (which is `restrictSectionAlong` of the same arguments, so folding is a one-step unfolding).
  have hA : AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
        M.toModules (restrictToThickening L M κ P) = _ :=
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_comp'
      (jetNeighborhood.toTotalSpace L κ).left (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
      (jetNeighborhood.toTotalSpace_proj L κ) M.toModules
      (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
        (jetNeighborhood.toTotalSpace_proj L κ)) P
  unfold xiCoefficientThickening
  rw [dif_pos hq, hA]
  erw [← hψeq]
  -- Leaves B, C assembled at section level (`thickeningCoefficient_apply_of`).
  unfold xiCoefficient AlgebraicGeometry.Scheme.totalSpace.coefficient
  exact jetNeighborhood.thickeningCoefficient_apply_of L M κ q hq ψ hB P

end
