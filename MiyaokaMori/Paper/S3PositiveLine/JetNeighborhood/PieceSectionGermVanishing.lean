import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient

/-! # Vanishing cone coefficient ⇒ vanishing `t`-coefficient of the coordinate function
(proof of Lemma 3.1 of the paper)

The converse direction of `BasedJet.exists_pieceSection_germ_notMem_of_not_isZeroAt`
(`JetWeightComponentEqCoefficientGeneratesAtAux.lean`): if the cone coefficient `J.coefficient ℓ m`
vanishes at `y` (`IsZeroAt`), then for every affine open `U ∋ ρ(y)` with a frame `a` of `A = f^*O(1)`,
the `m`-th `ξ`-coefficient `J.pieceSection U m _ (x_ℓ^{a^∨}|_𝒵)` of the coordinate function has germ at
`y` in `𝔪_y • ⊤`. Both directions are the same chain of three germ criteria (isomorphism, tensor with
the frame `a_M` on the left, isomorphism), read with `.mp` instead of `.mpr`; the key equality is
`BasedJet.coefficient_eq` + `BasedJet.pullbackSectionToPushforward_coneCoordinate_res` (step (4) of
`exists_pieceSection_generatesAt`). Used for `BasedJet.normalizedTupleNowhereZero_of_unit_coefficient`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-- **Vanishing cone coefficient ⇒ vanishing `ξ`-coefficient of the coordinate function**
(proof of Lemma 3.1 of the paper). Let `U ⊆ C` be an open with a frame `a` of
`A = f^*O(1)`, `y ∈ ρ⁻¹U`, `m ≤ κ`. If `J.coefficient ℓ m` vanishes at `y`, then the germ at `y` of
`J.pieceSection U m _ (x_ℓ^{a^∨}|_𝒵)` — the `m`-th `ξ`-coefficient of `J^♯` of the `ℓ`-th coordinate
function of the frame `a`, restricted to the cone — lies in `𝔪_y • ⊤`.

Proof. `BasedJet.coefficient_eq` writes `J.coefficient ℓ m = Φ'((M ◁ χ)(Q))` with `Φ'` an isomorphism,
`χ = structureIso⁻¹ ≫ π_m ≫ pieceIso ≫ monoidalPowIsoTensorPower` and
`Q = pullbackSectionToPushforward p M (coneCoordinate J ℓ)`. Isomorphisms preserve "germ in `𝔪_y • ⊤`"
(`germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`); on `ρ⁻¹U`, `Q = a_M ⊗ (J ≫ coneι)^♯(x_ℓ^{a^∨})`
(`pullbackSectionToPushforward_coneCoordinate_res`) with `a_M = η_ρ(θ' a)` a frame
(`isFrame_unit_unit_map`), and tensoring with a frame on the left preserves the criterion
(`germ_whiskerLeft_app_mem_maximalIdeal_smul_iff_of_res_eq_tensorSections`); a last isomorphism
(`monoidalPowIsoTensorPower`) and `appLE_comp_appLE` give the statement. This is
`exists_pieceSection_germ_notMem_of_not_isZeroAt` with every `iff` read in the other direction. -/
theorem BasedJet.pieceSection_germ_mem_of_isZeroAt (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (ℓ : Fin (X.embDim + 1)) (m : ℕ) (hm : m ≤ κ) (U : C.toScheme.Opens) (hyU : y ∈ ρ.hom ⁻¹ᵁ U)
    {a : Γ(seedLineBundle X.embedding f, U)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U a)
    (hleb : (MMSetup.cone f).hom ⁻¹ᵁ U ≤ BasedJet.coneι f ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U))
    (h : IsZeroAt (J.coefficient ℓ m) y) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
        (ρ.hom ⁻¹ᵁ U) y hyU
        (J.pieceSection U m hm (AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn (seedLineBundle X.embedding f)
          (X.embDim + 1) ℓ U hf.dualSec (BasedJet.coneι f) ((MMSetup.cone f).hom ⁻¹ᵁ U) hleb)) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y)) := by
  rw [J.coefficient_eq ℓ m hm] at h
  have h1 := (AlgebraicGeometry.Scheme.Modules.germ_hom_app_mem_maximalIdeal_smul_iff_of_iso
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)).symm ≪≫
      (L.coefficientModuleIso
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) m)) ⊤ trivial
    ((CategoryTheory.MonoidalCategoryStruct.whiskerLeft
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
          CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨m, Nat.lt_succ_of_le hm⟩ ≫
          (truncatedJetAlgebra.pieceIso L m).hom ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).hom)).app ⊤
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (J.coneCoordinate ℓ)))).mp h
  have h2 := (AlgebraicGeometry.Scheme.Modules.germ_whiskerLeft_app_mem_maximalIdeal_smul_iff_of_res_eq_tensorSections
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩ ≫
      (truncatedJetAlgebra.pieceIso L m).hom ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).hom)
    _ hyU (BasedJet.isFrame_unit_unit_map U hf) _ (J.pullbackSectionToPushforward_coneCoordinate_res ℓ U hf)).mp h1
  have h3 := (AlgebraicGeometry.Scheme.Modules.germ_hom_app_mem_maximalIdeal_smul_iff_of_iso
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m) (ρ.hom ⁻¹ᵁ U) hyU
    (((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩ ≫
      (truncatedJetAlgebra.pieceIso L m).hom).app (ρ.hom ⁻¹ᵁ U)
      (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf), ρ.hom ⁻¹ᵁ U) from
        (J.hom ≫ BasedJet.coneι f).appLE
          ((AlgebraicGeometry.Scheme.totalSpace
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
          (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
          (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
            (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
          (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
            hf.dualSec)))).mp h2
  have hc : (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) (by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
          J.over])).hom
      (AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn (seedLineBundle X.embedding f)
        (X.embDim + 1) ℓ U hf.dualSec (BasedJet.coneι f) ((MMSetup.cone f).hom ⁻¹ᵁ U) hleb) =
      (J.hom ≫ BasedJet.coneι f).appLE
        ((AlgebraicGeometry.Scheme.totalSpace
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
        (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
        (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
          (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
        (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
          hf.dualSec) :=
    ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE J.hom (BasedJet.coneι f)
      ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
      ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) hleb
      (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage, J.over]))
      (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
        hf.dualSec)
  show (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
    (ρ.hom ⁻¹ᵁ U) y hyU
    ((((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le hm⟩ ≫
        (truncatedJetAlgebra.pieceIso L m).hom).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U))).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj
            (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) from
        (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) (by
          rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
            J.over])).hom
          (AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn (seedLineBundle X.embedding f)
            (X.embDim + 1) ℓ U hf.dualSec (BasedJet.coneι f) ((MMSetup.cone f).hom ⁻¹ᵁ U) hleb))) ∈ _
  rw [hc]
  exact h3

end
