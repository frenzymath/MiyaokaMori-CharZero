import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.Paper.S2WeightedJets.Cone.TotLineAffineOverBase

/-! # The `ξ`-expansion of `J^♯ c` on a neighbourhood: ring homomorphism, unit clause, germ criterion
(used for `BasedJet.pieceSection_germ_mem_of_forall_isZeroAt`; proof of Lemma 3.1 of the paper)

For a based jet `J : C̃_(κ)(L) → 𝒵` over `ρ`, an open `U ⊆ C` and an open `W ≤ ρ⁻¹U` of `C̃`, the map
`c ↦ structureIso⁻¹(J^♯ c) ∈ 𝒜(W) = (truncatedJetAlgebra L κ).sectionsRing W` (`BasedJet.xiExpansion`) is a ring
homomorphism `Γ(𝒵, π⁻¹U) → 𝒜(W)` (`BasedJet.xiExpansionHom`; `structureIso_inv_app_mul`, `structureIso_inv_app_one`)
sending `π^♯ r` to `sectionsUnit (ρ^♯ r|_W)` (`BasedJet.xiExpansion_cone_app`; `J.over` and
`relativeSpec.structureHom_app_sectionsUnit`). The `n`-th `ξ`-coefficient `J.pieceSection U n _ c` (defined on `ρ⁻¹U`)
has germ at `y ∈ W` in `𝔪_y • ⊤` iff the `n`-th piece of the `ξ`-expansion on `W` does
(`BasedJet.germ_pieceSection_mem_iff`; `germ_res_mem_maximalIdeal_smul_iff`, naturality, and the isomorphism
`pieceIso_n`, `germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-- `p⁻¹W ≤ J⁻¹π⁻¹U` when `W ≤ ρ⁻¹U` (`J ≫ π = p ≫ ρ`). -/
theorem BasedJet.proj_preimage_le (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) :
    jetNeighborhood.proj L κ ⁻¹ᵁ W ≤ J.hom ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ U) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, J.over, AlgebraicGeometry.Scheme.Hom.comp_preimage]
  exact fun z hz => hW hz

/-- The `ξ`-expansion of `J^♯ c` on `W ≤ ρ⁻¹U`: `structureIso⁻¹ (J^♯ c) ∈ 𝒜(W)`. -/
def BasedJet.xiExpansion (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U)) :
    (truncatedJetAlgebra L κ).sectionsRing W :=
  ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv.val.app (Opposite.op W)).hom
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
        (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj (Opposite.op W) : Type u) from
      (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ W) (J.proj_preimage_le U hW)).hom c)

/-- The `ξ`-expansion is a ring homomorphism (`J^♯` is a ring homomorphism; `structureIso⁻¹` preserves `1` and
products, `structureIso_inv_app_one`, `structureIso_inv_app_mul`). -/
def BasedJet.xiExpansionHom (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) :
    Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U) →+* (truncatedJetAlgebra L κ).sectionsRing W where
  toFun := J.xiExpansion U hW
  map_zero' := by
    unfold BasedJet.xiExpansion
    rw [map_zero]
    exact map_zero _
  map_add' a b := by
    unfold BasedJet.xiExpansion
    rw [map_add]
    exact map_add _ _ _
  map_one' := by
    unfold BasedJet.xiExpansion
    rw [map_one]
    exact AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_one (truncatedJetAlgebra L κ) W
  map_mul' a b := by
    unfold BasedJet.xiExpansion
    rw [map_mul]
    exact AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_mul (truncatedJetAlgebra L κ) W _ _

theorem BasedJet.xiExpansionHom_apply (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U)) :
    J.xiExpansionHom U hW c = J.xiExpansion U hW c := rfl

/-- **Unit clause**: the `ξ`-expansion of `π^♯ r` is the constant `sectionsUnit W (ρ^♯ r|_W)`
(`J ≫ π = p ≫ ρ`, `appLE_comp_appLE`, and `structureHom (sectionsUnit s) = p^♯ s`,
`relativeSpec.structureHom_app_sectionsUnit`). -/
theorem BasedJet.xiExpansion_cone_app (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) (r : Γ(C.toScheme, U)) :
    J.xiExpansion U hW ((MMSetup.cone f).hom.app U r) =
      (truncatedJetAlgebra L κ).sectionsUnit W ((ρ.hom.appLE U W hW).hom r) := by
  -- J^♯ (π^♯ r) = p^♯ (ρ^♯ r)
  have h1 : (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ W)
      (J.proj_preimage_le U hW)).hom ((MMSetup.cone f).hom.app U r) =
      ((jetNeighborhood.proj L κ).app W).hom ((ρ.hom.appLE U W hW).hom r) := by
    have e1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE J.hom (MMSetup.cone f).hom U
      ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ W) le_rfl (J.proj_preimage_le U hW)
    have e2 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetNeighborhood.proj L κ) ρ.hom U W
      (jetNeighborhood.proj L κ ⁻¹ᵁ W) hW le_rfl
    have e3 : (J.hom ≫ (MMSetup.cone f).hom).appLE U (jetNeighborhood.proj L κ ⁻¹ᵁ W)
        ((J.proj_preimage_le U hW).trans ((Opens.map J.hom.base).map (homOfLE le_rfl)).le) =
        (jetNeighborhood.proj L κ ≫ ρ.hom).appLE U (jetNeighborhood.proj L κ ⁻¹ᵁ W)
        (le_rfl.trans ((Opens.map (jetNeighborhood.proj L κ).base).map (homOfLE hW)).le) :=
      AlgebraicGeometry.Scheme.Hom.appLE_congr_hom J.over _ _ _ _
    have e4 := congrArg (fun φ : Γ(C.toScheme, U) ⟶ Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ W) =>
      φ.hom r) (e1.trans (e3.trans e2.symm))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e4
    rw [AlgebraicGeometry.Scheme.Hom.app_eq_appLE, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    exact e4
  unfold BasedJet.xiExpansion
  have h2 := AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_sectionsUnit (truncatedJetAlgebra L κ) W
    ((ρ.hom.appLE U W hW).hom r)
  have h3 : ∀ x, ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv.val.app
      (Opposite.op W)).hom (((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).val.app
        (Opposite.op W)).hom x) = x := fun x =>
    congrArg (fun g : (truncatedJetAlgebra L κ).carrier ⟶ (truncatedJetAlgebra L κ).carrier => (g.val.app (Opposite.op W)).hom x)
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).hom_inv_id
  rw [← h3 ((truncatedJetAlgebra L κ).sectionsUnit W ((ρ.hom.appLE U W hW).hom r))]
  congr 1
  rw [h1]
  exact h2.symm

/-- **Restriction of the `n`-th `ξ`-coefficient**: `(J.pieceSection U n _ c)|_W = pieceIso_n (π_n (xiExpansion c))`
(naturality of `structureIso⁻¹ ≫ π_n ≫ pieceIso_n` and `appLE_map` for `J^♯`). -/
theorem BasedJet.res_pieceSection (J : BasedJet f ρ L κ) (U : C.toScheme.Opens) {W : ρ.source.toScheme.Opens}
    (hW : W ≤ ρ.hom ⁻¹ᵁ U) (n : ℕ) (hn : n ≤ κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U)) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).res hW
        (J.pieceSection U n hn c) =
      ((truncatedJetAlgebra.pieceIso L n).hom.val.app (Opposite.op W)).hom
        (((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨n, Nat.lt_succ_of_le hn⟩).val.app (Opposite.op W)).hom (J.xiExpansion U hW c)) := by
  unfold BasedJet.pieceSection BasedJet.xiExpansion
  have hnat := PresheafOfModules.naturality_apply
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨n, Nat.lt_succ_of_le hn⟩ ≫
      (truncatedJetAlgebra.pieceIso L n).hom).val (CategoryTheory.homOfLE hW).op
    (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
        (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj
          (Opposite.op (ρ.hom ⁻¹ᵁ U)) : Type u) from
      (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) (by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
          J.over])).hom c)
  refine hnat.symm.trans ?_
  have hres := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U) ⟶
      Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ W) => φ.hom c)
    (AlgebraicGeometry.Scheme.Hom.appLE_map J.hom
      (show jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U) ≤ J.hom ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ U) by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage, J.over])
      (CategoryTheory.homOfLE (show jetNeighborhood.proj L κ ⁻¹ᵁ W ≤ jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U) from
        fun z hz => hW hz)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hres
  exact congrArg _ hres

/-- **Germ criterion through the `ξ`-expansion**: for `y ∈ W ≤ ρ⁻¹U`, the germ at `y` of `J.pieceSection U n _ c` lies
in `𝔪_y • ⊤` iff the germ at `y` of the `n`-th piece of the `ξ`-expansion on `W` does
(`germ_res_mem_maximalIdeal_smul_iff`, `res_pieceSection`, `germ_hom_app_mem_maximalIdeal_smul_iff_of_iso`). -/
theorem BasedJet.germ_pieceSection_mem_iff (J : BasedJet f ρ L κ) (y : ρ.source.toScheme) (U : C.toScheme.Opens)
    {W : ρ.source.toScheme.Opens} (hW : W ≤ ρ.hom ⁻¹ᵁ U) (hyW : y ∈ W) (n : ℕ) (hn : n ≤ κ)
    (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U)) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.germ
        (ρ.hom ⁻¹ᵁ U) y (hW hyW) (J.pieceSection U n hn c) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) n).presheaf.stalk y)) ↔
    (truncatedJetAlgebra.piece L n).presheaf.germ W y hyW
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨n, Nat.lt_succ_of_le hn⟩).app W (J.xiExpansion U hW c)) ∈
      (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y) ((truncatedJetAlgebra.piece L n).presheaf.stalk y)) := by
  rw [← AlgebraicGeometry.Scheme.Modules.germ_res_mem_maximalIdeal_smul_iff _ hW hyW (J.pieceSection U n hn c),
    J.res_pieceSection U hW n hn c]
  exact AlgebraicGeometry.Scheme.Modules.germ_hom_app_mem_maximalIdeal_smul_iff_of_iso
    (truncatedJetAlgebra.pieceIso L n) W hyW _

end
