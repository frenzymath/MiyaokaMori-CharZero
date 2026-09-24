import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.PositiveLineCoreWeightedRescaling_AffineJet
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueFieldSectionsGerm

/-! # The generic affine jet: `ĵ^♯` on constants is a germ, and `ĵ` lies over every open containing `η_C`
(helper for Lemma 3.1 of the paper)

`affineJetSectionsHom ĵ hW : S(W) →+* R` (`PositiveLineCoreWeightedRescaling_AffineJet`) is the ring homomorphism
`ĵ^♯ ∘ Θ_W` of an `R`-point `ĵ : Spec R → J_κ^s` over `W`; `affineJetCoordAt` is its value on the pieces
(`affineJetCoordAt_eq_affineJetSectionsHom`), it is compatible with restriction
(`affineJetSectionsHom_sectionsRestrictHom`) and on constants it is `ĵ^♯ ∘ π^♯`
(`affineJetSectionsHom_sectionsUnitHom`). This module adds what the transition lemma needs for the
**generic affine jet** `ĵ : Spec κ(η_{C̃}) → J_κ^s` over `η_{C̃} ≫ ρ`:

* `affineJetCoord_eq_affineJetSectionsHom`: `affineJetCoord` (the `K(C̃)`-valued coordinates) is
  `ι_K⁻¹ ∘ affineJetSectionsHom` on the pieces;
* `affineJetSectionsHom_unit`: on constants, `ĵ^♯` is `(ĵ ≫ π)^♯` (`Scheme.Hom.appLE_comp_appLE`);
* `affineJetSectionsHom_unit_eq_germ`: read in `K(C̃)`, a constant `r ∈ Γ(C, V)` goes to the germ of
  `ρ^♯ r` at the generic point, i.e. to `algebraMap (O_{C̃,y}) K(C̃)` of its germ at any `y` over `V`
  (`functionFieldIsoResidueField_inv_ΓSpecIso_hom_appLE`, `Scheme.algebraMap_germ_eq_germToFunctionField`);
* `top_le_preimage_of_genericPoint_mem`: `ĵ` lies over every open containing `η_C`, because
  `π(ĵ) = ρ(η_{C̃}) = η_C` (`FiniteCover.hom_genericPoint`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}

/-- `affineJetCoord` is `ι_K⁻¹ ∘ affineJetSectionsHom` on `ofPiece x`
(`affineJetCoord_eq_affineJetCoordAt`, `affineJetCoordAt_eq_affineJetSectionsHom`). -/
theorem affineJetCoord_eq_affineJetSectionsHom {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (m : ℕ) (x : (jetAlgebra f κ).sectionsPiece V m) :
    affineJetCoord ρ ĵ hV m x =
      (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
       ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
        (affineJetSectionsHom ĵ hV ((jetAlgebra f κ).ofPiece V m x))) := by
  rw [affineJetCoord_eq_affineJetCoordAt, affineJetCoordAt_eq_affineJetSectionsHom]

/-- On the constants, `ĵ^♯` is `(ĵ ≫ π)^♯` (`affineJetSectionsHom_sectionsUnitHom`,
`Scheme.Hom.appLE_comp_appLE`). -/
theorem affineJetSectionsHom_unit {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    {R : CommRingCat.{u}}
    (ĵ : AlgebraicGeometry.Spec R ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec R).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (r : Γ(C.toScheme, V)) :
    affineJetSectionsHom ĵ hV ((jetAlgebra f κ).sectionsUnitHom V r) =
      (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom
        (((ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom).appLE
          V ⊤ hV).hom r) := by
  rw [affineJetSectionsHom_sectionsUnitHom, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
  show (AlgebraicGeometry.Scheme.ΓSpecIso R).hom.hom
    (((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.appLE V
        ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)
        le_rfl ≫
      ĵ.appLE ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)
        ⊤ hV).hom r) = _
  rw [AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE]

/-- Two equal morphisms have equal `appLE` (proof-irrelevant in the inclusion). -/
private theorem affineJet_appLE_congr_hom {T Y : AlgebraicGeometry.Scheme.{u}} {φ ψ : T ⟶ Y}
    (hφψ : φ = ψ) (U : Y.Opens) (e : (⊤ : T.Opens) ≤ φ ⁻¹ᵁ U) (e' : (⊤ : T.Opens) ≤ ψ ⁻¹ᵁ U) :
    φ.appLE U ⊤ e = ψ.appLE U ⊤ e' := by
  subst hφψ
  rfl

/-- **The constants of the generic affine jet are germs at the generic point.** For `ĵ` over
`η_{C̃} ≫ ρ`, `y ∈ ρ⁻¹V` and `r ∈ Γ(C, V)`: `ι_K⁻¹ (ĵ^♯ r) = algebraMap (O_{C̃,y}) K(C̃) (germ_y (ρ^♯ r))`
(`affineJetSectionsHom_unit`, `functionFieldIsoResidueField_inv_ΓSpecIso_hom_appLE`,
`Scheme.algebraMap_germ_eq_germToFunctionField`). -/
theorem affineJetSectionsHom_unit_eq_germ {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {V : C.toScheme.Opens}
    (hV : (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V))
    (y : ρ.source.toScheme) (hy : y ∈ ρ.hom ⁻¹ᵁ V) (r : Γ(C.toScheme, V)) :
    (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
     ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
      (affineJetSectionsHom ĵ hV ((jetAlgebra f κ).sectionsUnitHom V r))) =
      algebraMap (ρ.source.toScheme.presheaf.stalk y) ρ.source.toScheme.functionField
        (ρ.source.toScheme.presheaf.germ (ρ.hom ⁻¹ᵁ V) y hy ((ρ.hom.app V).hom r)) := by
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have : Nonempty (ρ.hom ⁻¹ᵁ V) := ⟨⟨y, hy⟩⟩
  set η := ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) with hη_def
  have hηV : genericPoint ρ.source.toScheme ∈ ρ.hom ⁻¹ᵁ V :=
    (genericPoint_specializes y).mem_open (ρ.hom ⁻¹ᵁ V).isOpen hy
  have hη' : (⊤ : (AlgebraicGeometry.Spec
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      η ⁻¹ᵁ (ρ.hom ⁻¹ᵁ V) := by
    intro s _
    show η.base s ∈ ρ.hom ⁻¹ᵁ V
    have hs : η.base s = genericPoint ρ.source.toScheme :=
      AlgebraicGeometry.Scheme.fromSpecResidueField_apply _ s
    rw [hs]
    exact hηV
  have e : (⊤ : (AlgebraicGeometry.Spec
      (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      (η ≫ ρ.hom) ⁻¹ᵁ V := hη'
  rw [affineJetSectionsHom_unit, affineJet_appLE_congr_hom hĵ V hV e,
    ← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE η ρ.hom V (ρ.hom ⁻¹ᵁ V) ⊤ le_rfl hη',
    AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  show ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso _).hom.hom
      ((η.appLE (ρ.hom ⁻¹ᵁ V) ⊤ hη').hom ((ρ.hom.app V).hom r))) = _
  rw [AlgebraicGeometry.Scheme.functionFieldIsoResidueField_inv_ΓSpecIso_hom_appLE _ hηV hη',
    AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField ρ.source.toScheme hy]

/-- **The generic affine jet lies over every open containing `η_C`**: `π(ĵ) = ρ(η_{C̃}) = η_C`
(`FiniteCover.hom_genericPoint`). -/
theorem top_le_preimage_of_genericPoint_mem {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {κ : ℕ}
    (ρ : FiniteCover k C)
    (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
      (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
    (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)
    {V : C.toScheme.Opens} (hη : genericPoint C.toScheme ∈ V) :
    (⊤ : (AlgebraicGeometry.Spec
        (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom
        ⁻¹ᵁ V) := by
  intro s _
  show (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
    (ĵ.base s) ∈ V
  have h1 : (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom.base
      (ĵ.base s) =
      ρ.hom.base ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base s) :=
    congrArg (fun φ : AlgebraicGeometry.Spec _ ⟶ C.toScheme => φ.base s) hĵ
  have hs : (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base s =
      genericPoint ρ.source.toScheme :=
    AlgebraicGeometry.Scheme.fromSpecResidueField_apply _ s
  rw [h1, hs, ρ.hom_genericPoint]
  exact hη

end
