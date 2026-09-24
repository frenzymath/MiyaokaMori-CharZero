import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfRingMap

/-! # Points of `p_L⁻¹(W) ≅ Spec 𝒜(W)` given by ring maps, and hom-extensionality for affine sources
(helper for Lemma 3.1 of the paper)

(Hom-extensionality for morphisms from an affine scheme into an affine open is `isAffine_hom_ext_of_appLE` in
`LocalJetGluing`.)
* `pointOfRingHom φ : Y → p_L⁻¹(W)` for a ring map `φ : 𝒜(W) → Γ(Y, ⊤)`
  (`Y.toSpecΓ ≫ Spec.map φ ≫ affineIso.inv`); its ring map on `⊤` is `φ` up to the identifications
  (`pointOfRingHom_appTop`), and composed with a local jet `g_Ψ` it has ring map `Ψ ≫ φ` on `B_V`
  (`pointOfRingHom_localJet_appLE`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)
  (L : LineBundle ρ.source.toVariety)
  {W : ρ.source.toScheme.Opens} (hW : AlgebraicGeometry.IsAffineOpen W) {Y : AlgebraicGeometry.Scheme.{u}}
  (φ : CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W) ⟶ Γ(Y, ⊤))

/-- **The point of `p_L⁻¹(W) ≅ Spec 𝒜(W)` attached to a ring map** `φ : 𝒜(W) → Γ(Y, ⊤)`. -/
def pointOfRingHom : Y ⟶ (jetNeighborhood.proj L κ ⁻¹ᵁ W).toScheme :=
  Y.toSpecΓ ≫ AlgebraicGeometry.Spec.map φ ≫
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).inv

/-- The ring map of `pointOfRingHom φ` on `⊤` is `affineIso.inv.appTop ≫ ΓSpecIso.hom ≫ φ`
(`toSpecΓ_appTop`, `ΓSpecIso_naturality`). -/
theorem pointOfRingHom_appTop :
    (pointOfRingHom κ ρ L hW φ).appTop =
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).inv.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso _).hom ≫ φ := by
  show (Y.toSpecΓ ≫ AlgebraicGeometry.Spec.map φ ≫
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).inv).appTop = _
  rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.comp_appTop,
    AlgebraicGeometry.Scheme.toSpecΓ_appTop, Category.assoc]
  congr 1
  exact AlgebraicGeometry.Scheme.ΓSpecIso_naturality φ

/-- `pointOfRingHom φ ≫ g_Ψ` lands in `π⁻¹V`. -/
theorem top_le_pointOfRingHom_localJet_preimage {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W)) :
    (⊤ : Y.Opens) ≤ (pointOfRingHom κ ρ L hW φ ≫ localJet f κ ρ L hV hW Ψ) ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
  fun x _ => top_le_localJet_preimage f κ ρ L hV hW Ψ (x := (pointOfRingHom κ ρ L hW φ).base x) trivial

set_option backward.isDefEq.respectTransparency false in
/-- **The ring map of `pointOfRingHom φ ≫ g_Ψ` on `B_V` is `Ψ ≫ φ`** (`localJet_appLE`, `pointOfRingHom_appTop`;
the identifications `ΓSpecIso`, `affineIso` cancel). -/
theorem pointOfRingHom_localJet_appLE {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W)) :
    (pointOfRingHom κ ρ L hW φ ≫ localJet f κ ρ L hV hW Ψ).appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤
        (top_le_pointOfRingHom_localJet_preimage f κ ρ L hW φ hV Ψ) = Ψ ≫ φ := by
  set e := AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩ with he
  have e₂ : (⊤ : Y.Opens) ≤ (pointOfRingHom κ ρ L hW φ) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (pointOfRingHom κ ρ L hW φ) (localJet f κ ρ L hV hW Ψ)
    ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ ⊤ (top_le_localJet_preimage f κ ρ L hV hW Ψ) e₂]
  have h2 : (pointOfRingHom κ ρ L hW φ).appLE ⊤ ⊤ e₂ = (pointOfRingHom κ ρ L hW φ).appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.appTop, AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
    rfl
  have h3 : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, Iso.inv_hom_id, AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [localJet_appLE, h2, pointOfRingHom_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc e.hom.appTop e.inv.appTop, h3, Category.id_comp, Iso.inv_hom_id_assoc]

end jetNeighborhood

end
