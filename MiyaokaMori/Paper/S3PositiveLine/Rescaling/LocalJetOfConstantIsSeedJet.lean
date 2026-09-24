import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetOfRingMap

/-! # The local jet of a constant ring map is the seed jet
(helper for Lemma 3.1 of the paper; the degenerate case `γ = 0` of
`localJet_eq_of_generic`, where all positive-weight pieces of `Ψ` vanish)

If `Ψ : B_V → 𝒜(W)` is `c ↦ sectionsUnit (ρ^♯ (s^♯ c))` (constant term `s^♯`, no positive pieces), then
its local jet `p_L⁻¹(W) → 𝒵` is the seed jet `p_L⁻¹(W) ↪ C̃_(κ)(L) → C̃ → C → 𝒵`:
`Spec.map (s^♯) ≫ fromSpec_{π⁻¹V} = fromSpec_V ≫ s` and `Spec.map (ρ^♯) ≫ fromSpec_V = fromSpec_W ≫ ρ`
(`IsAffineOpen.SpecMap_appLE_fromSpec`), and `affineIso.hom ≫ Spec.map (sectionsUnit) ≫ fromSpec_W =
p_L⁻¹(W).ι ≫ p_L` (`relativeSpec.affineIso_hom_Spec_map_sectionsUnit`, as in `localJet_over`).

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

set_option backward.isDefEq.respectTransparency false in
/-- **The local jet of the constant ring map `c ↦ ρ^♯ (s^♯ c) · 1` is the seed jet**
`p_L⁻¹(W).ι ≫ p_L ≫ ρ ≫ s`. -/
theorem localJet_eq_seed {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    {W : ρ.source.toScheme.Opens} (hW : AlgebraicGeometry.IsAffineOpen W) (hWV : W ≤ ρ.hom ⁻¹ᵁ V)
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W))
    (hΨ : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V),
      Ψ.hom c = (truncatedJetAlgebra L κ).sectionsUnit W ((ρ.hom.appLE V W hWV).hom
        (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
          (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c))) :
    localJet f κ ρ L hV hW Ψ =
      (jetNeighborhood.proj L κ ⁻¹ᵁ W).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom ≫ (MMSetup.seed f).1 := by
  have hπV := cone_preimage_isAffineOpen f hV
  have hcomp : Ψ = (MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
      (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V) ≫
      ρ.hom.appLE V W hWV ≫ CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit W) := by
    ext c
    exact hΨ c
  have h1 : AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit W)) ≫
        hW.fromSpec ≫ ρ.hom ≫ (MMSetup.seed f).1 := by
    rw [hcomp, AlgebraicGeometry.Spec.map_comp, AlgebraicGeometry.Spec.map_comp, Category.assoc, Category.assoc,
      AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec (MMSetup.seed f).1 hπV hV
        (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V),
      ← Category.assoc (AlgebraicGeometry.Spec.map (ρ.hom.appLE V W hWV)) hV.fromSpec,
      AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ρ.hom hV hW hWV, Category.assoc]
  have h2 : (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit W)) ≫
        hW.fromSpec = (jetNeighborhood.proj L κ ⁻¹ᵁ W).ι ≫ jetNeighborhood.proj L κ := by
    rw [← Category.assoc,
      AlgebraicGeometry.Scheme.relativeSpec.affineIso_hom_Spec_map_sectionsUnit (truncatedJetAlgebra L κ)
        ⟨W, hW⟩, ← AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
    exact AlgebraicGeometry.morphismRestrict_ι _ _
  have h2' : ((AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit W))) ≫
        hW.fromSpec = (jetNeighborhood.proj L κ ⁻¹ᵁ W).ι ≫ jetNeighborhood.proj L κ := by
    rw [Category.assoc]; exact h2
  show (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨W, hW⟩).hom ≫
    AlgebraicGeometry.Spec.map Ψ ≫ hπV.fromSpec = _
  rw [h1]
  simp only [← Category.assoc]
  rw [h2']

end jetNeighborhood

end
