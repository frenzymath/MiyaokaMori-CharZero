import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraFlatPullback

/-! # Stacks 0805: blowing up commutes with flat base change

If `g : X₁ → X₂` is flat, the blowup of `X₁` along `g⁻¹Z` is `X₁ ×_{X₂} Bl_Z X₂`. In particular
blowing up commutes with restriction to open subschemes and with the localizations
`Spec O_{X,x} → X`; this is what makes the point blowups in the proof of Corollary 4.3 of the paper (§4) isomorphisms away from the centre and allows the
exceptional curve to be computed locally.

Proof: three pieces are composed.
1. `IdealSheafData.reesAlgebra_comap_iso_pullback_of_flat`: for `g` flat,
   `𝓡(g⁻¹I·O_{X₁}) ≅ g^*𝓡(I)` as graded quasi-coherent algebras.
2. `relativeProj.exists_iso_of_algebra_iso`: `Proj_{X₁} 𝓡(g⁻¹I) ≅ Proj_{X₁} g^*𝓡(I)` over `X₁`.
3. `relativeProj_baseChange` (Stacks 01O3): `Proj_{X₁} g^*𝓡(I) ≅ X₁ ×_{X₂} Proj_{X₂} 𝓡(I)`,
   compatible with the first projection.
Composing the two isomorphisms gives `e`; the compatibility
`e.hom ≫ pullback.fst = (blowup (I.comap g)).hom` is the composite of the two compatibilities.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0805.** For a flat morphism `g : X₁ → X₂` and an ideal sheaf `I` on `X₂`, the blowup of
`X₁` along `g⁻¹I` is isomorphic over `X₁` to the base change `X₁ ×_{X₂} Bl_I X₂`. -/
theorem AlgebraicGeometry.Scheme.blowup_flatBaseChange {X₁ X₂ : AlgebraicGeometry.Scheme.{u}}
    (g : X₁ ⟶ X₂) [AlgebraicGeometry.Flat g] (I : X₂.IdealSheafData) :
    ∃ e : (AlgebraicGeometry.Scheme.blowup (I.comap g)).left ≅
        CategoryTheory.Limits.pullback g (AlgebraicGeometry.Scheme.blowup I).hom,
      e.hom ≫ CategoryTheory.Limits.pullback.fst _ _ = (AlgebraicGeometry.Scheme.blowup (I.comap g)).hom := by
  unfold AlgebraicGeometry.Scheme.blowup
  obtain ⟨φ⟩ := AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebra_comap_iso_pullback_of_flat g I
  obtain ⟨e₁, he₁, -⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso φ
  obtain ⟨e₀, he₀, -⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange g I.reesAlgebra
  refine ⟨e₁ ≪≫ e₀, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he₀, he₁]

end
