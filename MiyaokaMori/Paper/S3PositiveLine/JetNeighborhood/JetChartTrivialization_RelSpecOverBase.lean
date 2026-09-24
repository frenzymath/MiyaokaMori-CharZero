import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine

/-! # The affine chart of a relative Spec is an isomorphism over the base

**The chart `Spec 𝒜(U) ≅ π⁻¹U` of a relative Spec is an isomorphism over `U`**: for a quasi-coherent
algebra `𝒜` on `X` with `π : Spec_X 𝒜 → X` and an affine open `U`,
`affineIso.hom ≫ Spec(unit : Γ(X, U) → 𝒜(U)) = (π ∣_ U) ≫ (U ≅ Spec Γ(X, U))`.
Proof: `affineIso.inv ≫ ι_{π⁻¹U} = chart` (`relativeSpec.affineIso_inv_ι`) and
`chart ≫ π = Spec(unit) ≫ isoSpec.inv ≫ U.ι` (`AffineAlgebra.chart_hom`, `chartToOpen`), so after cancelling
the monomorphism `U.ι` (`morphismRestrict_ι`) we get `affineIso.inv ≫ (π ∣_ U) = Spec(unit) ≫ isoSpec.inv`.
Source: Stacks 01LX (3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The chart of a relative Spec over an affine open is an isomorphism over that open (see module docstring). -/
theorem AlgebraicGeometry.Scheme.relativeSpec.affineIso_hom_Spec_map_sectionsUnit {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.sectionsUnit U.1)) =
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ∣_ U.1) ≫ U.2.isoSpec.hom := by
  have h1 : (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ∣_ U.1) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.sectionsUnit U.1)) ≫ U.2.isoSpec.inv := by
    apply (cancel_mono U.1.ι).mp
    rw [Category.assoc, AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc,
      AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι, Category.assoc]
    exact A.toAffineAlgebra.chart_hom ⟨U.1, U.2⟩
  have h2 : ((AlgebraicGeometry.Scheme.relativeSpec A).hom ∣_ U.1) =
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.sectionsUnit U.1)) ≫ U.2.isoSpec.inv := by
    rw [← h1, Iso.hom_inv_id_assoc]
  rw [h2, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
