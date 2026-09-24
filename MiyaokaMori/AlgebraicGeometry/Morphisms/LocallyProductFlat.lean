import MiyaokaMori.Prelude

/-! # Locally a product implies flat

A morphism which, over an open cover of the base, is isomorphic to the projection from a product
with a fixed fiber is flat: flatness is local on the base, and a projection is a base change of a
flat morphism. (Used for the deformation family of Lemma 2.3 of the paper.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem flat_of_locally_product {Y X S F : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (p : X ⟶ S) (q : F ⟶ S) [AlgebraicGeometry.Flat q] (𝒰 : X.OpenCover)
    (e : ∀ i, ∃ φ : CategoryTheory.Limits.pullback f (𝒰.f i) ≅
        CategoryTheory.Limits.pullback (𝒰.f i ≫ p) q,
        φ.hom ≫ CategoryTheory.Limits.pullback.fst (𝒰.f i ≫ p) q = 𝒰.pullbackHom f i) :
    AlgebraicGeometry.Flat f := by
  let _ : AlgebraicGeometry.IsZariskiLocalAtTarget @AlgebraicGeometry.Flat :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget
      @AlgebraicGeometry.Flat (Q := @RingHom.Flat)
  refine (AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
    (P := @AlgebraicGeometry.Flat) 𝒰).mpr fun i ↦ ?_
  obtain ⟨φ, hφ⟩ := e i
  rw [← hφ]
  have hφflat : AlgebraicGeometry.Flat φ.hom :=
    AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion
      (P := @AlgebraicGeometry.Flat) (Q := @RingHom.Flat) RingHom.Flat.containsIdentities
  have hfst : AlgebraicGeometry.Flat
      (CategoryTheory.Limits.pullback.fst (𝒰.f i ≫ p) q) :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback (𝒰.f i ≫ p) q).flip inferInstance
  exact @AlgebraicGeometry.Flat.comp _ _ _ φ.hom _ hφflat hfst

end
