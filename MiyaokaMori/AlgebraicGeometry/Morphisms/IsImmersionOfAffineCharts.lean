import MiyaokaMori.Prelude

/-! # An immersion criterion through affine charts

**Immersion criterion through affine charts** (Stacks 01VU, third paragraph; 01O9; 07RK): a morphism
`r : X ⟶ Y` is an immersion as soon as there is a family of **affine** opens `U i ⊆ Y` covering the image of `r`
such that every preimage `r⁻¹(U i)` is affine and every ring map `Γ(U i, O_Y) → Γ(r⁻¹U i, O_X)` is surjective.

Proof. `IsImmersion` is Zariski-local on the target and stable under
composition with open immersions on the right, so by Mathlib `IsZariskiLocalAtTarget.of_range_subset_iSup` it
suffices to show that each restriction `r ∣_ U i : r⁻¹(U i) ⟶ U i` is an immersion. Both schemes are affine and
`(r ∣_ U i).appTop` is, up to the identification `(U i).ι ''ᵁ ⊤ = U i`, the surjective map
`r.appLE (U i) (r⁻¹U i)`; a morphism of affine schemes surjective on global sections is a closed immersion
(Mathlib `IsClosedImmersion.of_surjective_of_isAffine`), hence an immersion.

Used in Stacks 07RM, Step 5; it is the target-side generalisation of
`isImmersion_projectivizationMorphism_of_charts` (`ProjectivizationChartImmersion.lean`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A morphism of affine schemes with surjective map on global sections is an immersion (it is a closed
immersion, Mathlib `IsClosedImmersion.of_surjective_of_isAffine`). -/
theorem AlgebraicGeometry.isImmersion_of_surjective_of_isAffine {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y] (f : X ⟶ Y)
    (h : Function.Surjective f.appTop) : AlgebraicGeometry.IsImmersion f :=
  haveI : AlgebraicGeometry.IsClosedImmersion f :=
    AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine f h
  inferInstance

/-- The restriction `r ∣_ U` to an open `U` of the target is surjective on global sections iff
`r.appLE U (r⁻¹U)` is. -/
theorem AlgebraicGeometry.morphismRestrict_appTop_surjective_iff {X Y : AlgebraicGeometry.Scheme.{u}}
    (r : X ⟶ Y) (U : Y.Opens) :
    Function.Surjective (r ∣_ U).appTop ↔ Function.Surjective (r.appLE U (r ⁻¹ᵁ U) le_rfl) := by
  have h1 : (r ∣_ U).appTop = (r ∣_ U).appLE ⊤ ((r ∣_ U) ⁻¹ᵁ ⊤) le_rfl := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  rw [h1, AlgebraicGeometry.morphismRestrict_appLE]
  have hU : U.ι ''ᵁ ⊤ = U := AlgebraicGeometry.Scheme.Opens.ι_image_top U
  have hV : (r ⁻¹ᵁ U).ι ''ᵁ ((r ∣_ U) ⁻¹ᵁ ⊤) = r ⁻¹ᵁ U :=
    (AlgebraicGeometry.image_morphismRestrict_preimage r U ⊤).trans (congrArg (fun W => r ⁻¹ᵁ W) hU)
  exact r.appLE_congr _ hU hV (fun g => Function.Surjective g)

/-- **Immersion criterion**: `r` is an immersion if the range of `r` is covered by affine opens `U i` with affine
preimages and surjective ring maps `Γ(U i, O_Y) → Γ(r⁻¹U i, O_X)`. -/
theorem AlgebraicGeometry.isImmersion_of_affine_charts {X Y : AlgebraicGeometry.Scheme.{u}} (r : X ⟶ Y)
    {ι : Type v} (U : ι → Y.Opens) (hcov : ∀ x : X, ∃ i, r.base x ∈ U i)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hpre : ∀ i, AlgebraicGeometry.IsAffineOpen (r ⁻¹ᵁ U i))
    (hsurj : ∀ i, Function.Surjective (r.appLE (U i) (r ⁻¹ᵁ U i) le_rfl)) :
    AlgebraicGeometry.IsImmersion r := by
  have hRR : MorphismProperty.RespectsRight (C := AlgebraicGeometry.Scheme.{u})
      @AlgebraicGeometry.IsImmersion @AlgebraicGeometry.IsOpenImmersion :=
    ⟨fun i hi f hf => by
      have : AlgebraicGeometry.IsImmersion f := hf
      have : AlgebraicGeometry.IsOpenImmersion i := hi
      infer_instance⟩
  apply AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup (P := @AlgebraicGeometry.IsImmersion) U
  · rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := hcov x
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    exact ⟨i, hi⟩
  · intro i
    have : AlgebraicGeometry.IsAffine (U i).toScheme := hU i
    have : AlgebraicGeometry.IsAffine (r ⁻¹ᵁ U i).toScheme := hpre i
    exact AlgebraicGeometry.isImmersion_of_surjective_of_isAffine (r ∣_ U i)
      ((AlgebraicGeometry.morphismRestrict_appTop_surjective_iff r (U i)).2 (hsurj i))

end
