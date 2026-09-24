import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0ha1

/-! # Additivity of stalk dimension along a flat morphism

Stacks 02JS, step 1 (the local-ring part): for a flat morphism `f : X → Y` of locally Noetherian
schemes and `x ↦ y`, `dim 𝒪_{X,x} = dim 𝒪_{Y,y} + dim 𝒪_{X_y,x}`.

Source: Stacks 00ON (Algebra, lemma-dimension-formula-going-down; in Mathlib as
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), Stacks 00HS (flat ⇒ going down; Mathlib
`Algebra.HasGoingDown.of_flat`), Stacks 0HA1 (`𝒪_{X_y,x} ≅ 𝒪_{X,x}/𝔪_y 𝒪_{X,x}`; this project's
`AlgebraicGeometry.Scheme.Hom.fiber_stalk_iso`).

Proof. Let `A := 𝒪_{Y,y}`, `B := 𝒪_{X,x}`, `φ := f.stalkMap x : A → B`. `φ` is a local
homomorphism and is flat (`AlgebraicGeometry.Flat.stalkMap`), so `B` satisfies going down over `A`
and `𝔪_B` lies over `𝔪_A`. Since `A` and `B` are Noetherian, 00ON gives
`ht 𝔪_B = ht 𝔪_A + ht (𝔪_B / 𝔪_A B)` in `B/𝔪_A B`. In a local ring the height of the maximal ideal is
the Krull dimension (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`), and `B/𝔪_A B` is local
with maximal ideal `𝔪_B/𝔪_A B` (`φ` local ⇒ `𝔪_A B ≤ 𝔪_B ≠ ⊤`). Finally 0HA1 identifies
`𝒪_{X_y,x}` with `B/𝔪_A B`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

section ring

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- **Stacks 00ON for local rings.** For a flat local homomorphism `φ : A → B` of local rings with
`B` Noetherian, `dim B = dim A + dim B/𝔪_A B`. -/
theorem ringKrullDim_eq_add_quotient_map_maximalIdeal_of_flat [IsNoetherianRing A]
    [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map φ) := by
  let _ : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hφ
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom φ›
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  have hI_ne : (maximalIdeal A).map φ ≠ ⊤ := (map_maximalIdeal_lt_top φ).ne
  have : Nontrivial (B ⧸ (maximalIdeal A).map φ) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  have : IsLocalRing (B ⧸ (maximalIdeal A).map φ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal B).map (Ideal.Quotient.mk ((maximalIdeal A).map φ)) =
      maximalIdeal (B ⧸ (maximalIdeal A).map φ) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h' : (maximalIdeal B).height = (maximalIdeal A).height +
      ((maximalIdeal B).map (Ideal.Quotient.mk ((maximalIdeal A).map φ))).height := h
  rw [hmax] at h'
  rw [← maximalIdeal_height_eq_ringKrullDim (R := B), ← maximalIdeal_height_eq_ringKrullDim (R := A),
    ← maximalIdeal_height_eq_ringKrullDim (R := B ⧸ (maximalIdeal A).map φ), ← WithBot.coe_add, h']

end ring

/-- **Stacks 02JS, local-ring part.** For a flat morphism `f : X → Y` of locally Noetherian schemes
and `x ∈ X`, `dim 𝒪_{X,x} = dim 𝒪_{Y,f x} + dim 𝒪_{X_{f x}, x}`. -/
theorem ringKrullDim_stalk_eq_add_fiber_stalk {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f.base x)) +
      ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) := by
  obtain ⟨e⟩ := f.fiber_stalk_iso x
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact ringKrullDim_eq_add_quotient_map_maximalIdeal_of_flat (f.stalkMap x).hom (Flat.stalkMap f x)

end AlgebraicGeometry

end
