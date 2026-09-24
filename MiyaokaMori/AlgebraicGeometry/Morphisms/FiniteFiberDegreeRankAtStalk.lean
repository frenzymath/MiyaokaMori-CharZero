import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.AffineSchemeOverFieldLengthResidueDegreeSum
import MiyaokaMori.AlgebraicGeometry.Morphisms.PushforwardRankAtStalkFiberSections
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardDivisorViaGenericFiber

/-! # The fiber degree of a finite morphism equals the rank of the pushforward

For a finite morphism `f : X → Y` and `y ∈ Y`, the fiber degree at `y` is
`Σ_{x ∈ f⁻¹{y}} length(O_{F,x})·[κ(x):κ(y)] = rank_y (f_*O_X)` (Stacks 02RH, steps 3–4 of the proof;
Stacks 02M0).

## Route

Write `k := κ(y)`, `F := f.fiber y`, `ι := f.fiberι y : F ⟶ X`, `q := f.fiberToSpecResidueField y : F ⟶ Spec k`.
1. **Reindex along `ι`.** `ι` is injective with image `f ⁻¹' {y}` (`Scheme.Hom.range_fiberι`, `isEmbedding`), so
   `∑ᶠ x ∈ f⁻¹{y}, φ x = ∑ᶠ ξ : F, φ (ι ξ)` (`finsum_mem_range`).
2. **Summand.** For `x = ι ξ` we have `f x = y`; transporting along this equality (`subst`) identifies the stalk
   `O_{f.fiber (f x), asFiber x}` with `O_{F, ξ}` (`length_stalk_fiber_asFiber_eq`, `fiberHomeo_symm_fiberι`), and
   `f.residueDegree (ι ξ) = q.residueDegree ξ` (`Scheme.Hom.residueDegree_fiberToSpecResidueField`: `ι ≫ f = q ≫ s`
   with `ι`, `s` preimmersions of residue degree `1`). 
3. **Affine scheme over a field**: `q` is finite
   (base change of `f`), so `Γ(F, O_F)` is a finite `k`-algebra (`Scheme.Hom.finite_appTop`) and
   `∑ᶠ ξ : F, length(O_{F,ξ})·q.residueDegree ξ = dim_k Γ(F, O_F)` — Artinian decomposition + Stacks 02M0.
4. **Rank of the pushforward**:
   `rank_y (f_* O_X) = dim_k Γ(F, O_F)` for the affine morphism `f`
   (stalk of the quasi-coherent `f_*O_X` = localization of `Γ(X, f⁻¹U)`;
   `Γ(F) = κ(y) ⊗_R Γ(X, f⁻¹U)` from Mathlib's `isIso_pushoutSection_of_isAffineOpen`).
5. Cast to `ℤ` (`F` is finite, `IsArtinianScheme (f.fiber y)`, so both `finsum`s are finite sums).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Transport of the local ring of the fiber at `asFiber x` along `f x = y`: the stalk of `f.fiber (f x)` at
`f.asFiber x` is (definitionally, after `subst`) the stalk of `f.fiber y` at `(f.fiberHomeo y).symm ⟨x, hx⟩`. -/
theorem Scheme.Hom.length_stalk_fiber_asFiber_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y} (x : X)
    (hx : f.base x = y) :
    Module.length ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
        ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
      = Module.length ((f.fiber y).presheaf.stalk ((f.fiberHomeo y).symm ⟨x, hx⟩))
          ((f.fiber y).presheaf.stalk ((f.fiberHomeo y).symm ⟨x, hx⟩)) := by
  subst hx; rfl

/-- `(f.fiberHomeo y).symm ⟨ι ξ, _⟩ = ξ` for `ι = f.fiberι y` (`fiberHomeo_apply`). -/
theorem Scheme.Hom.fiberHomeo_symm_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (ξ : f.fiber y)
    (h : f.base ((f.fiberι y).base ξ) = y) :
    (f.fiberHomeo y).symm ⟨(f.fiberι y).base ξ, h⟩ = ξ := by
  have : (⟨(f.fiberι y).base ξ, h⟩ : f.base ⁻¹' {y}) = f.fiberHomeo y ξ := Subtype.ext rfl
  rw [this, Homeomorph.symm_apply_apply]

end AlgebraicGeometry

/-- **Fiber degree of a finite morphism** (Stacks 02RH, steps 3–4 of the proof; Algebra 02M0).
Let `f : X → Y` be finite and `y ∈ Y`, `F = f.fiber y = X ×_Y Spec κ(y)`. Then
`∑_{x ∈ f⁻¹{y}} length(O_{F,x}) · [κ(x) : κ(y)] = rank_y (f_* O_X)`, where `rank_y M = dim_{κ(y)} (κ(y) ⊗ M_y)`
(`Scheme.Modules.rankAtStalk`). No flatness and no Noetherian hypothesis is needed.

Proof: see the module docstring (reindex along `fiberι`, transport the summand, apply
`Scheme.Hom.finsum_length_stalk_mul_residueDegree_eq_finrank_of_isAffine` to `q : F ⟶ Spec κ(y)` and
`Scheme.Hom.rankAtStalk_pushforward_unit_eq_finrank_fiber_sections` to `f`).
Edge cases: if `y ∉ f(X)` then `F = ∅`, `Γ(F) = 0`, both sides are `0`; non-reduced fibers contribute their lengths. -/
theorem AlgebraicGeometry.Scheme.Hom.finsum_length_fiber_mul_residueDegree_eq_rankAtStalk
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] (y : Y) :
    ∑ᶠ x ∈ f.base ⁻¹' {y},
      ((Module.length ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))
          ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x))).toNat : ℤ) * (f.residueDegree x : ℤ)
      = (AlgebraicGeometry.Scheme.Modules.rankAtStalk
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) y : ℤ) := by
  open AlgebraicGeometry in
  -- Step 1: reindex the sum along the fiber embedding ι : F → X (injective, image f⁻¹{y}).
  have hinj : Function.Injective (f.fiberι y).base := (f.fiberι y).isEmbedding.injective
  have hrange : Set.range (f.fiberι y).base = f.base ⁻¹' {y} := f.range_fiberι y
  rw [← hrange, finsum_mem_range hinj]
  -- Step 2: the summand at ι ξ is length(O_{F,ξ}) · q.residueDegree ξ.
  have hsum : ∀ ξ : f.fiber y,
      ((Module.length
          ((f.fiber (f.base ((f.fiberι y).base ξ))).presheaf.stalk (f.asFiber ((f.fiberι y).base ξ)))
          ((f.fiber (f.base ((f.fiberι y).base ξ))).presheaf.stalk
            (f.asFiber ((f.fiberι y).base ξ)))).toNat : ℤ)
        * (f.residueDegree ((f.fiberι y).base ξ) : ℤ)
      = ((Module.length ((f.fiber y).presheaf.stalk ξ) ((f.fiber y).presheaf.stalk ξ)).toNat : ℤ)
        * ((f.fiberToSpecResidueField y).residueDegree ξ : ℤ) := by
    intro ξ
    have h : f.base ((f.fiberι y).base ξ) = y := by
      have := Set.mem_range_self (f := (f.fiberι y).base) ξ
      rw [hrange] at this
      exact this
    rw [Scheme.Hom.length_stalk_fiber_asFiber_eq f _ h, Scheme.Hom.fiberHomeo_symm_fiberι,
      Scheme.Hom.residueDegree_fiberToSpecResidueField]
  rw [finsum_congr hsum]
  -- Step 3: q : F → Spec κ(y) is finite (base change of f), so Γ(F) is a finite κ(y)-algebra.
  have hq : IsFinite (f.fiberToSpecResidueField y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) inferInstance
  have hfin : ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (f.fiberToSpecResidueField y).appTop).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp (f.fiberToSpecResidueField y).finite_appTop
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hB := Scheme.Hom.finsum_length_stalk_mul_residueDegree_eq_finrank_of_isAffine
    (k := Y.residueField y) (f.fiberToSpecResidueField y) hfin
  -- Step 4: rank of the pushforward.
  have hA := Scheme.Hom.rankAtStalk_pushforward_unit_eq_finrank_fiber_sections f y
  rw [hA, ← hB]
  -- Step 5: cast to ℤ (F is finite).
  let _ : Fintype (f.fiber y) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  push_cast
  rfl

end
