import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01n2
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupSpecIsoProjRees
import MiyaokaMori.RingTheory.GradedRing.ReesResidueBaseChangePolynomial

/-! # Stacks 0AGQ: the exceptional fibre of the blowup of a regular local ring of dimension two

Stacks 0AGQ(1): for a two-dimensional regular local ring `(A, 𝔪, κ)`, the exceptional (closed) fibre
of the blowup of `Spec A` along `𝔪` is isomorphic to `P¹_κ` (the paper uses this in the proof of
Lemma 5.1, §5: "the new exceptional curve is a `P¹`").

The proof assembles three inputs:
* `Scheme.blowup_spec_iso_proj_reesGrading_over`: `Bl_𝔪 Spec A ≅ Proj(⊕ 𝔪ⁿ)` over `Spec A`;
* `IsRegularLocalRing.exists_reesGrading_maximalIdeal_baseChange_residueField`:
  `(⊕ 𝔪ⁿ) ⊗_A κ ≅ κ[T₀,T₁]` in `IsBaseChange` form (a consequence of Stacks 00NO);
* `Proj.isPullback_of_isBaseChange` (Stacks 01N2): `Proj` commutes with base change, compatibly
  with `toSpecZero`.
The assembly only uses `pullback.map` (base change along the first isomorphism) and
`IsPullback.isoPullback` (the pullback square of the third item).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

/-- **Stacks 0AGQ(1), form over `κ`**: for a two-dimensional regular local ring `(A, 𝔪, κ)` and the
blowup `X = Bl_𝔪 Spec A`, the closed fibre `E = X ×_{Spec A} Spec κ` is isomorphic to `P¹_κ` **as a
`κ`-scheme**: there is `e : E ≅ P¹_κ` such that `e` composed with the structure morphism
`ProjectiveLine κ ↘ Spec κ` (`= ProjectiveSpace.toSpecBase 1 κ`
`= Proj.toSpecZero ≫ Spec.map (algebraMap κ (κ[T₀,T₁])₀)`) is the second projection
`pullback.snd : E ⟶ Spec κ` of the fibre product.

Source: Stacks 0AGQ(1); the paper uses it in the proof of Lemma 5.1 (§5).
`pointBlowup.exists_fiber_iso_projectiveLine_residueField` needs exactly this form with the
compatibility of structure morphisms; the weaker `Nonempty` form
`blowup_regularLocalRing_dimTwo_exceptional` below follows from it directly.

**Proof** (the argument of Stacks 0AGQ):
1. **`X = Proj(⊕ₙ 𝔪ⁿ)` over `Spec A`**: `Scheme.blowup_spec_iso_proj_reesGrading_over`
   (Stacks 0804 over all of `Spec A`, compatibly with the structure morphisms) gives
   `e₁ : (Bl_𝔪 Spec A).left ≅ Proj (reesGrading 𝔪)` with
   `e₁.hom ≫ toSpecZero ≫ Spec.map (algebraMap A (Rees)₀) = blowup.hom`.
   (The local statement `blowup_preimage_affine` only gives `Nonempty (b⁻¹U ≅ Proj Rees)` without
   this compatibility, which is why the stronger form is needed.)
2. **`(⊕ 𝔪ⁿ) ⊗_A κ = gr_𝔪 A ≅ κ[T₀,T₁]`**:
   `IsRegularLocalRing.exists_reesGrading_maximalIdeal_baseChange_residueField` gives a graded ring
   homomorphism `f : reesGrading 𝔪 →+*ᵍ κ[T₀,T₁]` (standard grading), the irrelevant-ideal
   condition, an `A`-algebra homomorphism `fR` and `IsBaseChange κ fR`. Its mathematical content
   is Stacks 00NO (for `𝔪 = (x, y)`, the coefficients of a homogeneous relation of degree `n` all
   lie in `𝔪`).
3. **`Proj` commutes with base change** (Stacks 01N2): from the data of step 2,
   `Proj.isPullback_of_isBaseChange` gives the pullback square
   `Proj κ[T₀,T₁] --Proj.map f--> Proj(⊕ 𝔪ⁿ)` with vertical sides
   `toSpecZero ≫ Spec.map (algebraMap κ …₀)` (definitionally `ProjectiveLine κ ↘ Spec κ`) and
   `toSpecZero ≫ Spec.map (algebraMap A …₀)`, and bottom side `Spec κ → Spec A`.
4. **Composition**: `pullback.map` along `e₁` (the equation of step 1) identifies
   `E = pullback blowup.hom (Spec.map (algebraMap A κ))` with
   `pullback (toSpecZero ≫ Spec.map …) (Spec.map (algebraMap A κ))`, and
   `IsPullback.isoPullback.symm` of the square of step 3 identifies the latter with
   `Proj κ[T₀,T₁] = P¹_κ`. Compatibility: `isoPullback_inv_snd` turns the structure morphism of
   `P¹_κ` back into `pullback.snd`, and `lift_snd` for `pullback.map` turns it back into
   `pullback.snd` of `E`.

The closed immersion `r : X → P¹_A` (Stacks 01N1) of the original argument is not needed for this
statement. Edge cases: `dim A = 2` excludes fields and the one-dimensional case; `κ` is a field
(`IsLocalRing.ResidueField`), and `P¹_κ` uses the `[Field κ]` instance;
`Spec.map (ofHom (algebraMap A κ))` and `Spec.map (IsLocalRing.residue A)` are definitionally
equal (`IsLocalRing.ResidueField.algebraMap_eq`). -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_over_residueField
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    let I : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal A).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ∃ e : CategoryTheory.Limits.pullback (AlgebraicGeometry.Scheme.blowup I).hom
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))
      ≅ ProjectiveLine (IsLocalRing.ResidueField A),
      e.hom ≫ (ProjectiveLine (IsLocalRing.ResidueField A) ↘
          AlgebraicGeometry.Spec (CommRingCat.of (IsLocalRing.ResidueField A))) =
        CategoryTheory.Limits.pullback.snd _ _ := by
  intro I
  -- Step 1: `Bl_𝔪 Spec A ≅ Proj(⊕ 𝔪ⁿ)` over `Spec A`
  obtain ⟨e₁, he₁⟩ :=
    AlgebraicGeometry.Scheme.blowup_spec_iso_proj_reesGrading_over A (IsLocalRing.maximalIdeal A)
  -- Step 2: `(⊕ 𝔪ⁿ) ⊗_A κ ≅ κ[T₀,T₁]`
  obtain ⟨f, hf, fR, hfR, hbc⟩ :=
    IsRegularLocalRing.exists_reesGrading_maximalIdeal_baseChange_residueField A 2 hdim
  -- Step 3: `Proj` commutes with base change
  have hpb := AlgebraicGeometry.Proj.isPullback_of_isBaseChange
    (Ideal.reesGrading (IsLocalRing.maximalIdeal A))
    (MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A)) f hf fR hfR hbc
  -- Step 4: base change along `e₁`
  let m := CategoryTheory.Limits.pullback.map (AlgebraicGeometry.Scheme.blowup I).hom
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))
    (AlgebraicGeometry.Proj.toSpecZero (Ideal.reesGrading (IsLocalRing.maximalIdeal A)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap A (Ideal.reesGrading (IsLocalRing.maximalIdeal A) 0))))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))
    e₁.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he₁]) (by rw [Category.comp_id, Category.id_comp])
  refine ⟨asIso m ≪≫ hpb.isoPullback.symm, ?_⟩
  change m ≫ hpb.isoPullback.inv ≫
    (AlgebraicGeometry.Proj.toSpecZero
        (MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A)
        (MvPolynomial.homogeneousSubmodule (Fin 2) (IsLocalRing.ResidueField A) 0)))) = _
  rw [hpb.isoPullback_inv_snd]
  exact (CategoryTheory.Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Stacks 0AGQ(1), weak form (an abstract isomorphism of schemes, without the compatibility with
the `κ`-structure): obtained from `blowup_regularLocalRing_dimTwo_exceptional_over_residueField`
by forgetting the compatibility equation. Used by `pointBlowup.fiber_iso_projectiveLine`. -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    let I : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal A).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    Nonempty (CategoryTheory.Limits.pullback (AlgebraicGeometry.Scheme.blowup I).hom
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A))))
      ≅ ProjectiveLine (IsLocalRing.ResidueField A)) := by
  intro I
  obtain ⟨e, -⟩ :=
    AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional_over_residueField A hdim
  exact ⟨e⟩

end
