import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfFiniteOverProjective
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationFunctionField
import MiyaokaMori.AlgebraicGeometry.Morphisms.RegularImpliesSmoothOverPerfectField
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.Stacks035l
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0ecg
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks0bx2

/-! # Normalization of a curve in a finite extension of its function field

`C̃_1 :=` the normalization of `C̃_0` in a finite field extension `K'/k(C̃_0)` is a smooth connected
projective curve, the morphism to `C̃_0` is a finite cover, and `K(C̃_1) ≅ K'` compatibly with `η`
(pulling back functions along `η` corresponds to the `k(C̃_0)`-algebra structure of `K'`). This is
the step "take a further finite extension … its normalization" of the paper (§3).

Proof sketch (the same as `exists_normalization_of_integralCurve`, the case `K = K(Γ)`, with an
arbitrary finite extension `K'` and the compatibility of the function field isomorphism with `η^*`):
1. `C := (Spec K' → C̃₀).normalization` (`AlgebraicGeometry.Scheme.Covers.curveFieldNormalization`),
   `ν := fromNormalization`; `ν` is finite (`finite_normalization_of_curve`).
2. `C` is integral and `ν` sends the generic point to the generic point (`normalization_functionField`).
3. `dim C = dim C̃₀ = 1` (`ν` integral and surjective, Stacks 0ECG); `C` is normal (Stacks 035L,
   `Spec K'` is normal); Noetherian normal of dimension one implies regular (Stacks 0BX2), hence
   smooth over the perfect field `k` (`isSmoothOver_iff_regular`).
4. Projective: a finite morphism to a projective scheme has projective source
   (`IsProjectiveOver.of_isFinite`, Stacks 0B3I/0892).
5. `ν` integral and dominant implies surjective (`curveFieldNormalizationMap_surjective`); package
   as a `FiniteCover`.
6. `K(C) ≃+* K'`: `curveFieldNormalizationFunctionFieldEquiv` is `K(C) ≃ₐ[K(C̃₀)] K'`, where the
   scalar structure on `K(C)` is given by the stalk map `dominantFunctionFieldMap ν` at the generic
   point; `pullbackFunction ν` is by definition this stalk map when `ν` is dominant
   (`pullbackFunctionHom_apply`), so the compatibility `e (ν^* ψ) = algebraMap ψ` is `AlgEquiv.commutes`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The normalization of a smooth projective curve in a finite extension `K'` of its function field
is a finite cover whose function field is `K'`, compatibly with pullback of functions. -/
theorem exists_normalization_in_extension {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (Ct₀ : SmoothProjectiveCurve k) (K' : Type u) [Field K'] [Algebra Ct₀.toScheme.functionField K']
    [Module.Finite Ct₀.toScheme.functionField K'] :
    ∃ (Ct₁ : SmoothProjectiveCurve k) (η : FiniteCover k Ct₀) (_ : η.source = Ct₁)
      (e : η.source.toScheme.functionField ≃+* K'),
      ∀ ψ : Ct₀.toScheme.functionField,
        e (pullbackFunction η.hom ψ) = algebraMap Ct₀.toScheme.functionField K' ψ := by
  -- Step 1: the relative normalization of `Y := C̃₀` in `Spec K'` (`curveFieldNormalization`,
  -- i.e. Mathlib's `(Spec K' → Y).normalization`), with its integral projection `ν`.
  let Y := Ct₀.toScheme
  let C := AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Y K'
  let ν : C ⟶ Y := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Y K'
  have hproper : AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    Ct₀.isProper
  have : AlgebraicGeometry.IsOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := {}
  -- Step 2: `ν` is finite.
  have hfin : AlgebraicGeometry.IsFinite ν :=
    finite_normalization_of_curve (k := k) (Y := Y) K'
  -- Step 3: `C` is integral, generic point maps to generic point.
  obtain ⟨-, hgen, -, -⟩ := AlgebraicGeometry.normalization_functionField (Y := Y) K'
  -- `k`-structure on `C`: `ν ≫ (Y → Spec k)`.
  let : C.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨ν ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : AlgebraicGeometry.IsOfFiniteType (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsOfFiniteType (ν ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    exact { toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  have : AlgebraicGeometry.IsLocallyNoetherian C :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- Step 4: dimension: `ν` integral and surjective ⇒ `dim C = dim Y = 1` (Stacks 0ECG).
  have hdimC : topologicalKrullDim C = 1 := by
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective ν]
    exact Ct₀.dim_one
  -- Step 5: normal (Stacks 035L: `Spec K'` normal ⇒ the relative normalization is normal).
  have : C.IsNormal := by
    have : (AlgebraicGeometry.Spec (CommRingCat.of K')).IsNormal :=
      AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed _
    change (AlgebraicGeometry.Scheme.Hom.normalization
      (AlgebraicGeometry.Scheme.Covers.curveExtensionGenericMap Y K')).IsNormal
    apply AlgebraicGeometry.Scheme.Hom.normalization_isNormal
  -- Step 6: proper over `k` (finite ⇒ proper; composition).
  have : AlgebraicGeometry.IsProper (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsProper (ν ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    infer_instance
  -- Package `C̃₁`: normal + Noetherian + dim 1 ⇒ regular (0BX2) ⇒ smooth over the perfect field `k`;
  -- finite over projective ⇒ projective; integral ⇒ connected.
  let Ct : SmoothProjectiveCurve k :=
    { carrier := C
      smooth := by
        apply (isSmoothOver_iff_regular C).mpr
        apply AlgebraicGeometry.Scheme.isRegular_of_isNormal_of_dim_le_one
        exact le_of_eq hdimC
      projective := by
        have : ν.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
        exact IsProjectiveOver.of_isFinite ν Ct₀.projective
      connected := inferInstance
      dim_one := hdimC }
  -- Step 7: `ν` finite and surjective (integral + dominant) ⇒ a `FiniteCover`.
  let η : FiniteCover k Ct₀ :=
    { source := Ct
      hom := ν
      isOver := rfl
      finite := hfin
      surjective := inferInstance }
  -- The function field of `C̃₁` is `K'`, compatibly with `ν^*`
  -- (`curveFieldNormalizationFunctionFieldEquiv`, an algebra equivalence over `K(C̃₀)` for the
  -- scalar structure induced by `ν`, which is exactly `pullbackFunction ν`).
  let := AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ν
  let e := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationFunctionFieldEquiv Y K'
  refine ⟨Ct, η, rfl, e.toRingEquiv, fun ψ => ?_⟩
  change e (pullbackFunction ν ψ) = algebraMap Y.functionField K' ψ
  rw [← pullbackFunctionHom_apply ν hgen ψ]
  exact e.commutes ψ

end
