import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.NormalizationFunctionField
import MiyaokaMori.AlgebraicGeometry.Morphisms.RegularImpliesSmoothOverPerfectField
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.Stacks035l
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0ecg
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks0bx2
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOfFiniteOverProjective
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # Normalization of an integral curve

The normalization `ν_0 : C̃_0 → Γ ⊂ Y` of an integral curve `Γ`: `C̃_0` is a smooth connected
projective curve and `ν_0` is finite, surjective and birational.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An integral curve in a projective scheme over an algebraically closed field has a normalization:
a smooth projective curve with a finite surjective birational morphism onto it. -/
theorem exists_normalization_of_integralCurve {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (Γ : AlgebraicGeometry.Scheme.{u}) [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral Γ] (hproj : IsProjectiveOver k Γ) (hdim : SchemeIsOneDimensional Γ) :
    ∃ (Ct : SmoothProjectiveCurve k) (ν : Ct.toScheme ⟶ Γ),
      haveI : AlgebraicGeometry.IsIntegral Ct.toScheme := SmoothProjectiveCurve.isIntegral Ct;
      ν ≫ (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        Ct.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) ∧
      AlgebraicGeometry.IsFinite ν ∧ Function.Surjective ν.base ∧
      ∃ hν : ν.base (genericPoint Ct.toScheme) = genericPoint Γ, functionFieldDegree ν = 1 := by
  -- the relative normalization of `Γ` in its own function field `K(Γ)` (`curveFieldNormalization`,
  -- i.e. Mathlib's `(Spec K(Γ) → Γ).normalization`)
  let C := AlgebraicGeometry.Scheme.Covers.curveFieldNormalization Γ Γ.functionField
  let ν : C ⟶ Γ := AlgebraicGeometry.Scheme.Covers.curveFieldNormalizationMap Γ Γ.functionField
  have hproper : AlgebraicGeometry.IsProper (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    hproj.isProper
  have : AlgebraicGeometry.IsOfFiniteType (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := {}
  -- `ν` is finite (`K = K(Γ)`)
  have hfin : AlgebraicGeometry.IsFinite ν :=
    finite_normalization_of_curve (k := k) (Y := Γ) Γ.functionField
  -- generic point and function field degree (`K = K(Γ)`)
  obtain ⟨-, hgen, -, hdeg⟩ :=
    AlgebraicGeometry.normalization_functionField (Y := Γ) Γ.functionField
  -- `k`-structure: `ν ≫ (Γ → Spec k)`
  let : C.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨ν ≫ (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : AlgebraicGeometry.IsOfFiniteType (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsOfFiniteType (ν ≫ (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    exact { toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  have : AlgebraicGeometry.IsLocallyNoetherian C :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- dimension: `ν` integral and surjective, so `dim C = dim Γ = 1` (Stacks 0ECG)
  have hdimC : topologicalKrullDim C = 1 := by
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective ν]
    exact hdim
  -- normal (Stacks 035L: `Spec K(Γ)` normal, so the relative normalization is normal)
  have : C.IsNormal := by
    have : (AlgebraicGeometry.Spec (CommRingCat.of Γ.functionField)).IsNormal :=
      AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed _
    change (AlgebraicGeometry.Scheme.Hom.normalization
      (AlgebraicGeometry.Scheme.Covers.curveExtensionGenericMap Γ Γ.functionField)).IsNormal
    apply AlgebraicGeometry.Scheme.Hom.normalization_isNormal
  -- proper (finite implies proper; composite)
  have : AlgebraicGeometry.IsProper (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.IsProper (ν ≫ (Γ ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    infer_instance
  let Ct : SmoothProjectiveCurve k :=
    { carrier := C
      smooth := by
        apply (isSmoothOver_iff_regular C).mpr
        apply AlgebraicGeometry.Scheme.isRegular_of_isNormal_of_dim_le_one
        exact le_of_eq hdimC
      projective := by
        haveI : ν.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
        exact IsProjectiveOver.of_isFinite ν hproj
      connected := inferInstance
      dim_one := hdimC }
  refine ⟨Ct, ν, rfl, hfin, ν.surjective, hgen, ?_⟩
  exact hdeg.trans (Module.finrank_self _)

end
