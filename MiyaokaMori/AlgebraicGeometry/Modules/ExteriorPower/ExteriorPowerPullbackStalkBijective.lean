import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerStalkConjugacyAllSections
import MiyaokaMori.Algebra.ExteriorPowerBijectiveHelpers

/-!
# Conditional bijectivity for the exterior pullback stalk comparison

The all-sections conjugacy identifies the comparison stalk map only after it is
preceded by the actual tensor-to-pullback-stalk map.  Consequently bijectivity
of the module map and of exterior-power base change gives bijectivity of that
composite.  Bijection of the comparison stalk map itself additionally needs
surjectivity of the preceding pullback-stalk map; this file records that
condition explicitly instead of treating it as an automatic consequence of an
adjunction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

/-- Pure function-level cancellation: if `E ∘ S ∘ T ∘ B` and the three outer maps are bijective,
so is `S`. Stated on variables so that no stalk or exterior-power carrier is ever unfolded. -/
theorem bijective_of_comp₄_bijective {α β γ δ ε : Type*}
    (E : δ → ε) (S : γ → δ) (T : β → γ) (B : α → β)
    (hE : Function.Bijective E) (hT : Function.Bijective T) (hB : Function.Bijective B)
    (h : Function.Bijective (fun z ↦ E (S (T (B z))))) : Function.Bijective S := by
  have h1 : Function.Bijective (E ∘ (S ∘ (T ∘ B))) := h
  rw [Function.Bijective.of_comp_iff' hE] at h1
  exact (Function.Bijective.of_comp_iff S (hT.comp hB)).mp h1

/-- Base change of (the linear map underlying) a linear equivalence is bijective. -/
theorem linearEquiv_baseChange_bijective {R A M N : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : Function.Bijective (e.toLinearMap.baseChange A) :=
  (LinearEquiv.baseChange R A M N e).bijective


variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) (x : X)

local instance : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  modulePullbackStalkAlgebra f x

local instance (U : Y.Opensᵒᵖ) : CommRing (Y.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Y, U.unop))

/--
The all-sections conjugacy makes the *composite* stalk map bijective when the
module stalk map and the exterior-power base-change map are bijective.  The
composite is displayed explicitly because the pullback stalk map preceding the
comparison is not known to be onto from the adjunction alone.
-/
theorem moduleExteriorPullbackComparison_stalk_composite_bijective
    (hM : Function.Bijective (modulePullbackStalkTensorMap f M x))
    (hBase : Function.Bijective
      (exteriorPowerBaseChangeMap
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.stalk (f x)) n)) :
    Function.Bijective
      (fun z ↦
        moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n
          (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)
            (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x
              (((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
                (X.presheaf.stalk x)) z)))) := by
  have hMap : Function.Bijective
      (exteriorPower.map n (modulePullbackStalkTensorMap f M x)) :=
    exteriorPower_map_bijective n (modulePullbackStalkTensorMap f M x) hM
  have hRight : Function.Bijective
      (fun z ↦ exteriorPower.map n (modulePullbackStalkTensorMap f M x)
        (exteriorPowerBaseChangeMap
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
          (M.presheaf.stalk (f x)) n z)) :=
    hMap.comp hBase
  have hEq :
      (fun z ↦
        moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n
          (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)
            (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x
              (((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
                (X.presheaf.stalk x)) z)))) =
      (fun z ↦ exteriorPower.map n (modulePullbackStalkTensorMap f M x)
        (exteriorPowerBaseChangeMap
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
          (M.presheaf.stalk (f x)) n z)) := by
    funext z
    exact moduleExteriorPullbackComparison_stalk_conjugacy_all f M n x z
  rw [hEq]
  exact hRight

/--
The comparison stalk map itself is bijective under the preceding composite
hypotheses and an explicit bijectivity hypothesis for the actual pullback
stalk tensor map of the exterior-power module.  The extra hypothesis is
mathematically necessary for this conclusion and is not hidden in the
adjunction API.
-/
-- Splitting the composite with `simpa`/`rw` at the concrete level runs into coercions on the carrier of
-- the exterior power and non-beta-reduced `rw` patterns; the cancellation is therefore done at the
-- variable level in `bijective_of_comp₄_bijective`, and the concrete level is a single term application.
theorem moduleExteriorPullbackComparison_stalk_bijective_of_bijective
    (hM : Function.Bijective (modulePullbackStalkTensorMap f M x))
    (hBase : Function.Bijective
      (exteriorPowerBaseChangeMap
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.stalk (f x)) n))
    (hExt : Function.Bijective
      (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x)) :
    Function.Bijective
      (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)) :=
  bijective_of_comp₄_bijective
    (moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n)
    (moduleStalkMap X x (moduleExteriorPullbackComparison f M n))
    (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x)
    ((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
        (X.presheaf.stalk x))
    (LinearEquiv.bijective _) hExt (linearEquiv_baseChange_bijective _)
    (moduleExteriorPullbackComparison_stalk_composite_bijective f M n x hM hBase)

end AlgebraicGeometry.Scheme.Modules
