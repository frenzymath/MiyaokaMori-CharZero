import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison

/-! # The pointwise value of the twist comparison morphism

Let `f : 𝒜 → ℬ` be a graded ring homomorphism with `ℬ₊ ⊆ f(𝒜₊)ℬ`. The comparison morphism
`O_{Proj 𝒜}(n) → (Proj.map f)_* O_{Proj ℬ}(n)` (`Proj.twistToPushforward`) sends a section `s` over an open `U`
(a function with values in the localizations `A_x`) to the function `y ↦ (A_{f⁻¹y} → B_y)(s(f⁻¹y))`, i.e. to the
value at `y` of `Proj.twistComapFun f hf U (Proj.map f ⁻¹ U) s`, where `A_{f⁻¹y} → B_y` is
`Localization.localRingHom`.

Proof:
1. `(Proj.twistToPushforward).val.app U` is by definition `ModuleCat.ofHom` with `toFun`
   `s ↦ ⟨twistComapFun f hf U _ _ s.1, _⟩`.
2. `Scheme.Modules.Hom.app` is `forget₂ (ModuleCat → Ab)` applied to `val.app`, which does not change the underlying
   function; taking `.1` on both sides and evaluating at `y` gives a definitional equality (`rfl`).
3. `twistComapFun` is by definition `Localization.localRingHom (comap f y) y f rfl (s ⟨comap f y, _⟩)`, which gives the
   second form (`rfl`).

Source: the pointwise description of `θ` in Stacks 01MX.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The pointwise value of the comparison morphism on sections (in terms of `twistComapFun`). -/
theorem AlgebraicGeometry.Proj.twistToPushforward_app_apply
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U)
    (y : ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens)) :
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ n
        ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U) from
      ((AlgebraicGeometry.Proj.twistToPushforward f hf n).app U).hom s).1 y =
      AlgebraicGeometry.Proj.twistComapFun f hf U ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U)
        (fun _ h ↦ h) s.1 y :=
  rfl

end
