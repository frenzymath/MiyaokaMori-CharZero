import MiyaokaMori.Prelude

/-! # Lifting a section through a morphism that is an isomorphism over an open

If `β : S ⟶ W` is an isomorphism over an open `U`, a morphism `σ₀ : C ⟶ U` landing in `U` lifts to
`σ : C ⟶ S` with `σ ≫ β = σ₀ ≫ U.ι`; if moreover `Ψ : S ⟶ Y` agrees with `h ∘ β` on `β⁻¹U`, then
`σ ≫ Ψ = σ₀ ≫ h`. (Corollary 4.3 of the paper: "since `β` is an isomorphism over
`U`, the zero section lifts to a section `σ` with `Φ ∘ σ = f ∘ ρ`".)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem AlgebraicGeometry.exists_lift_of_isIso_morphismRestrict {S W C : Scheme.{u}}
    (β : S ⟶ W) (U : W.Opens) (hiso : IsIso (β ∣_ U)) (σ₀ : C ⟶ U.toScheme) :
    ∃ σ : C ⟶ S, σ ≫ β = σ₀ ≫ U.ι ∧
      ∀ {Y : Scheme.{u}} (Ψ : S ⟶ Y) (h : U.toScheme ⟶ Y),
        (β ⁻¹ᵁ U).ι ≫ Ψ = (β ∣_ U) ≫ h → σ ≫ Ψ = σ₀ ≫ h := by
  refine ⟨σ₀ ≫ inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · intro Y Ψ h hagree
    rw [Category.assoc, Category.assoc, hagree, IsIso.inv_hom_id_assoc]

end
