import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter

/-! # Stalks of a point blowup away from the center

Stalk-level consequences of "the blowup is an isomorphism away from the centre" (Stacks 02OS(1)):
for `f : X ⟶ Y` and an open `U ⊆ Y` with `f ∣_ U` an isomorphism, `f` induces isomorphisms on the
stalks at the points of `f⁻¹(U)` and is injective on `f⁻¹(U)`. Specialized to the point blowup
`π : Bl_p S → S` of a smooth projective surface and `U = S ∖ {p}` (`pointBlowup_isIso_away`).

Used in the proof of Stacks 0AHH (blowing up improves the length sum; steps 5, 6: the terms of the length sum away from the
exceptional fibre are the terms of the original ideal sheaf).

Source: Stacks 02OS(1) / 0807; `Paper/S3PositiveLine/BlowupIsoAwayFromCenter.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- If `f ∣_ U` is an isomorphism, `f` induces isomorphisms on the stalks over `U`:
`(f ⁻¹ᵁ U).ι ≫ f = (f ∣_ U) ≫ U.ι` is an open immersion (`morphismRestrict_ι`), so its stalk maps
are isomorphisms, and `stalkMap_comp` splits off the stalk isomorphism of `(f ⁻¹ᵁ U).ι`. -/
theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)] (x : X) (hx : x ∈ f ⁻¹ᵁ U) : IsIso (f.stalkMap x) := by
  obtain ⟨x', rfl⟩ : x ∈ Set.range (f ⁻¹ᵁ U).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hx
  have h1 : IsIso (((f ⁻¹ᵁ U).ι ≫ f).stalkMap x') := by
    rw [← AlgebraicGeometry.morphismRestrict_ι]
    infer_instance
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (f.stalkMap ((f ⁻¹ᵁ U).ι x'))
    ((f ⁻¹ᵁ U).ι.stalkMap x') inferInstance h1

/-- If `f ∣_ U` is an isomorphism, `f` is injective on `f⁻¹(U)` (the base map of `f ∣_ U` is the
restriction of `f` to `f⁻¹(U) → U`, `morphismRestrict_base`, and it is a bijection). -/
theorem injOn_preimage_of_isIso_morphismRestrict {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)] : Set.InjOn f (f ⁻¹ᵁ U : Set X) := by
  intro x₁ hx₁ x₂ hx₂ hf
  have hinj : Function.Injective (f ∣_ U).base :=
    (AlgebraicGeometry.Scheme.Hom.isOpenEmbedding (f ∣_ U)).injective
  have h := AlgebraicGeometry.morphismRestrict_base f U
  have hx : (f ∣_ U).base ⟨x₁, hx₁⟩ = (f ∣_ U).base ⟨x₂, hx₂⟩ := by
    rw [h]
    exact Subtype.ext hf
  exact congrArg Subtype.val (hinj hx)

end AlgebraicGeometry.Scheme.Hom

/-- The point blowup `π : Bl_p S → S` induces isomorphisms on stalks away from the exceptional
fibre (`pointBlowup_isIso_away` with `U = S ∖ {p}`). -/
theorem pointBlowup.isIso_stalkMap_π_of_ne {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (y : (pointBlowup S p hp).toScheme) (hy : pointBlowup.π S p hp y ≠ p) :
    IsIso ((pointBlowup.π S p hp).stalkMap y) := by
  let U : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
  have : IsIso ((pointBlowup.π S p hp) ∣_ U) := pointBlowup_isIso_away S p hp U (fun h => h rfl)
  exact AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_morphismRestrict _ U y hy

/-- The point blowup `π : Bl_p S → S` is injective away from the exceptional fibre. -/
theorem pointBlowup.π_injOn {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    Set.InjOn (pointBlowup.π S p hp) {y | pointBlowup.π S p hp y ≠ p} := by
  let U : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
  have : IsIso ((pointBlowup.π S p hp) ∣_ U) := pointBlowup_isIso_away S p hp U (fun h => h rfl)
  exact AlgebraicGeometry.Scheme.Hom.injOn_preimage_of_isIso_morphismRestrict _ U

end
