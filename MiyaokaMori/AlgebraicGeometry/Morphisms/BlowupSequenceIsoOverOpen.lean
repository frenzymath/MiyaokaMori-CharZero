import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup
import MiyaokaMori.AlgebraicGeometry.Morphisms.BlowupIsoAwayFromCentre

/-! # A sequence of point blowups is an isomorphism away from the centres

A sequence `β` of point blowups whose centres all lie outside an open `U` is an isomorphism over
`U`; and "pointwise agreement on `D`" restricts to a smaller open `U ≤ D` (Corollary 4.3 of the paper; Stacks 02OS (1), by induction along the sequence).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

theorem MiyaokaMori.Statement.IsPointBlowupSequenceOver.isIso_morphismRestrict {W S : Scheme.{u}}
    (U : W.Opens) (β : S ⟶ W)
    (hβ : MiyaokaMori.Statement.IsPointBlowupSequenceOver W ((U : Set W)ᶜ) β) : IsIso (β ∣_ U) := by
  induction hβ with
  | id => infer_instance
  | cons f b prev centre closed hallowed hblow ih =>
    have h1 : IsIso (b ∣_ (f ⁻¹ᵁ U)) :=
      MiyaokaMori.Statement.IsBlowup.isIso_morphismRestrict_pointIdeal centre b hblow (f ⁻¹ᵁ U)
        (fun hmem => hallowed hmem)
    have h2 : IsIso (f ∣_ U) := ih
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

theorem AlgebraicGeometry.morphismRestrict_agree_of_le {S W Y : Scheme.{u}} (β : S ⟶ W)
    (D U : W.Opens) (hU : U ≤ D) (Ψ : S ⟶ Y) (h : D.toScheme ⟶ Y)
    (hagree : (β ⁻¹ᵁ D).ι ≫ Ψ = (β ∣_ D) ≫ h) :
    (β ⁻¹ᵁ U).ι ≫ Ψ = (β ∣_ U) ≫ W.homOfLE hU ≫ h := by
  have hle : β ⁻¹ᵁ U ≤ β ⁻¹ᵁ D := fun x hx => hU hx
  have key : S.homOfLE hle ≫ (β ∣_ D) = (β ∣_ U) ≫ W.homOfLE hU := by
    rw [← cancel_mono D.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
  calc (β ⁻¹ᵁ U).ι ≫ Ψ = S.homOfLE hle ≫ (β ⁻¹ᵁ D).ι ≫ Ψ := by rw [Scheme.homOfLE_ι_assoc]
    _ = S.homOfLE hle ≫ (β ∣_ D) ≫ h := by rw [hagree]
    _ = (β ∣_ U) ≫ W.homOfLE hU ≫ h := by rw [← Category.assoc, key, Category.assoc]

end
