import MiyaokaMori.Prelude

/-! # Morphisms from a reduced scheme compatible with the base on a dense open

A morphism `Ψ : S → Y` from a reduced scheme `S` which is compatible with the (separated) base `B` on a
dense open `V` is a `B`-morphism.

References: Hartshorne II, Exercise 4.2 (two morphisms from a reduced scheme to a separated scheme that
agree on a dense open are equal); Mathlib's `ext_of_isDominant_of_isSeparated`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- If the two morphisms `Ψ ≫ (Y ↘ B)`, `(S ↘ B) : S → B` agree on a dense open `V` (`h`), `S` is
reduced and `B` is separated (absolutely, i.e. `terminal.from B` is separated; automatic for
`B = Spec k`), then they are equal, i.e. `Ψ` is a `B`-morphism.

Proof (Mathlib's version of Hartshorne II, Exercise 4.2): `V.ι` is dominant (`IsDominant`), since its
image `Set.range V.ι = V` (`Scheme.Opens.range_ι`) is dense in `S` (`hV`). Apply
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated` to `s := terminal.from B` (separated by
`[B.IsSeparated]`): both morphisms composed with `s` are `terminal.from S` (`terminal.hom_ext`), and they
agree after the dominant `V.ι` (`h`), hence they are equal. -/
theorem AlgebraicGeometry.Scheme.Hom.isOver_of_agree_on_dense {S Y B : Scheme.{u}} [S.Over B]
    [Y.Over B] [IsReduced S] [B.IsSeparated] (Ψ : S ⟶ Y) (V : S.Opens) (hV : Dense (V : Set S))
    (h : V.ι ≫ Ψ ≫ (Y ↘ B) = V.ι ≫ (S ↘ B)) : Ψ.IsOver B := by
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hV⟩
  exact ⟨ext_of_isDominant_of_isSeparated (terminal.from B) (terminal.hom_ext _ _) V.ι h⟩

/-- Auxiliary: if `Ψ` agrees with `(β ∣_ U) ≫ homOfLE ≫ h` on `β⁻¹U`, and `h` and `β` are both
`B`-morphisms, then `Ψ` is compatible with the base on `β⁻¹U`. -/
theorem AlgebraicGeometry.Scheme.Hom.comp_over_of_agree {S W X B : Scheme.{u}} [S.Over B] [W.Over B]
    [X.Over B] (β : S ⟶ W) [β.IsOver B] (U D : W.Opens) (hUD : U ≤ D) (Ψ : S ⟶ X)
    (h : D.toScheme ⟶ X) (hh : h ≫ (X ↘ B) = D.ι ≫ (W ↘ B))
    (hagree : (β ⁻¹ᵁ U).ι ≫ Ψ = (β ∣_ U) ≫ W.homOfLE hUD ≫ h) :
    (β ⁻¹ᵁ U).ι ≫ Ψ ≫ (X ↘ B) = (β ⁻¹ᵁ U).ι ≫ (S ↘ B) := by
  rw [← Category.assoc, hagree]
  simp only [Category.assoc]
  rw [hh, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc, CategoryTheory.comp_over]

end
