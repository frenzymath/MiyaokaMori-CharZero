import MiyaokaMori.Prelude

/-! # A cancellation law in a localized monoidal category

Let `L : C ⥤ D` be a monoidal localization functor (`Localization.Monoidal`), `p : P ⟶ P'` a morphism
in `C`, `e : L P' ⟶ L P` with `L p ≫ e = 𝟙` (typically `p` is the unit of an adjunction and `e` the
counit, by a triangle identity), and `eB : L Q ≅ B` any isomorphism. Then

`L (p ⊗ 𝟙) ≫ (μ_{P',Q}⁻¹ ≫ (e ⊗ eB.hom)) ≫ ((L P ◁ eB.inv) ≫ μ_{P,Q}) = 𝟙`.

Mathlib describes `Localization.Monoidal.μ` only through its naturality, not by its values, so proofs
that need to evaluate `μ` on concrete elements get stuck. This lemma cancels a pair of `μ`'s together
with a pair of comparison isomorphisms to the identity, so that `μ` no longer appears and the rest of
the computation can be done on sections. The proof only uses the naturality of `δ` (`= μ⁻¹`) and the
functoriality of `tensorHom`. Used for the two inverse laws of the tensor–Hom adjunction (Stacks 01CM).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.Localization.Monoidal

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] (L : C ⥤ D)
  (W : MorphismProperty C) [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

/-- The cancellation law in a localized monoidal category; see the module docstring. -/
theorem map_tensorHom_id_comp_μ_cancel {P P' Q : C} (p : P ⟶ P')
    (e : (toMonoidalCategory L W ε).obj P' ⟶ (toMonoidalCategory L W ε).obj P)
    {B : LocalizedMonoidal L W ε} (eB : (toMonoidalCategory L W ε).obj Q ≅ B)
    (h : (toMonoidalCategory L W ε).map p ≫ e = 𝟙 _) :
    (toMonoidalCategory L W ε).map (p ⊗ₘ 𝟙 Q) ≫ ((μ L W ε P' Q).inv ≫ (e ⊗ₘ eB.hom)) ≫
        (((toMonoidalCategory L W ε).obj P ◁ eB.inv) ≫ (μ L W ε P Q).hom) = 𝟙 _ := by
  rw [← CategoryTheory.Localization.Monoidal.id_tensorHom]
  have hδ : ∀ X Y : C, Functor.OplaxMonoidal.δ (toMonoidalCategory L W ε) X Y = (μ L W ε X Y).inv :=
    fun _ _ => rfl
  have hnat := Functor.OplaxMonoidal.δ_natural (toMonoidalCategory L W ε) p (𝟙 Q)
  rw [hδ, hδ] at hnat
  simp only [Category.assoc]
  rw [← Category.assoc ((toMonoidalCategory L W ε).map (p ⊗ₘ 𝟙 Q)), ← hnat, Category.assoc]
  simp only [Functor.map_id, tensorHom_comp_tensorHom_assoc, h, Category.id_comp,
    Iso.hom_inv_id, Category.comp_id, id_tensorHom_id, Iso.inv_hom_id]

end CategoryTheory.Localization.Monoidal

end
