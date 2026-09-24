import MiyaokaMori.Prelude

/-! # Products of two multiplications in a braided category

`C` braided monoidal. For `f : X₁ ⊗ Y₁ ⟶ Z₁` and `g : X₂ ⊗ Y₂ ⟶ Z₂` the **pair multiplication** is
`pairMul f g := tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ g) : (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ⟶ Z₁ ⊗ Z₂`
(the multiplication of the tensor product of two monoids, Mathlib `Mon_.tensorObj`).

If moreover a binary operation `t : C → C → C` on objects comes with comparison isomorphisms
`τ X Y : t X Y ≅ X ⊗ Y` (for us `t = Modules.tensor`, `τ = tensorIsoTensorObj`), the **conjugated** version is
`combMul τ f g := ((τ _ _).hom ⊗ (τ _ _).hom) ≫ pairMul f g ≫ (τ _ _).inv : t X₁ X₂ ⊗ t Y₁ Y₂ ⟶ t Z₁ Z₂`;
this is the shape of `twistPullbackMul` (`Paper/S2WeightedJets/CoordinatePowerNonzeroLocus_SplitTwistMulAdd_TwistPullbackPow.lean`).

Results (pure coherence: `tensorμ_natural_left/right`, `tensor_right_unitality`, `tensor_associativity`):
* `pairMul_unit_right` / `combMul_unit_right`: componentwise right unit laws give the right unit law of the product;
* `pairMul_assoc_step` / `combMul_assoc_step`: componentwise associativity steps
  `(X ◁ f) ≫ f' = α⁻¹ ≫ (f'' ▷ W) ≫ f'''` give the associativity step of the product.

Source: standard (tensor product of monoids in a braided category); modelled on
`IsGradedMonoid.tensor` (`MiyaokaMori.Algebra.GradedMonoidTensor`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace MiyaokaMori

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- `tensorμ ≫ (f ⊗ g)`. -/
noncomputable def pairMul {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) :
    (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ⟶ Z₁ ⊗ Z₂ :=
  tensorμ X₁ X₂ Y₁ Y₂ ≫ (f ⊗ₘ g)

/-- Right unit law of the pair multiplication from the componentwise ones. -/
theorem pairMul_unit_right {X₁ X₂ U₁ U₂ : C} (u₁ : 𝟙_ C ⟶ U₁) (u₂ : 𝟙_ C ⟶ U₂)
    (f : X₁ ⊗ U₁ ⟶ X₁) (g : X₂ ⊗ U₂ ⟶ X₂)
    (h₁ : (X₁ ◁ u₁) ≫ f = (ρ_ X₁).hom) (h₂ : (X₂ ◁ u₂) ≫ g = (ρ_ X₂).hom) :
    ((X₁ ⊗ X₂) ◁ ((λ_ (𝟙_ C)).inv ≫ (u₁ ⊗ₘ u₂))) ≫ pairMul f g = (ρ_ (X₁ ⊗ X₂)).hom := by
  unfold pairMul
  rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, h₁, h₂,
    tensor_right_unitality]

/-- `tensor_associativity` solved for `(_ ◁ tensorμ) ≫ tensorμ`. -/
theorem tensor_associativity' (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) :
    ((X₁ ⊗ X₂) ◁ tensorμ Y₁ Y₂ Z₁ Z₂) ≫ tensorμ X₁ X₂ (Y₁ ⊗ Z₁) (Y₂ ⊗ Z₂) =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (Z₁ ⊗ Z₂)).inv ≫ (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ ⊗ Z₂)) ≫
        tensorμ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) Z₁ Z₂ ≫ ((α_ X₁ Y₁ Z₁).hom ⊗ₘ (α_ X₂ Y₂ Z₂).hom) := by
  rw [tensor_associativity, Iso.inv_hom_id_assoc]

/-- Associativity step of the pair multiplication from the componentwise ones. -/
theorem pairMul_assoc_step {X₁ Y₁ W₁ V₁ S₁ Z₁ X₂ Y₂ W₂ V₂ S₂ Z₂ : C}
    (f : Y₁ ⊗ W₁ ⟶ V₁) (f' : X₁ ⊗ V₁ ⟶ Z₁) (f'' : X₁ ⊗ Y₁ ⟶ S₁) (f''' : S₁ ⊗ W₁ ⟶ Z₁)
    (g : Y₂ ⊗ W₂ ⟶ V₂) (g' : X₂ ⊗ V₂ ⟶ Z₂) (g'' : X₂ ⊗ Y₂ ⟶ S₂) (g''' : S₂ ⊗ W₂ ⟶ Z₂)
    (h₁ : (X₁ ◁ f) ≫ f' = (α_ X₁ Y₁ W₁).inv ≫ (f'' ▷ W₁) ≫ f''')
    (h₂ : (X₂ ◁ g) ≫ g' = (α_ X₂ Y₂ W₂).inv ≫ (g'' ▷ W₂) ≫ g''') :
    ((X₁ ⊗ X₂) ◁ pairMul f g) ≫ pairMul f' g' =
      (α_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (W₁ ⊗ W₂)).inv ≫ (pairMul f'' g'' ▷ (W₁ ⊗ W₂)) ≫ pairMul f''' g''' := by
  unfold pairMul
  rw [whiskerLeft_comp, Category.assoc, tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, h₁, h₂,
    ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, comp_whiskerRight]
  simp only [Category.assoc]
  rw [tensorμ_natural_left_assoc, reassoc_of% tensor_associativity']
  simp only [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_assoc]

section Comb

variable {t : C → C → C} (τ : ∀ X Y : C, t X Y ≅ X ⊗ Y)

/-- `pairMul f g` conjugated by the comparison isomorphisms `τ`. -/
noncomputable def combMul {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂) :
    t X₁ X₂ ⊗ t Y₁ Y₂ ⟶ t Z₁ Z₂ :=
  ((τ X₁ X₂).hom ⊗ₘ (τ Y₁ Y₂).hom) ≫ pairMul f g ≫ (τ Z₁ Z₂).inv

/-- Right unit law of `combMul` from the componentwise ones; the unit is `(λ_ 𝟙_).inv ≫ (u₁ ⊗ u₂) ≫ τ⁻¹`. -/
theorem combMul_unit_right {X₁ X₂ U₁ U₂ : C} (u₁ : 𝟙_ C ⟶ U₁) (u₂ : 𝟙_ C ⟶ U₂)
    (f : X₁ ⊗ U₁ ⟶ X₁) (g : X₂ ⊗ U₂ ⟶ X₂)
    (h₁ : (X₁ ◁ u₁) ≫ f = (ρ_ X₁).hom) (h₂ : (X₂ ◁ u₂) ≫ g = (ρ_ X₂).hom) :
    (t X₁ X₂ ◁ ((λ_ (𝟙_ C)).inv ≫ (u₁ ⊗ₘ u₂) ≫ (τ U₁ U₂).inv)) ≫ combMul τ f g = (ρ_ (t X₁ X₂)).hom := by
  unfold combMul
  rw [tensorHom_def (τ X₁ X₂).hom (τ U₁ U₂).hom]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (pairMul_unit_right u₁ u₂ f g h₁ h₂), rightUnitor_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Associativity step of `combMul` from the componentwise ones. -/
theorem combMul_assoc_step {X₁ Y₁ W₁ V₁ S₁ Z₁ X₂ Y₂ W₂ V₂ S₂ Z₂ : C}
    (f : Y₁ ⊗ W₁ ⟶ V₁) (f' : X₁ ⊗ V₁ ⟶ Z₁) (f'' : X₁ ⊗ Y₁ ⟶ S₁) (f''' : S₁ ⊗ W₁ ⟶ Z₁)
    (g : Y₂ ⊗ W₂ ⟶ V₂) (g' : X₂ ⊗ V₂ ⟶ Z₂) (g'' : X₂ ⊗ Y₂ ⟶ S₂) (g''' : S₂ ⊗ W₂ ⟶ Z₂)
    (h₁ : (X₁ ◁ f) ≫ f' = (α_ X₁ Y₁ W₁).inv ≫ (f'' ▷ W₁) ≫ f''')
    (h₂ : (X₂ ◁ g) ≫ g' = (α_ X₂ Y₂ W₂).inv ≫ (g'' ▷ W₂) ≫ g''') :
    (t X₁ X₂ ◁ combMul τ f g) ≫ combMul τ f' g' =
      (α_ (t X₁ X₂) (t Y₁ Y₂) (t W₁ W₂)).inv ≫ (combMul τ f'' g'' ▷ t W₁ W₂) ≫ combMul τ f''' g''' := by
  unfold combMul
  have key := pairMul_assoc_step f f' f'' f''' g g' g'' g''' h₁ h₂
  rw [tensorHom_def (τ X₁ X₂).hom (τ V₁ V₂).hom, tensorHom_def (τ S₁ S₂).hom (τ W₁ W₂).hom]
  simp only [Category.assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp]
  rw [reassoc_of% key, ← reassoc_of% (tensorHom_def (τ X₁ X₂).hom ((τ Y₁ Y₂).hom ⊗ₘ (τ W₁ W₂).hom)),
    ← whisker_exchange_assoc, ← reassoc_of% (tensorHom_def ((τ X₁ X₂).hom ⊗ₘ (τ Y₁ Y₂).hom) (τ W₁ W₂).hom),
    associator_inv_naturality_assoc]

/-- Post-composing `combMul` with a conjugated tensor of morphisms absorbs it into the components. -/
theorem combMul_comp_conj {X₁ Y₁ Z₁ Z₁' X₂ Y₂ Z₂ Z₂' : C} (f : X₁ ⊗ Y₁ ⟶ Z₁) (g : X₂ ⊗ Y₂ ⟶ Z₂)
    (x : Z₁ ⟶ Z₁') (y : Z₂ ⟶ Z₂') :
    combMul τ f g ≫ ((τ Z₁ Z₂).hom ≫ (x ⊗ₘ y) ≫ (τ Z₁' Z₂').inv) = combMul τ (f ≫ x) (g ≫ y) := by
  unfold combMul pairMul
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

/-- The associativity step of `combMul` in the shape of `twistPullbackMul_assoc`: with `tensorMapHom f g` spelled
`τ ≫ (f ⊗ g) ≫ τ⁻¹` and `tensorAssocIso` spelled `τ ≫ (τ ▷ _) ≫ α ≫ (_ ◁ τ⁻¹) ≫ τ⁻¹`, the componentwise steps
`h₁ h₂` (with the index/associator transports `x`, `y` on the left-hand factors) give
`tensorMapHom (τ ≫ combMul f'' g'') 𝟙 ≫ τ ≫ combMul f''' g''' =
 tensorAssocIso ≫ tensorMapHom 𝟙 (τ ≫ combMul f g) ≫ τ ≫ combMul f' g' ≫ tensorMapHom x y`. -/
theorem combMul_assoc_conj {X₁ Y₁ W₁ V₁ S₁ Z₁ Z₁' X₂ Y₂ W₂ V₂ S₂ Z₂ Z₂' : C}
    (f : Y₁ ⊗ W₁ ⟶ V₁) (f' : X₁ ⊗ V₁ ⟶ Z₁') (f'' : X₁ ⊗ Y₁ ⟶ S₁) (f''' : S₁ ⊗ W₁ ⟶ Z₁) (x : Z₁' ⟶ Z₁)
    (g : Y₂ ⊗ W₂ ⟶ V₂) (g' : X₂ ⊗ V₂ ⟶ Z₂') (g'' : X₂ ⊗ Y₂ ⟶ S₂) (g''' : S₂ ⊗ W₂ ⟶ Z₂) (y : Z₂' ⟶ Z₂)
    (h₁ : (X₁ ◁ f) ≫ f' ≫ x = (α_ X₁ Y₁ W₁).inv ≫ (f'' ▷ W₁) ≫ f''')
    (h₂ : (X₂ ◁ g) ≫ g' ≫ y = (α_ X₂ Y₂ W₂).inv ≫ (g'' ▷ W₂) ≫ g''') :
    ((τ (t (t X₁ X₂) (t Y₁ Y₂)) (t W₁ W₂)).hom ≫
        (((τ (t X₁ X₂) (t Y₁ Y₂)).hom ≫ combMul τ f'' g'') ⊗ₘ 𝟙 (t W₁ W₂)) ≫ (τ (t S₁ S₂) (t W₁ W₂)).inv) ≫
      (τ (t S₁ S₂) (t W₁ W₂)).hom ≫ combMul τ f''' g''' =
    ((τ (t (t X₁ X₂) (t Y₁ Y₂)) (t W₁ W₂)).hom ≫ ((τ (t X₁ X₂) (t Y₁ Y₂)).hom ▷ t W₁ W₂) ≫
        (α_ (t X₁ X₂) (t Y₁ Y₂) (t W₁ W₂)).hom ≫ (t X₁ X₂ ◁ (τ (t Y₁ Y₂) (t W₁ W₂)).inv) ≫
        (τ (t X₁ X₂) (t (t Y₁ Y₂) (t W₁ W₂))).inv) ≫
      ((τ (t X₁ X₂) (t (t Y₁ Y₂) (t W₁ W₂))).hom ≫
        (𝟙 (t X₁ X₂) ⊗ₘ ((τ (t Y₁ Y₂) (t W₁ W₂)).hom ≫ combMul τ f g)) ≫ (τ (t X₁ X₂) (t V₁ V₂)).inv) ≫
      ((τ (t X₁ X₂) (t V₁ V₂)).hom ≫ combMul τ f' g') ≫
      ((τ Z₁' Z₂').hom ≫ (x ⊗ₘ y) ≫ (τ Z₁ Z₂).inv) := by
  have step := combMul_assoc_step τ f (f' ≫ x) f'' f''' g (g' ≫ y) g'' g''' h₁ h₂
  rw [Iso.eq_inv_comp] at step
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_id, id_tensorHom, comp_whiskerRight, whiskerLeft_comp,
    whiskerLeft_inv_hom_assoc]
  rw [combMul_comp_conj, ← step]

end Comb

end MiyaokaMori
