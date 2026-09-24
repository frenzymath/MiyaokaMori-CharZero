import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportShape
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplicationLocalAgreeAux
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear

/-! # The transport shape and pulled-back multiplications (variable level)

Helper module for the dictionary leaf (D-μ) `LiftData.twistTransport_twistMulHom`
(`RelativeProjLiftEvaluationTwistFamilyTransport.lean`).
Setting: a commutative square `j ≫ τ = φ ≫ ρ` (`j : V ⟶ T` an open immersion), modules `N₁ N₂ N₃` on `P`,
`G₁ G₂ G₃` on `Q`, chart isomorphisms `cₖ : ρ^*Nₖ ≅ Gₖ`, multiplications `m : N₁ ⊗ N₂ ⟶ N₃`, `m' : G₁ ⊗ G₂ ⟶ G₃`,
and the *pulled-back multiplications* `f^♯m := δ_f⁻¹ ≫ f^*m : f^*N₁ ⊗ f^*N₂ ⟶ f^*N₃` (`δ_f = pullbackTensorObjHom f`, the
oplax structure of `pullback f`). **If the chart identity `ρ^♯m ≫ c₃ = (c₁ ⊗ c₂) ≫ m'` holds, then the transport
shapes `Θₖ := transportIsoShape … cₖ` carry `τ^♯m` to `φ^♯m'`**:
`Θ₃(τ^♯m (x ⊗ y)) = φ^♯m' (Θ₁ x ⊗ Θ₂ y)` on sections (`transportIsoShape_hom_app_mul`).

The proof is the monoidal pseudofunctoriality of `pullback`: `pullbackComp` is compatible with `δ`
(`pullbackComp_hom_app_pullbackTensorObjHom`), `pullbackCongr` trivially so,
`δ` is natural (Mathlib `Functor.OplaxMonoidal.δ_natural`), and `restrictFunctorIsoPullback` enters only through
pulled-back sections (`restrictFunctorIsoPullback_hom_app_apply`, `pullbackTensorObjHom_app_pullbackSectionsOn`).
Everything is at the variable level, so the concrete statement is a first-order instance.

Sources: Stacks 01NR, 01MO (the multiplications); the rest is formal. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section Delta

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- `pullbackCongr` is compatible with the comparison maps `δ` (both are the identity after `subst`). -/
theorem pullbackCongr_hom_app_pullbackTensorObjHom {f f' : X ⟶ Y} (e : f = f') (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr e).hom.app (M ⊗ N) ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f' M N =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M N ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackCongr e).hom.app M ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullbackCongr e).hom.app N) := by
  subst e
  have h : ∀ K : Y.Modules, (AlgebraicGeometry.Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app K = 𝟙 _ := by
    intro K
    unfold AlgebraicGeometry.Scheme.Modules.pullbackCongr
    rw [eqToIso.hom, eqToHom_refl, NatTrans.id_app]
  rw [h, h, h, Category.id_comp, MonoidalCategory.id_tensorHom_id, Category.comp_id]

/-- The inverse form of `pullbackComp_hom_app_pullbackTensorObjHom`:
`(pullbackComp f g)⁻¹ ≫ f^*δ_g ≫ δ_f = δ_{f ≫ g} ≫ ((pullbackComp f g)⁻¹ ⊗ (pullbackComp f g)⁻¹)`. -/
theorem pullbackComp_inv_app_pullbackTensorObjHom {Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app (M ⊗ N) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N) ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (f ≫ g) M N ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app N) := by
  have T := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackTensorObjHom f g M N
  have e1 : (AlgebraicGeometry.Scheme.Modules.pullback f).map (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom g M N) ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N) =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app (M ⊗ N) ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (f ≫ g) M N ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app N) := by
    rw [← Category.assoc, T]
    simp only [Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
    erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]
  rw [e1, Iso.inv_hom_id_app_assoc]

end Delta

section Transport

variable {V T P Q : AlgebraicGeometry.Scheme.{u}} (j : V ⟶ T) [AlgebraicGeometry.IsOpenImmersion j] (τ : T ⟶ P)
  (φ : V ⟶ Q) (ρ : Q ⟶ P) (hτ : j ≫ τ = φ ≫ ρ)

/-- The pullback-side part `Θ'` of the transport shape: `j^*τ^*N ⟶ φ^*G`. -/
def transportCore (N : P.Modules) (G : Q.Modules) (c : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N ≅ G) :
    (AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback φ).obj G :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app N ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app N ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app N ≫
    (AlgebraicGeometry.Scheme.Modules.pullback φ).map c.hom

/-- `Θ = rFIP ≫ Θ'`. -/
theorem transportIsoShape_hom_eq (N : P.Modules) (G : Q.Modules)
    (c : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N ≅ G) :
    (AlgebraicGeometry.Scheme.Modules.transportIsoShape j τ φ ρ hτ N G c).hom =
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).hom.app
          ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N) ≫
        AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N G c := by
  unfold AlgebraicGeometry.Scheme.Modules.transportIsoShape AlgebraicGeometry.Scheme.Modules.transportCore
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_hom, Iso.app_hom, Iso.app_inv]

omit [AlgebraicGeometry.IsOpenImmersion j] in
/-- **The core of the transport shape carries `τ^♯m` to `φ^♯m'`** (morphism level), given the chart identity
`ρ^♯m ≫ c₃ = (c₁ ⊗ c₂) ≫ m'`. Proof: naturality of `pullbackComp`, `pullbackCongr`, `pullbackComp⁻¹` moves `m`
to the right, the chart identity replaces `ρ^*m ≫ c₃`, then the `δ`-compatibilities (`pullbackComp_hom_app_pullbackTensorObjHom`
twice, `pullbackCongr_hom_app_pullbackTensorObjHom`, `δ_natural`) collapse everything to `δ_j ≫ (Θ'₁ ⊗ Θ'₂)`. -/
theorem transportCore_mul (N₁ N₂ N₃ : P.Modules) (G₁ G₂ G₃ : Q.Modules)
    (c₁ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₁ ≅ G₁)
    (c₂ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₂ ≅ G₂)
    (c₃ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₃ ≅ G₃)
    (m : N₁ ⊗ N₂ ⟶ N₃) (m' : G₁ ⊗ G₂ ⟶ G₃)
    (hchart : CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ N₁ N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ρ).map m ≫ c₃.hom = (c₁.hom ⊗ₘ c₂.hom) ≫ m') :
    (AlgebraicGeometry.Scheme.Modules.pullback j).map
        (CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom τ N₁ N₂) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback τ).map m) ≫
        AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₃ G₃ c₃ =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom j
          ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₁) ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₁ G₁ c₁ ⊗ₘ
          AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₂ G₂ c₂) ≫
        CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom φ G₁ G₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback φ).map m' := by
  have hchart' : (AlgebraicGeometry.Scheme.Modules.pullback ρ).map m ≫ c₃.hom =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ N₁ N₂ ≫ (c₁.hom ⊗ₘ c₂.hom) ≫ m' := by
    rw [← hchart, IsIso.hom_inv_id_assoc]
  -- naturality of the three comparison isomorphisms in `m`
  have n1 : (AlgebraicGeometry.Scheme.Modules.pullback j).map ((AlgebraicGeometry.Scheme.Modules.pullback τ).map m) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app N₃ =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app (N₁ ⊗ N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ τ)).map m :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.naturality m
  have n2 : (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ τ)).map m ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app N₃ =
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app (N₁ ⊗ N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (φ ≫ ρ)).map m :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.naturality m
  have n3 : (AlgebraicGeometry.Scheme.Modules.pullback (φ ≫ ρ)).map m ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app N₃ =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app (N₁ ⊗ N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback φ).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map m) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.naturality m
  -- δ-compatibilities
  have d1 := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackTensorObjHom j τ N₁ N₂
  have d2 := AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackTensorObjHom hτ N₁ N₂
  have d3 := AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackTensorObjHom φ ρ N₁ N₂
  have d4 : (AlgebraicGeometry.Scheme.Modules.pullback φ).map (c₁.hom ⊗ₘ c₂.hom) ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom φ G₁ G₂ =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom φ
          ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₁) ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₂) ≫
        ((AlgebraicGeometry.Scheme.Modules.pullback φ).map c₁.hom ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullback φ).map c₂.hom) := by
    rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_eq_δ, AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_eq_δ]
    exact (Functor.OplaxMonoidal.δ_natural (AlgebraicGeometry.Scheme.Modules.pullback φ) c₁.hom c₂.hom).symm
  -- the key identity, with `δ_φ` on the right
  have key : (AlgebraicGeometry.Scheme.Modules.pullback j).map
        (CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom τ N₁ N₂)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app (N₁ ⊗ N₂) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app (N₁ ⊗ N₂) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app (N₁ ⊗ N₂) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback φ).map (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ N₁ N₂) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback φ).map (c₁.hom ⊗ₘ c₂.hom) ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom φ G₁ G₂ =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom j
          ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₁) ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₂) ≫
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app N₁ ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app N₁ ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app N₁ ≫
            (AlgebraicGeometry.Scheme.Modules.pullback φ).map c₁.hom) ⊗ₘ
          ((AlgebraicGeometry.Scheme.Modules.pullbackComp j τ).hom.app N₂ ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackCongr hτ).hom.app N₂ ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackComp φ ρ).inv.app N₂ ≫
            (AlgebraicGeometry.Scheme.Modules.pullback φ).map c₂.hom)) := by
    slice_lhs 6 7 => rw [d4]
    slice_lhs 4 6 => rw [d3]
    slice_lhs 3 4 => rw [d2]
    slice_lhs 2 3 => rw [d1]
    slice_lhs 1 2 => rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [Category.id_comp]
    simp only [Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom]
  -- assemble
  rw [CategoryTheory.Functor.map_comp]
  unfold AlgebraicGeometry.Scheme.Modules.transportCore
  slice_lhs 2 3 => rw [n1]
  slice_lhs 3 4 => rw [n2]
  slice_lhs 4 5 => rw [n3]
  slice_lhs 5 6 => rw [← CategoryTheory.Functor.map_comp, hchart', CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% key]
  simp only [IsIso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(★) The transport shape carries `τ^♯m` to `φ^♯m'` on sections.** For `x` a section of `τ^*N₁` and `y` of
`τ^*N₂` over `j''A'`: `Θ₃((τ^♯m)(x ⊗ y)) = (φ^♯m')(Θ₁ x ⊗ Θ₂ y)`, where `Θₖ := transportIsoShape … cₖ`, given the
chart identity `ρ^♯m ≫ c₃ = (c₁ ⊗ c₂) ≫ m'`.

Proof: `Θₖ = rFIP ≫ Θ'ₖ`; `rFIP` on a section is the pulled-back section `pullbackSectionsOn j`
(`restrictFunctorIsoPullback_hom_app_apply`), `j^*(τ^♯m)` acts inside pulled-back sections
(`pullback_map_app_pullbackSectionsOn_bc`), the morphism identity `transportCore_mul` applies, `δ_j` on a pulled-back
tensor section is the tensor of the pulled-back sections (`pullbackTensorObjHom_app_pullbackSectionsOn`), and
`tensorHom` acts componentwise (`tensorHom_tensorSections`). -/
theorem transportIsoShape_hom_app_mul (N₁ N₂ N₃ : P.Modules) (G₁ G₂ G₃ : Q.Modules)
    (c₁ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₁ ≅ G₁)
    (c₂ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₂ ≅ G₂)
    (c₃ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj N₃ ≅ G₃)
    (m : N₁ ⊗ N₂ ⟶ N₃) (m' : G₁ ⊗ G₂ ⟶ G₃)
    (hchart : CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ N₁ N₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ρ).map m ≫ c₃.hom = (c₁.hom ⊗ₘ c₂.hom) ≫ m')
    (A' : V.Opens) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₁, j ''ᵁ A'))
    (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₂, j ''ᵁ A')) :
    (AlgebraicGeometry.Scheme.Modules.transportIsoShape j τ φ ρ hτ N₃ G₃ c₃).hom.app A'
        ((CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom τ N₁ N₂) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback τ).map m).app (j ''ᵁ A')
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (j ''ᵁ A') x y)) =
      (CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom φ G₁ G₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback φ).map m').app A'
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ A'
          ((AlgebraicGeometry.Scheme.Modules.transportIsoShape j τ φ ρ hτ N₁ G₁ c₁).hom.app A' x)
          ((AlgebraicGeometry.Scheme.Modules.transportIsoShape j τ φ ρ hτ N₂ G₂ c₂).hom.app A' y)) := by
  have hA' : A' ≤ j ⁻¹ᵁ (j ''ᵁ A') := le_of_eq (j.preimage_image_eq A').symm
  have hm := AlgebraicGeometry.Scheme.Modules.transportCore_mul j τ φ ρ hτ N₁ N₂ N₃ G₁ G₂ G₃ c₁ c₂ c₃ m m' hchart
  rw [AlgebraicGeometry.Scheme.Modules.transportIsoShape_hom_eq, AlgebraicGeometry.Scheme.Modules.transportIsoShape_hom_eq,
    AlgebraicGeometry.Scheme.Modules.transportIsoShape_hom_eq]
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₃))
      (AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₃ G₃ c₃) A',
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₁))
      (AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₁ G₁ c₁) A' x,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback j).hom.app
        ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₂))
      (AlgebraicGeometry.Scheme.Modules.transportCore j τ φ ρ hτ N₂ G₂ c₂) A' y]
  erw [AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply j
      ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₃) A',
    AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply j
      ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₁) A' x,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply j
      ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj N₂) A' y]
  rw [← AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc j
    (CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom τ N₁ N₂) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback τ).map m) (j ''ᵁ A') A' hA'
    (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (j ''ᵁ A') x y)]
  rw [← AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, hm,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_pullbackSectionsOn]
  exact congrArg _ (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ A' _ _)

end Transport

section ChartMul

variable {P R Q : AlgebraicGeometry.Scheme.{u}} (ι : R ⟶ P) [AlgebraicGeometry.IsOpenImmersion ι] (e : R ≅ Q)
  (ρ : Q ⟶ P) (hρ : e.inv ≫ ι = ρ)

/-- For an isomorphism `e`, `e⁻¹^{-1}(A) ≤ e(A)` (opens-level: `e⁻¹^{-1}A = (e⁻¹ ≫ e)^{-1}(e(A))`). -/
theorem preimage_inv_le_image_hom (A : R.Opens) : e.inv ⁻¹ᵁ A ≤ e.hom ''ᵁ A := by
  have h1 : e.inv ⁻¹ᵁ A = (e.inv ≫ e.hom) ⁻¹ᵁ (e.hom ''ᵁ A) := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, e.hom.preimage_image_eq]
  rw [h1, e.inv_hom_id]
  intro x hx
  exact hx

/-- `chartIsoShape_hom_app_pullbackSectionsOn` with the target section `t` over an arbitrary open `C` (the
version in `…Transport_Shape.lean` is the case `C = ⊤`). Same proof. -/
theorem chartIsoShape_hom_app_pullbackSectionsOn' (N : P.Modules) (G : Q.Modules)
    (a : N.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G)
    (B : P.Opens) (s : Γ(N, B)) (C : Q.Opens) (hC : ι ⁻¹ᵁ B ≤ e.hom ⁻¹ᵁ C) (t : Γ(G, C))
    (ha : a.hom.app (ι ⁻¹ᵁ B)
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv.app (ι ⁻¹ᵁ B)
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)) =
      ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G).presheaf.map (homOfLE hC).op
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom e.hom G C t))
    (U : Q.Opens) (k : U ≤ ρ ⁻¹ᵁ B) (k' : U ≤ C) :
    (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ N G a).hom.app U
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ρ N B U k s) =
      G.presheaf.map (homOfLE k').op t := by
  subst hρ
  have k₁ : U ≤ e.inv ⁻¹ᵁ (ι ⁻¹ᵁ B) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact k
  have k₄ : U ≤ e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ C) := k₁.trans (e.inv.preimage_mono hC)
  have k₅ : U ≤ (e.inv ≫ e.hom) ⁻¹ᵁ C := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact k₄
  have k₆ : U ≤ (𝟙 Q) ⁻¹ᵁ C := by
    rw [← e.inv_hom_id]
    exact k₅
  unfold AlgebraicGeometry.Scheme.Modules.chartIsoShape
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam]
  rw [AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn _ N B U k k s]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackSectionsOn e.inv ι N B U k₁ k s]
  erw [AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc e.inv
    (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv ≫ a.hom) (ι ⁻¹ᵁ B) U k₁
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)]
  erw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv a.hom (ι ⁻¹ᵁ B)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s)]
  erw [ha]
  erw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res e.inv
    ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G) k₄ k₁ hC
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom e.hom G C t)]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackSectionsOn e.inv e.hom G C U k₄ k₅ t]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_pullbackSectionsOn e.inv_hom_id G C U k₅ k₆]
  erw [AlgebraicGeometry.Scheme.Modules.pullbackId_hom_app_pullbackSectionsOn_tfam G C U k₆ t]
  rfl

/-- **The chart shape on a pulled-back section, in terms of the chart comparison alone.** For `s ∈ Γ(N, B)` and
`A := ι⁻¹B`, with `s' := s|_{ι''A}` read as a section of `N|_R` over `A`:
`chartIsoShape(ρ^*s |_U) = (rFIP(e)⁻¹ (a s'))|_U` for every `U ≤ ρ⁻¹B` (`U ≤ e''A` by `preimage_inv_le_image_hom`).
Proof: `chartIsoShape_hom_app_pullbackSectionsOn'` with `C := e''A`, `t := rFIP(e)⁻¹(a s')`; its hypothesis holds
because `rFIP(ι)⁻¹(η_ι s) = s'` (`pullbackSectionsOn_self`, `pullbackSectionsOn_res`,
`restrictFunctorIsoPullback_inv_app_pullbackSectionsOn`) and `(η_e t)|_A = rFIP(e)(t) = a s'`
(`restrictFunctorIsoPullback_hom_app_apply`, `modIso_hom_app_inv_app`). -/
theorem chartIsoShape_hom_app_pullbackSectionsOn_eq (N : P.Modules) (G : Q.Modules)
    (a : N.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G)
    (B : P.Opens) (s : Γ(N, B)) (U : Q.Opens) (k : U ≤ ρ ⁻¹ᵁ B) (k' : U ≤ e.hom ''ᵁ (ι ⁻¹ᵁ B)) :
    (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ N G a).hom.app U
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ρ N B U k s) =
      G.presheaf.map (homOfLE k').op
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app G).inv.app (ι ⁻¹ᵁ B)
          (a.hom.app (ι ⁻¹ᵁ B) (N.presheaf.map (homOfLE (ι.image_preimage_le B)).op s))) := by
  set A := ι ⁻¹ᵁ B with hA
  set s' : Γ(N, ι ''ᵁ A) := N.presheaf.map (homOfLE (ι.image_preimage_le B)).op s with hs'
  set t : Γ(G, e.hom ''ᵁ A) :=
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app G).inv.app A (a.hom.app A s') with ht
  have hC : A ≤ e.hom ⁻¹ᵁ (e.hom ''ᵁ A) := le_of_eq (e.hom.preimage_image_eq A).symm
  have hAι : A ≤ ι ⁻¹ᵁ (ι ''ᵁ A) := le_of_eq (ι.preimage_image_eq A).symm
  apply AlgebraicGeometry.Scheme.Modules.chartIsoShape_hom_app_pullbackSectionsOn' ι e ρ hρ N G a B s (e.hom ''ᵁ A) hC t
    _ U k k'
  -- the hypothesis `ha`
  have h1 : ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback ι).app N).inv.app A
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ι N B s) = s' := by
    rw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_self ι N B s,
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res ι N le_rfl hAι (ι.image_preimage_le B) s]
    exact AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_inv_app_pullbackSectionsOn ι N A hAι s'
  have h2 : ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj G).presheaf.map (homOfLE hC).op
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom e.hom G (e.hom ''ᵁ A) t) =
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app G).hom.app A t := by
    rw [AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_apply e.hom G A t]
    rfl
  rw [h1, h2, ht]
  exact (AlgebraicGeometry.Scheme.Modules.modIso_hom_app_inv_app
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app G) A _).symm

/-- Restriction of a tensor section is the tensor section of the restrictions (`tensorSections_restrict`). -/
theorem tensorSections_map_tfm {Z : AlgebraicGeometry.Scheme.{u}} {A B : Z.Modules} {U V : Z.Opens} (h : V ≤ U)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ⊗ B).presheaf.map (homOfLE h).op (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B V (A.presheaf.map (homOfLE h).op a)
        (B.presheaf.map (homOfLE h).op b) :=
  AlgebraicGeometry.Scheme.Modules.tensorSections_restrict A B (homOfLE h) a b

/-- `(tensorIsoTensorObj A B).inv = tensorToSheafify A B` (definitional). -/
theorem tensorIsoTensorObj_inv_eq {Z : AlgebraicGeometry.Scheme.{u}} (A B : Z.Modules) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).inv = AlgebraicGeometry.Scheme.Modules.tensorToSheafify A B :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The local multiplication on pure tensor sections, through the chart comparisons.** If `μP|_R` is the shape
`twistMulLocalShape ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μQ` (`hμ`), then for `x ∈ Γ(M₁, ι''A)`, `y ∈ Γ(M₂, ι''A)`:
`rFIP(e)⁻¹(i₃ (μP (x ⊗ y))) = μQ (t₁ ⊗ t₂)` with `tₖ := rFIP(e)⁻¹(iₖ x)`, `rFIP(e)⁻¹(i₂ y)`, where `⊗` denotes
`tensorIsoTensorObj⁻¹ (tensorSections · ·)`. Proof: `μP` on `ι''A` is `(restrictFunctor ι).map μP` on `A`
(definitional), `= shape` by `hμ`; `shape ≫ i₃.hom` is the normal form (`twistMulLocalShape_comp_eq`) whose value on
`η(x ⊗ y)` is given by `twistMulNormalForm_val_app`; `tensorToSheafify_tensorSections` translates between
`tensorIsoTensorObj⁻¹ (tensorSections x y)` and the sheafification unit on `x ⊗ₜ y`. -/
theorem shape_mul_app_tensorSections (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Q.Modules)
    (i₁ : M₁.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₁)
    (i₂ : M₂.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₂)
    (i₃ : M₃.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₃)
    (μP : AlgebraicGeometry.Scheme.Modules.tensor M₁ M₂ ⟶ M₃) (μQ : AlgebraicGeometry.Scheme.Modules.tensor N₁ N₂ ⟶ N₃)
    (hμ : (AlgebraicGeometry.Scheme.Modules.restrictFunctor ι).map μP =
      AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ι e.hom M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μQ)
    (A : R.Opens) (x : Γ(M₁, ι ''ᵁ A)) (y : Γ(M₂, ι ''ᵁ A)) :
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app N₃).inv.app A
        (i₃.hom.app A (μP.app (ι ''ᵁ A)
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv.app (ι ''ᵁ A)
            (AlgebraicGeometry.Scheme.Modules.tensorSections M₁ M₂ (ι ''ᵁ A) x y)))) =
      μQ.app (e.hom ''ᵁ A)
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv.app (e.hom ''ᵁ A)
          (AlgebraicGeometry.Scheme.Modules.tensorSections N₁ N₂ (e.hom ''ᵁ A)
            (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app N₁).inv.app A (i₁.hom.app A x))
            (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app N₂).inv.app A (i₂.hom.app A y)))) := by
  have hz : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv.app (ι ''ᵁ A)
      (AlgebraicGeometry.Scheme.Modules.tensorSections M₁ M₂ (ι ''ᵁ A) x y) =
      ((AlgebraicGeometry.Scheme.Modules.shAdj P).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG P).obj M₁ ⊗ (AlgebraicGeometry.Scheme.Modules.shG P).obj M₂)).app
        (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y) :=
    AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections M₁ M₂ (ι ''ᵁ A) x y
  have hw : ∀ (u : Γ(N₁, e.hom ''ᵁ A)) (v : Γ(N₂, e.hom ''ᵁ A)),
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv.app (e.hom ''ᵁ A)
        (AlgebraicGeometry.Scheme.Modules.tensorSections N₁ N₂ (e.hom ''ᵁ A) u v) =
      ((AlgebraicGeometry.Scheme.Modules.shAdj Q).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG Q).obj N₁ ⊗ (AlgebraicGeometry.Scheme.Modules.shG Q).obj N₂)).app
        (op (e.hom ''ᵁ A)) (TensorProduct.tmul _ u v) :=
    fun u v => AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections N₁ N₂ (e.hom ''ᵁ A) u v
  rw [hz]
  -- `μP` on `ι''A` is `(restrictFunctor ι).map μP` on `A`, which is the shape
  have hres : ∀ z : Γ(AlgebraicGeometry.Scheme.Modules.tensor M₁ M₂, ι ''ᵁ A),
      μP.app (ι ''ᵁ A) z =
        (AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ι e.hom M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μQ).app A z := by
    intro z
    rw [← hμ]
    rfl
  rw [hres]
  have hc := AlgebraicGeometry.Scheme.Modules.app_app_eq_of_comp_eq _ _ _
    (AlgebraicGeometry.Scheme.Modules.twistMulLocalShape_comp_eq ι e.hom M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃
      i₁.hom i₂.hom i₃.hom rfl rfl rfl μQ) A
    (((AlgebraicGeometry.Scheme.Modules.shAdj P).unit.app
        ((AlgebraicGeometry.Scheme.Modules.shG P).obj M₁ ⊗ (AlgebraicGeometry.Scheme.Modules.shG P).obj M₂)).app
        (op (ι ''ᵁ A)) (TensorProduct.tmul _ x y))
  rw [hc]
  have hn := AlgebraicGeometry.Scheme.Modules.twistMulNormalForm_val_app ι e.hom M₁ M₂ N₁ N₂ N₃ i₁.hom i₂.hom μQ A x y
  erw [hn]
  refine (AlgebraicGeometry.Scheme.Modules.modIso_inv_app_hom_app
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app N₃) A _).trans ?_
  exact congrArg (fun z => μQ.app (e.hom ''ᵁ A) z) (hw _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- **The chart identity for the chart shape (★★).** If `μP|_R` is the local shape
`twistMulLocalShape ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μQ` (`hμ`; for `twistMul S a b` this is
`restrictFunctor_map_glueHom` + `twistMulLocal_eq_shape`), then with `cₖ := chartIsoShape … iₖ : ρ^*Mₖ ≅ Nₖ`:
`δ_ρ⁻¹ ≫ ρ^*(tITO⁻¹ ≫ μP) ≫ c₃ = (c₁ ⊗ c₂) ≫ tITO⁻¹ ≫ μQ` as morphisms `ρ^*M₁ ⊗ ρ^*M₂ ⟶ N₃`.

Proof (Stacks 01NR/01MO made formal). Cancel `δ_ρ` on the left; two morphisms out of `ρ^*(M₁ ⊗ M₂)` agree iff their
adjoint transposes `M₁ ⊗ M₂ ⟶ ρ_*N₃` agree (`Adjunction.homEquiv` injective, `homEquiv_unit`), and morphisms out of a
tensor product agree iff they agree on pure tensor sections `u ⊗ v` (`tensorObj_hom_ext`). On `η(u ⊗ v)`, i.e. the
pulled-back section `(ρ^*(u ⊗ v))|_{ρ⁻¹B}`: the left side is `c₃((ρ^*(μP(u ⊗ v)))|_{ρ⁻¹B})`
(`pullback_map_app_pullbackSectionsOn_bc`) `= (rFIP(e)⁻¹(i₃((μP(u ⊗ v))|_{ι''A})))|_{ρ⁻¹B}`
(`chartIsoShape_hom_app_pullbackSectionsOn_eq`, `A := ι⁻¹B`); the right side is `μQ(tITO⁻¹(c₁(ρ^*u) ⊗ c₂(ρ^*v)))`
(`pullbackTensorObjHom_app_pullbackSectionsOn`, `tensorHom_tensorSections`) `= (μQ(tITO⁻¹(t₁ ⊗ t₂)))|_{ρ⁻¹B}` with
`tₖ := rFIP(e)⁻¹(iₖ(u|_{ι''A}))` (`chartIsoShape_hom_app_pullbackSectionsOn_eq`, `tensorSections_map`, `app_res'`).
Both restrictions are along `ρ⁻¹B ≤ e''A` (`preimage_inv_le_image_hom`), and the inner sections agree by
`shape_mul_app_tensorSections`. -/
theorem chartIsoShape_mul (M₁ M₂ M₃ : P.Modules) (N₁ N₂ N₃ : Q.Modules)
    (i₁ : M₁.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₁)
    (i₂ : M₂.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₂)
    (i₃ : M₃.restrict ι ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj N₃)
    (μP : AlgebraicGeometry.Scheme.Modules.tensor M₁ M₂ ⟶ M₃) (μQ : AlgebraicGeometry.Scheme.Modules.tensor N₁ N₂ ⟶ N₃)
    (hμ : (AlgebraicGeometry.Scheme.Modules.restrictFunctor ι).map μP =
      AlgebraicGeometry.Scheme.Modules.twistMulLocalShape ι e.hom M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μQ) :
    CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ M₁ M₂) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ρ).map
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv ≫ μP) ≫
        (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₃ N₃ i₃).hom =
      ((AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₁ N₁ i₁).hom ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₂ N₂ i₂).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv ≫ μQ := by
  rw [← cancel_epi (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ M₁ M₂), IsIso.hom_inv_id_assoc]
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_hom_ext
  intro B u v
  change ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv ≫ μP) ≫
        (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₃ N₃ i₃).hom).app (ρ ⁻¹ᵁ B)
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ρ (M₁ ⊗ M₂) B
        (AlgebraicGeometry.Scheme.Modules.tensorSections M₁ M₂ B u v)) =
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ M₁ M₂ ≫
        ((AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₁ N₁ i₁).hom ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₂ N₂ i₂).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv ≫ μQ).app (ρ ⁻¹ᵁ B)
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ρ (M₁ ⊗ M₂) B
        (AlgebraicGeometry.Scheme.Modules.tensorSections M₁ M₂ B u v))
  rw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_self ρ (M₁ ⊗ M₂) B]
  have k' : ρ ⁻¹ᵁ B ≤ e.hom ''ᵁ (ι ⁻¹ᵁ B) := by
    subst hρ
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage]
    exact AlgebraicGeometry.Scheme.Modules.preimage_inv_le_image_hom e (ι ⁻¹ᵁ B)
  have hι : ι ''ᵁ (ι ⁻¹ᵁ B) ≤ B := ι.image_preimage_le B
  -- left side
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv ≫ μP))
      (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₃ N₃ i₃).hom (ρ ⁻¹ᵁ B),
    AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc ρ _ B (ρ ⁻¹ᵁ B) le_rfl,
    AlgebraicGeometry.Scheme.Modules.chartIsoShape_hom_app_pullbackSectionsOn_eq ι e ρ hρ M₃ N₃ i₃ B _ (ρ ⁻¹ᵁ B) le_rfl k']
  -- right side
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ρ M₁ M₂)
      (((AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₁ N₁ i₁).hom ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₂ N₂ i₂).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv ≫ μQ) (ρ ⁻¹ᵁ B),
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam
      ((AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₁ N₁ i₁).hom ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.chartIsoShape ι e ρ hρ M₂ N₂ i₂).hom)
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv ≫ μQ) (ρ ⁻¹ᵁ B),
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv μQ
      (ρ ⁻¹ᵁ B),
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_pullbackSectionsOn]
  erw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections,
    AlgebraicGeometry.Scheme.Modules.chartIsoShape_hom_app_pullbackSectionsOn_eq ι e ρ hρ M₁ N₁ i₁ B u (ρ ⁻¹ᵁ B) le_rfl k',
    AlgebraicGeometry.Scheme.Modules.chartIsoShape_hom_app_pullbackSectionsOn_eq ι e ρ hρ M₂ N₂ i₂ B v (ρ ⁻¹ᵁ B) le_rfl k']
  rw [← AlgebraicGeometry.Scheme.Modules.tensorSections_map_tfm k',
    AlgebraicGeometry.Scheme.Modules.app_res' (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N₁ N₂).inv k',
    AlgebraicGeometry.Scheme.Modules.app_res' μQ k']
  congr 1
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv μP B,
    ← AlgebraicGeometry.Scheme.Modules.app_res' μP hι,
    ← AlgebraicGeometry.Scheme.Modules.app_res' (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M₁ M₂).inv hι,
    AlgebraicGeometry.Scheme.Modules.tensorSections_map_tfm hι]
  exact AlgebraicGeometry.Scheme.Modules.shape_mul_app_tensorSections ι e M₁ M₂ M₃ N₁ N₂ N₃ i₁ i₂ i₃ μP μQ hμ
    (ι ⁻¹ᵁ B) _ _

end ChartMul

end AlgebraicGeometry.Scheme.Modules

end
