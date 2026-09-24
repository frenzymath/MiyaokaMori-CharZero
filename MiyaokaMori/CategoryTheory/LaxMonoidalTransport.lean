import MiyaokaMori.Prelude

/-! # Transport of a lax monoidal structure along a natural isomorphism

**Transporting a lax monoidal structure along a natural isomorphism of functors**: let `F G : C ⥤ D`
be functors between monoidal categories, `F` lax monoidal and `i : F ≅ G` a natural isomorphism. Then
`G` is lax monoidal with structure maps

* `ε G = ε F ≫ i.hom.app (𝟙_ C)`;
* `μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)`.

Proof: each of the five axioms follows from the corresponding axiom of `F` and the naturality of
`i.hom` / `i.inv`. For associativity: write all `▷` / `◁` as `⊗ₘ`, merge adjacent tensor morphisms
with `tensorHom_comp_tensorHom`, cancel the middle pair `i.hom.app ∘ i.inv.app = 𝟙`, so the left side
becomes `((i.inv X ⊗ₘ i.inv Y) ⊗ₘ i.inv Z) ≫ (μ F X Y ▷ F Z) ≫ μ F (X⊗Y) Z ≫ F(α) ≫ i.hom` (using the
naturality `i.hom.app _ ≫ G.map α = F.map α ≫ i.hom.app _`); then replace the middle three terms by
`α_(F X, F Y, F Z).hom ≫ (F X ◁ μ F Y Z) ≫ μ F X (Y⊗Z)` using the associativity of `F`, and finally
replace `α_(F …)` by `α_(G …)` with `associator_naturality`; both sides now agree term by term.

Mathlib only has the strong monoidal version `CategoryTheory.Functor.Monoidal.transport`
(`CategoryTheory/Monoidal/Functor.lean`); the lax version is what is needed to transport the lax
monoidal structure of the pushforward of sheaves of modules `Scheme.Modules.pushforward f` from
`forget ⋙ PresheafOfModules.pushforward ⋙ sheafify`.

Reference: the lax analogue of Mathlib's `Functor.Monoidal.transport`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory.Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Transport of a **lax** monoidal structure along a natural isomorphism of functors (Mathlib only
has the strong monoidal version `CategoryTheory.Functor.Monoidal.transport`). -/
@[instance_reducible]
noncomputable def transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) : G.LaxMonoidal where
  ε := ε F ≫ i.hom.app (𝟙_ C)
  μ X Y := (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y)
  μ_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μ_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    simp only [← tensorHom_id, ← id_tensorHom]
    simp only [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app, Category.id_comp,
      Category.comp_id]
    conv_lhs =>
      rw [show i.inv.app Z = i.inv.app Z ≫ 𝟙 (F.obj Z) from (Category.comp_id _).symm,
        ← tensorHom_comp_tensorHom]
    rw [← i.hom.naturality, tensorHom_id]
    simp only [Category.assoc]
    rw [associativity_assoc F X Y Z, associator_naturality_assoc]
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
  left_unitality X := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id, Category.id_comp]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp
  right_unitality X := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id, Category.id_comp]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp

@[reassoc]
theorem transport_ε {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    ε G = ε F ≫ i.hom.app (𝟙_ C) := rfl

@[reassoc]
theorem transport_μ {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) (X Y : C) :
    letI := transport i
    μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X ⊗ Y) := rfl

end CategoryTheory.Functor.LaxMonoidal
