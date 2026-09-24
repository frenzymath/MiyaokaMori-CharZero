import MiyaokaMori.Prelude

/-! # Transport of the commutative monoid axioms along a lax monoidal functor and an isomorphism

**Transporting the axioms of a commutative monoid object along a lax monoidal functor and an
isomorphism** — the general input for the three algebra axioms `one_mul` / `mul_assoc` / `mul_comm` of
the pushforward of a quasi-coherent algebra; independent of schemes and sheafification.

Let `F : C ⥤ D` be lax monoidal (`F.LaxMonoidal`, with unit comparison `ε F : 𝟙_ D ⟶ F.obj (𝟙_ C)` and
tensor comparison `μ F P Q : F.obj P ⊗ F.obj Q ⟶ F.obj (P ⊗ Q)`), `P : C` a monoid object (`MonObj P`,
multiplication `μ[P]`, unit `η[P]`), and `e : F.obj P ≅ M` an isomorphism in `D`. Put
* `transportMul := (e.inv ⊗ₘ e.inv) ≫ μ F P P ≫ F.map μ[P] ≫ e.hom : M ⊗ M ⟶ M`,
* `transportOne := ε F ≫ F.map η[P] ≫ e.hom : 𝟙_ D ⟶ M`.

Then `M` satisfies the left unit law and associativity in the form of the fields of `X.QCAlgebra`; if
`F` is lax braided (`F.LaxBraided`) and `P` is commutative (`IsCommMonObj P`), also commutativity.

Reference: a direct combination of Mathlib's `CategoryTheory.Functor.monObjObj` (a lax monoidal
functor sends monoid objects to monoid objects) and `CategoryTheory.MonObj.ofIso` (transport of monoid
objects along isomorphisms); commutativity uses `CategoryTheory.Functor.isCommMonObj_obj` and the
naturality of the braiding `BraidedCategory.braiding_naturality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory.Functor.LaxMonoidal

open scoped MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] (P : C) [MonObj P] {M : D} (e : F.obj P ≅ M)

/-- The transported multiplication `(e⁻¹ ⊗ e⁻¹) ≫ μ ≫ F(μ[P]) ≫ e`. -/
abbrev transportMul : M ⊗ M ⟶ M :=
  (e.inv ⊗ₘ e.inv) ≫ LaxMonoidal.μ F P P ≫ F.map μ[P] ≫ e.hom

/-- The transported unit `ε ≫ F(η[P]) ≫ e`. -/
abbrev transportOne : 𝟙_ D ⟶ M :=
  LaxMonoidal.ε F ≫ F.map η[P] ≫ e.hom

/-- The left unit law transported along a lax monoidal functor and an isomorphism (in the form of
`X.QCAlgebra.one_mul`). -/
theorem transport_one_mul :
    (λ_ M).hom = (transportOne F P e ▷ M) ≫ transportMul F P e := by
  let _ : MonObj (F.obj P) := F.monObjObj P
  let _ : MonObj M := MonObj.ofIso e
  have h := MonObj.one_mul M
  change ((LaxMonoidal.ε F ≫ F.map η[P]) ≫ e.hom) ▷ M ≫
    (e.inv ⊗ₘ e.inv) ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) ≫ e.hom = (λ_ M).hom at h
  simpa only [Category.assoc] using h.symm

/-- Associativity transported along a lax monoidal functor and an isomorphism (in the form of
`X.QCAlgebra.mul_assoc`). -/
theorem transport_mul_assoc :
    (α_ M M M).hom ≫ (M ◁ transportMul F P e) ≫ transportMul F P e =
      (transportMul F P e ▷ M) ≫ transportMul F P e := by
  let _ : MonObj (F.obj P) := F.monObjObj P
  let _ : MonObj M := MonObj.ofIso e
  have h := MonObj.mul_assoc M
  change (((e.inv ⊗ₘ e.inv) ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) ≫ e.hom) ▷ M) ≫
      ((e.inv ⊗ₘ e.inv) ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) ≫ e.hom) =
    (α_ M M M).hom ≫ (M ◁ ((e.inv ⊗ₘ e.inv) ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) ≫ e.hom)) ≫
      ((e.inv ⊗ₘ e.inv) ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) ≫ e.hom) at h
  simpa only [Category.assoc] using h.symm

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor.LaxBraided

open scoped MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.LaxBraided] (P : C) [MonObj P] [IsCommMonObj P] {M : D} (e : F.obj P ≅ M)

/-- Commutativity transported along a lax braided functor and an isomorphism (in the form of
`X.QCAlgebra.mul_comm`). In a separate section assuming only `F.LaxBraided`, to avoid an instance
diamond with `F.LaxMonoidal`. -/
theorem transport_mul_comm :
    (β_ M M).hom ≫ LaxMonoidal.transportMul F P e = LaxMonoidal.transportMul F P e := by
  have h1 : (β_ M M).hom ≫ (e.inv ⊗ₘ e.inv) =
      (e.inv ⊗ₘ e.inv) ≫ (β_ (F.obj P) (F.obj P)).hom :=
    (BraidedCategory.braiding_naturality e.inv e.inv).symm
  -- commutativity of `F.obj P`: the braiding passes through μ by `LaxBraided.braided`, then use the commutativity of `P`
  have h2 : (β_ (F.obj P) (F.obj P)).hom ≫ (LaxMonoidal.μ F P P ≫ F.map μ[P]) =
      LaxMonoidal.μ F P P ≫ F.map μ[P] := by
    rw [← Category.assoc, ← Functor.LaxBraided.braided, Category.assoc, ← F.map_comp,
      IsCommMonObj.mul_comm]
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (LaxMonoidal.μ F P P),
    ← Category.assoc (β_ (F.obj P) (F.obj P)).hom, h2, Category.assoc]

end CategoryTheory.Functor.LaxBraided

end
