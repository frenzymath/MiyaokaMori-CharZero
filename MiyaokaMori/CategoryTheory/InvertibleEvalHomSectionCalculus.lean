import MiyaokaMori.Prelude

/-! # Hom–section calculus for an invertible object

**Hom–section calculus for an invertible object, abstractly.** Let `F : C ⥤ D` be a braided strong monoidal
functor between braided monoidal categories, `D` symmetric. Fix objects `A, Da : C` with an isomorphism
`ev : Da ⊗ A ≅ 𝟙_ C` ("evaluation": for a line bundle `A` on a scheme, `Da = A^∨` and `ev` is the evaluation
pairing, an isomorphism by Stacks 01CT) such that the braiding `β_{A,A}` is the identity (true for line bundles,
Stacks 01CR). Transport the pair to `D`: `cT := ε ≫ F(ev⁻¹) ≫ δ : 𝟙_D ⟶ F Da ⊗ F A`,
`eT := μ ≫ F(ev) ≫ η : F Da ⊗ F A ⟶ 𝟙_D`; then `cT ≫ eT = 𝟙` and `β_{FA,FA} = 𝟙`.

* To a morphism `φ : F A ⟶ F B` attach the "section" `secHom φ := cT ≫ F Da ◁ φ ≫ μ : 𝟙_D ⟶ F (Da ⊗ B)`.
* `hom_eq_secHom`: `φ` is recovered from `secHom φ` by pairing with the base evaluation
  `evBase ev B : A ⊗ (Da ⊗ B) ⟶ B` (associator, braiding, `ev`, unitor):
  `(ρ_ (F A)).inv ≫ F A ◁ secHom φ ≫ μ ≫ F (evBase ev B) = φ`.
* `pair_secHom_eq`: for `φ : F A ⟶ F B`, `ψ : F B ⟶ F A` with `φ ≫ ψ = 𝟙`, the product of the two sections,
  paired by `pairBase evA evB : (Da ⊗ B) ⊗ (Db ⊗ A) ⟶ 𝟙_C`, is the unit section `ε`.
* `..._transport` versions carry along the bookkeeping isomorphisms (`Av ≅ Da`, `H ≅ Av ⊗ B`, `AH ≅ A ⊗ H`,
  `TH ≅ F A ⊗ F H`, `F (A ⊗ H) ≅ F A ⊗ F H`) in exactly the shape in which `xiSectionMul`, `pullbackTensorIso`
  and `LineBundle.zpow (-1)` produce them on the total space of a line bundle.

The proofs are pure monoidal algebra: naturality of the structure isomorphisms, the exchange law, the hexagon
(`braiding_tensor_left_hom`), symmetry `β ≫ β = 𝟙`, and the strong monoidal functor identities
(`Functor.Monoidal.map_*`, `μ_δ`, `δ_μ`, `ε_η`, `η_ε`, `Functor.map_braiding`).

Source: Stacks 01CM/01CN (Hom and tensor commute with pullback; `Hom(A, B) ≅ A^∨ ⊗ B`), 01CT (the evaluation
of an invertible sheaf is an isomorphism), 01CR (symmetry on `L ⊗ L`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v u' v'

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.EvalCalculus

section Base

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]

omit [SymmetricCategory D] in
/-- `(λ_ 𝟙).inv ≫ (q ⊗ₘ σ) = q ≫ (ρ_ X).inv ≫ X ◁ σ` for `q : 𝟙 ⟶ X`, `σ : 𝟙 ⟶ Y`. -/
@[reassoc]
theorem leftUnitor_inv_tensorHom {X Y : D} (q : 𝟙_ D ⟶ X) (σ : 𝟙_ D ⟶ Y) :
    (λ_ (𝟙_ D)).inv ≫ (q ⊗ₘ σ) = q ≫ (ρ_ X).inv ≫ X ◁ σ := by
  rw [tensorHom_def, unitors_inv_equal, ← Category.assoc, ← rightUnitor_inv_naturality]
  simp only [Category.assoc]

/-- `(ρ_ V).inv ≫ V ◁ c ≫ α⁻¹ ≫ β_{V,Dv} ▷ V = (λ_ V).inv ≫ c ▷ V` when `β_{V,V} = 𝟙` (symmetric `D`). -/
theorem rightUnitor_inv_whiskerLeft_braiding {V Dv : D} (c : 𝟙_ D ⟶ Dv ⊗ V)
    (hβ : (β_ V V).hom = 𝟙 _) :
    (ρ_ V).inv ≫ V ◁ c ≫ (α_ V Dv V).inv ≫ (β_ V Dv).hom ▷ V = (λ_ V).inv ≫ c ▷ V := by
  have h1 : (ρ_ V).inv ≫ V ◁ c = (λ_ V).inv ≫ c ▷ V ≫ (β_ (Dv ⊗ V) V).hom := by
    rw [BraidedCategory.braiding_naturality_left, braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h2 : (β_ (Dv ⊗ V) V).hom = (β_ Dv V).hom ▷ V ≫ (α_ V Dv V).hom := by
    rw [BraidedCategory.braiding_tensor_left_hom, hβ, whiskerLeft_id, Category.id_comp,
      Iso.hom_inv_id_assoc]
  have h1' := reassoc_of% h1
  rw [h1', h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight, Category.comp_id]

/-- **Core identity.** For `c : 𝟙 ⟶ Dv ⊗ V`, `e : Dv ⊗ V ⟶ 𝟙` with `c ≫ e = 𝟙` and `β_{V,V} = 𝟙`, every
`φ : V ⟶ B` is recovered from `c ≫ Dv ◁ φ` by pairing with `e`. -/
theorem hom_eq_of_pair {V Dv B : D} (c : 𝟙_ D ⟶ Dv ⊗ V) (e : Dv ⊗ V ⟶ 𝟙_ D) (hce : c ≫ e = 𝟙 _)
    (hβ : (β_ V V).hom = 𝟙 _) (φ : V ⟶ B) :
    (ρ_ V).inv ≫ V ◁ (c ≫ Dv ◁ φ) ≫ (α_ V Dv B).inv ≫ (β_ V Dv).hom ▷ B ≫ e ▷ B ≫ (λ_ B).hom = φ := by
  have h1 : V ◁ (Dv ◁ φ) ≫ (α_ V Dv B).inv = (α_ V Dv V).inv ≫ (V ⊗ Dv) ◁ φ :=
    associator_inv_naturality_right V Dv φ
  have h2 : (V ⊗ Dv) ◁ φ ≫ (β_ V Dv).hom ▷ B = (β_ V Dv).hom ▷ V ≫ (Dv ⊗ V) ◁ φ :=
    whisker_exchange _ _
  have h3 : (Dv ⊗ V) ◁ φ ≫ e ▷ B = e ▷ V ≫ 𝟙_ D ◁ φ := whisker_exchange _ _
  have h4 : 𝟙_ D ◁ φ ≫ (λ_ B).hom = (λ_ V).hom ≫ φ := leftUnitor_naturality φ
  have h5 := rightUnitor_inv_whiskerLeft_braiding c hβ
  calc (ρ_ V).inv ≫ V ◁ (c ≫ Dv ◁ φ) ≫ (α_ V Dv B).inv ≫ (β_ V Dv).hom ▷ B ≫ e ▷ B ≫ (λ_ B).hom
      = (ρ_ V).inv ≫ V ◁ c ≫ (V ◁ (Dv ◁ φ) ≫ (α_ V Dv B).inv) ≫ (β_ V Dv).hom ▷ B ≫ e ▷ B ≫
          (λ_ B).hom := by
        simp only [whiskerLeft_comp, Category.assoc]
    _ = (ρ_ V).inv ≫ V ◁ c ≫ (α_ V Dv V).inv ≫ ((V ⊗ Dv) ◁ φ ≫ (β_ V Dv).hom ▷ B) ≫ e ▷ B ≫
          (λ_ B).hom := by
        rw [h1]; simp only [Category.assoc]
    _ = (ρ_ V).inv ≫ V ◁ c ≫ (α_ V Dv V).inv ≫ (β_ V Dv).hom ▷ V ≫ ((Dv ⊗ V) ◁ φ ≫ e ▷ B) ≫
          (λ_ B).hom := by
        rw [h2]; simp only [Category.assoc]
    _ = ((ρ_ V).inv ≫ V ◁ c ≫ (α_ V Dv V).inv ≫ (β_ V Dv).hom ▷ V) ≫ e ▷ V ≫
          (𝟙_ D ◁ φ ≫ (λ_ B).hom) := by
        rw [h3]; simp only [Category.assoc]
    _ = ((λ_ V).inv ≫ c ▷ V) ≫ e ▷ V ≫ (λ_ V).hom ≫ φ := by rw [h5, h4]
    _ = φ := by
        rw [Category.assoc, ← Category.assoc (c ▷ V), ← comp_whiskerRight, hce, id_whiskerRight,
          Category.id_comp, Iso.inv_hom_id_assoc]

/-- **Core identity for the product of two sections.** With `(cA, eA)`, `(cB, eB)` as in `hom_eq_of_pair`
(`β_{B,B} = 𝟙`), and `φ : A ⟶ B`, `ψ : B ⟶ A` with `φ ≫ ψ = 𝟙`, the product of `cA ≫ Da ◁ φ` and
`cB ≫ Db ◁ ψ`, paired by "`eB` in the middle, then `eA`", is the identity of the unit. -/
theorem pair_secHom_eq_id {A Da B Db : D} (cA : 𝟙_ D ⟶ Da ⊗ A) (eA : Da ⊗ A ⟶ 𝟙_ D)
    (hA : cA ≫ eA = 𝟙 _) (cB : 𝟙_ D ⟶ Db ⊗ B) (eB : Db ⊗ B ⟶ 𝟙_ D) (hB : cB ≫ eB = 𝟙 _)
    (hβB : (β_ B B).hom = 𝟙 _) (φ : A ⟶ B) (ψ : B ⟶ A) (hφψ : φ ≫ ψ = 𝟙 A) :
    (λ_ (𝟙_ D)).inv ≫ ((cA ≫ Da ◁ φ) ⊗ₘ (cB ≫ Db ◁ ψ)) ≫ (α_ Da B (Db ⊗ A)).hom ≫
      Da ◁ ((α_ B Db A).inv ≫ (β_ B Db).hom ▷ A ≫ eB ▷ A ≫ (λ_ A).hom) ≫ eA = 𝟙 _ := by
  have hinner := hom_eq_of_pair cB eB hB hβB ψ
  have h1 := leftUnitor_inv_tensorHom (cA ≫ Da ◁ φ) (cB ≫ Db ◁ ψ)
  have h2 : (ρ_ (Da ⊗ B)).inv ≫ (Da ⊗ B) ◁ (cB ≫ Db ◁ ψ) ≫ (α_ Da B (Db ⊗ A)).hom =
      Da ◁ (ρ_ B).inv ≫ Da ◁ (B ◁ (cB ≫ Db ◁ ψ)) := by
    rw [rightUnitor_tensor_inv, Category.assoc, associator_naturality_right, Iso.inv_hom_id_assoc]
  calc (λ_ (𝟙_ D)).inv ≫ ((cA ≫ Da ◁ φ) ⊗ₘ (cB ≫ Db ◁ ψ)) ≫ (α_ Da B (Db ⊗ A)).hom ≫
        Da ◁ ((α_ B Db A).inv ≫ (β_ B Db).hom ▷ A ≫ eB ▷ A ≫ (λ_ A).hom) ≫ eA
      = (cA ≫ Da ◁ φ) ≫ ((ρ_ (Da ⊗ B)).inv ≫ (Da ⊗ B) ◁ (cB ≫ Db ◁ ψ) ≫ (α_ Da B (Db ⊗ A)).hom) ≫
          Da ◁ ((α_ B Db A).inv ≫ (β_ B Db).hom ▷ A ≫ eB ▷ A ≫ (λ_ A).hom) ≫ eA := by
        rw [← Category.assoc, h1]; simp only [Category.assoc]
    _ = cA ≫ Da ◁ (φ ≫ (ρ_ B).inv ≫ B ◁ (cB ≫ Db ◁ ψ) ≫ (α_ B Db A).inv ≫ (β_ B Db).hom ▷ A ≫
          eB ▷ A ≫ (λ_ A).hom) ≫ eA := by
        rw [h2]; simp only [whiskerLeft_comp, Category.assoc]
    _ = cA ≫ Da ◁ (φ ≫ ψ) ≫ eA := by rw [hinner]
    _ = 𝟙 _ := by rw [hφψ, whiskerLeft_id, Category.id_comp, hA]

omit [SymmetricCategory D] in
/-- Cancelling a `μ`/`δ` pair between a tensor product of two sections and a right whiskering. -/
@[reassoc]
theorem tensorHom_comp_whiskerRight_cancel {P₀ P P' Q₀ Q Q' : D} (x : 𝟙_ D ⟶ P₀) (x' : P₀ ⟶ P)
    (m : P ⟶ P') (d : P' ⟶ P) (hmd : m ≫ d = 𝟙 P) (y : 𝟙_ D ⟶ Q₀) (y' : Q₀ ⟶ Q) (m' : Q ⟶ Q') :
    ((x ≫ x' ≫ m) ⊗ₘ (y ≫ y' ≫ m')) ≫ d ▷ Q' = ((x ≫ x') ⊗ₘ (y ≫ y')) ≫ P ◁ m' := by
  rw [← Category.assoc x, ← Category.assoc y, ← tensorHom_comp_tensorHom, tensorHom_def' m m',
    Category.assoc, Category.assoc, ← comp_whiskerRight, hmd, id_whiskerRight, Category.comp_id]

end Base

section Functorial

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
variable (F : C ⥤ D) [F.Braided]

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {Da A : C}

/-- The transported coevaluation `ε ≫ F(ev⁻¹) ≫ δ : 𝟙_D ⟶ F Da ⊗ F A`. -/
def cT (ev : Da ⊗ A ≅ 𝟙_ C) : 𝟙_ D ⟶ F.obj Da ⊗ F.obj A := ε F ≫ F.map ev.inv ≫ δ F Da A

/-- The transported evaluation `μ ≫ F(ev) ≫ η : F Da ⊗ F A ⟶ 𝟙_D`. -/
def eT (ev : Da ⊗ A ≅ 𝟙_ C) : F.obj Da ⊗ F.obj A ⟶ 𝟙_ D := μ F Da A ≫ F.map ev.hom ≫ η F

theorem cT_eT (ev : Da ⊗ A ≅ 𝟙_ C) : cT F ev ≫ eT F ev = 𝟙 _ := by
  simp only [cT, eT, Category.assoc, Functor.Monoidal.δ_μ_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

/-- `β_{A,A} = 𝟙` is preserved by a braided strong monoidal functor. -/
theorem braiding_obj_eq_id (hβ : (β_ A A).hom = 𝟙 _) : (β_ (F.obj A) (F.obj A)).hom = 𝟙 _ := by
  have h := Functor.LaxBraided.braided (F := F) A A
  rw [hβ, Functor.map_id, Category.comp_id] at h
  exact (cancel_mono (μ F A A)).1 (h.symm.trans (Category.id_comp _).symm)

/-- The base evaluation `A ⊗ (Da ⊗ B) ⟶ B`: associator, braiding `A ⊗ Da ≅ Da ⊗ A`, `ev`, left unitor. -/
def evBase (ev : Da ⊗ A ≅ 𝟙_ C) (B : C) : A ⊗ (Da ⊗ B) ⟶ B :=
  (α_ A Da B).inv ≫ (β_ A Da).hom ▷ B ≫ ev.hom ▷ B ≫ (λ_ B).hom

/-- `evBase` as an isomorphism. -/
def evBaseIso (ev : Da ⊗ A ≅ 𝟙_ C) (B : C) : A ⊗ (Da ⊗ B) ≅ B :=
  (α_ A Da B).symm ≪≫ whiskerRightIso (β_ A Da) B ≪≫ whiskerRightIso ev B ≪≫ λ_ B

theorem evBaseIso_hom (ev : Da ⊗ A ≅ 𝟙_ C) (B : C) : (evBaseIso ev B).hom = evBase ev B := rfl

theorem map_evBase (ev : Da ⊗ A ≅ 𝟙_ C) (B : C) :
    F.map (evBase ev B) =
      δ F A (Da ⊗ B) ≫ F.obj A ◁ δ F Da B ≫ (α_ (F.obj A) (F.obj Da) (F.obj B)).inv ≫
        (β_ (F.obj A) (F.obj Da)).hom ▷ F.obj B ≫ eT F ev ▷ F.obj B ≫ (λ_ (F.obj B)).hom := by
  simp only [evBase, eT, Functor.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Functor.map_braiding, Functor.Monoidal.map_leftUnitor,
    Category.assoc, Functor.Monoidal.μ_δ_assoc, comp_whiskerRight, Functor.Monoidal.whiskerRight_μ_δ_assoc]

/-- The section attached to `φ : F A ⟶ F B`: `cT ≫ F Da ◁ φ ≫ μ : 𝟙_D ⟶ F (Da ⊗ B)`. -/
def secHom (ev : Da ⊗ A ≅ 𝟙_ C) {B : C} (φ : F.obj A ⟶ F.obj B) : 𝟙_ D ⟶ F.obj (Da ⊗ B) :=
  cT F ev ≫ F.obj Da ◁ φ ≫ μ F Da B

/-- **`φ` is recovered from its section** by pairing with the pulled-back base evaluation. -/
theorem hom_eq_secHom (ev : Da ⊗ A ≅ 𝟙_ C) (hβ : (β_ A A).hom = 𝟙 _) {B : C}
    (φ : F.obj A ⟶ F.obj B) :
    (ρ_ (F.obj A)).inv ≫ F.obj A ◁ secHom F ev φ ≫ μ F A (Da ⊗ B) ≫ F.map (evBase ev B) = φ := by
  rw [map_evBase, secHom]
  have h := hom_eq_of_pair (cT F ev) (eT F ev) (cT_eT F ev) (braiding_obj_eq_id F hβ) φ
  simp only [whiskerLeft_comp, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.whiskerLeft_μ_δ_assoc]
  simpa only [whiskerLeft_comp, Category.assoc] using h

/-- Cancellation of the bookkeeping isomorphisms inside a transported section. -/
theorem secHom_transport_cancel (ev : Da ⊗ A ≅ 𝟙_ C) {B Av H : C} (iA : Av ≅ Da) (tH : H ≅ Av ⊗ B)
    (φ : F.obj A ⟶ F.obj B) :
    secHom F ev φ ≫ F.map (iA.inv ▷ B) ≫ F.map tH.inv ≫ F.map tH.hom ≫ F.map (iA.hom ▷ B) =
      secHom F ev φ := by
  rw [Iso.map_inv_hom_id_assoc, ← Functor.map_comp, ← comp_whiskerRight, Iso.inv_hom_id,
    id_whiskerRight, Functor.map_id, Category.comp_id]

/-- **`hom_eq_secHom` with the bookkeeping isomorphisms**, in the shape produced by `xiSectionMul` and
`pullbackTensorIso` on a total space: `Av ≅ Da` (`zpowNegOneIso`), `H ≅ Av ⊗ B` and `AH ≅ A ⊗ H`
(`tensorIsoTensorObj` on the base), `TH ≅ F A ⊗ F H` (`tensorIsoTensorObj` upstairs), `pT` with
`pT.inv = μ` (`pullbackTensorObjIso`). -/
theorem hom_eq_secHom_transport (ev : Da ⊗ A ≅ 𝟙_ C) (hβ : (β_ A A).hom = 𝟙 _) {B Av H AH : C}
    (iA : Av ≅ Da) (tH : H ≅ Av ⊗ B) (tAH : AH ≅ A ⊗ H) {TH : D} (tT : TH ≅ F.obj A ⊗ F.obj H)
    (pT : F.obj (A ⊗ H) ≅ F.obj A ⊗ F.obj H) (hpT : pT.inv = μ F A H)
    (φ : F.obj A ⟶ F.obj B) (q : 𝟙_ D ⟶ F.obj A) :
    (λ_ (𝟙_ D)).inv ≫ (q ⊗ₘ (secHom F ev φ ≫ F.map (iA.inv ▷ B) ≫ F.map tH.inv)) ≫ tT.inv ≫
      (F.mapIso tAH ≪≫ pT ≪≫ tT.symm).inv ≫
      F.map (tAH.hom ≫ A ◁ tH.hom ≫ A ◁ (iA.hom ▷ B) ≫ evBase ev B) = q ≫ φ := by
  rw [leftUnitor_inv_tensorHom_assoc]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, hpT, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  rw [← μ_natural_right_assoc, ← μ_natural_right_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [secHom_transport_cancel, hom_eq_secHom F ev hβ φ]

variable {Db B : C}

/-- The base pairing `(Da ⊗ B) ⊗ (Db ⊗ A) ⟶ 𝟙_C`: associator, `evBase evB A` in the middle, then `evA`. -/
def pairBase (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) : (Da ⊗ B) ⊗ (Db ⊗ A) ⟶ 𝟙_ C :=
  (α_ Da B (Db ⊗ A)).hom ≫ Da ◁ evBase evB A ≫ evA.hom

/-- `pairBase` as an isomorphism. -/
def pairBaseIso (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) : (Da ⊗ B) ⊗ (Db ⊗ A) ≅ 𝟙_ C :=
  α_ Da B (Db ⊗ A) ≪≫ whiskerLeftIso Da (evBaseIso evB A) ≪≫ evA

theorem pairBaseIso_hom (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) :
    (pairBaseIso evA evB).hom = pairBase evA evB := rfl

theorem map_pairBase_comp_η (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) :
    F.map (pairBase evA evB) ≫ η F =
      δ F (Da ⊗ B) (Db ⊗ A) ≫ δ F Da B ▷ F.obj (Db ⊗ A) ≫
        (α_ (F.obj Da) (F.obj B) (F.obj (Db ⊗ A))).hom ≫
        F.obj Da ◁ (F.obj B ◁ δ F Db A ≫ (α_ (F.obj B) (F.obj Db) (F.obj A)).inv ≫
          (β_ (F.obj B) (F.obj Db)).hom ▷ F.obj A ≫ eT F evB ▷ F.obj A ≫ (λ_ (F.obj A)).hom) ≫
        eT F evA := by
  simp only [pairBase, eT, Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_whiskerLeft, map_evBase, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    whiskerLeft_comp, Functor.Monoidal.whiskerLeft_μ_δ_assoc]

/-- **The product of the sections of `φ` and of its inverse `ψ` is the unit section** (paired by `pairBase`). -/
theorem pair_secHom_eq (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) (hβB : (β_ B B).hom = 𝟙 _)
    (φ : F.obj A ⟶ F.obj B) (ψ : F.obj B ⟶ F.obj A) (hφψ : φ ≫ ψ = 𝟙 _) :
    (λ_ (𝟙_ D)).inv ≫ (secHom F evA φ ⊗ₘ secHom F evB ψ) ≫ μ F (Da ⊗ B) (Db ⊗ A) ≫
      F.map (pairBase evA evB) = ε F := by
  rw [← cancel_mono (η F), Functor.Monoidal.ε_η]
  simp only [Category.assoc]
  rw [map_pairBase_comp_η]
  simp only [Functor.Monoidal.μ_δ_assoc]
  unfold secHom
  rw [tensorHom_comp_whiskerRight_cancel_assoc _ _ _ _ (Functor.Monoidal.μ_δ F Da B),
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
    Functor.Monoidal.μ_δ, whiskerLeft_id, Category.id_comp]
  exact pair_secHom_eq_id (cT F evA) (eT F evA) (cT_eT F evA) (cT F evB) (eT F evB) (cT_eT F evB)
    (braiding_obj_eq_id F hβB) φ ψ hφψ

/-- **`pair_secHom_eq` with the bookkeeping isomorphisms** (`Av ≅ Da`, `Bv ≅ Db`, `H ≅ Av ⊗ B`, `H' ≅ Bv ⊗ A`,
`HH' ≅ H ⊗ H'`, `TH ≅ F H ⊗ F H'`, `pT.inv = μ`). -/
theorem pair_secHom_transport (evA : Da ⊗ A ≅ 𝟙_ C) (evB : Db ⊗ B ≅ 𝟙_ C) (hβB : (β_ B B).hom = 𝟙 _)
    {Av Bv H H' HH' : C} (iA : Av ≅ Da) (iB : Bv ≅ Db) (tH : H ≅ Av ⊗ B) (tH' : H' ≅ Bv ⊗ A)
    (tHH' : HH' ≅ H ⊗ H') {TH : D} (tT : TH ≅ F.obj H ⊗ F.obj H')
    (pT : F.obj (H ⊗ H') ≅ F.obj H ⊗ F.obj H') (hpT : pT.inv = μ F H H')
    (φ : F.obj A ⟶ F.obj B) (ψ : F.obj B ⟶ F.obj A) (hφψ : φ ≫ ψ = 𝟙 _) :
    (λ_ (𝟙_ D)).inv ≫
      ((secHom F evA φ ≫ F.map (iA.inv ▷ B) ≫ F.map tH.inv) ⊗ₘ
        (secHom F evB ψ ≫ F.map (iB.inv ▷ A) ≫ F.map tH'.inv)) ≫
      tT.inv ≫ (F.mapIso tHH' ≪≫ pT ≪≫ tT.symm).inv ≫
      F.map (tHH'.hom ≫ (tH.hom ⊗ₘ tH'.hom) ≫ ((iA.hom ▷ B) ⊗ₘ (iB.hom ▷ A)) ≫ pairBase evA evB) =
      ε F := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, hpT, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  rw [← μ_natural_assoc, ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [secHom_transport_cancel, secHom_transport_cancel]
  exact pair_secHom_eq F evA evB hβB φ ψ hφψ

end Functorial

end CategoryTheory.MonoidalCategory.EvalCalculus
