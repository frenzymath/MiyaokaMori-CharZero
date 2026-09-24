import MiyaokaMori.Prelude

/-! # Projection formula for a monoidal adjunction

Abstract projection formula for a monoidal adjunction.

Setting: `F ⊣ G` an adjunction between monoidal categories, `F` oplax monoidal
(cotensorator `δ`, counit `η : F 𝟙 ⟶ 𝟙`). The comparison map

  `θ_{M,N} : M ⊗ G N ⟶ G (F M ⊗ N)`,   `θ := T(δ_{M, G N} ≫ (F M ◁ ε_N))`

(`T` = adjoint transpose, `ε` = counit of the adjunction) is the projection-formula map.
We prove: `θ` is natural in `M` and in `N`; it is multiplicative in `M`
(`θ_{M ⊗ M'}` factors through `M ◁ θ_{M'}` and `θ_M`); `θ_𝟙` is an isomorphism when `η` is;
and consequently `θ_M` is an isomorphism whenever `M` is invertible (`M ⊗ M' ≅ 𝟙 ≅ M' ⊗ M`)
and `δ_{M,M'}`, `δ_{M',M}`, `η` are isomorphisms.

Source: Stacks 01E8 (projection formula), "clear when E = O_Y^{⊕ n}"; the reduction from an
invertible `M` to the unit is the standard argument via the equivalence `M ⊗ −`.
Everything here is pure category theory (no schemes), so it compiles fast.
-/

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [instF : F.OplaxMonoidal]

/-- The projection-formula comparison map `M ⊗ G N ⟶ G (F M ⊗ N)`: adjoint transpose of
`δ_{M, G N} ≫ (F M ◁ ε_N)`. -/
noncomputable def projFormulaHom (M : C) (N : D) : M ⊗ G.obj N ⟶ G.obj (F.obj M ⊗ N) :=
  adj.homEquiv _ _ (δ F M (G.obj N) ≫ (F.obj M ◁ adj.counit.app N))

theorem homEquiv_symm_projFormulaHom (M : C) (N : D) :
    (adj.homEquiv _ _).symm (adj.projFormulaHom M N) =
      δ F M (G.obj N) ≫ (F.obj M ◁ adj.counit.app N) :=
  Equiv.symm_apply_apply _ _

/-- `θ` is natural in `M`. -/
theorem projFormulaHom_naturality_left {M M' : C} (g : M ⟶ M') (N : D) :
    (g ▷ G.obj N) ≫ adj.projFormulaHom M' N =
      adj.projFormulaHom M N ≫ G.map (F.map g ▷ N) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm,
    homEquiv_symm_projFormulaHom, homEquiv_symm_projFormulaHom, ← δ_natural_left_assoc,
    assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [whisker_exchange]

/-- `θ` is natural in `N`. -/
theorem projFormulaHom_naturality_right (M : C) {N N' : D} (h : N ⟶ N') :
    (M ◁ G.map h) ≫ adj.projFormulaHom M N' =
      adj.projFormulaHom M N ≫ G.map (F.obj M ◁ h) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm,
    homEquiv_symm_projFormulaHom, homEquiv_symm_projFormulaHom, ← δ_natural_right_assoc,
    assoc, ← whiskerLeft_comp, ← whiskerLeft_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [adj.counit_naturality]

/-- `θ` is multiplicative in `M`:
`θ_{M ⊗ M'} ≫ G(δ_{M,M'} ▷ N) ≫ G(α) = α ≫ (M ◁ θ_{M'}) ≫ θ_{M, F M' ⊗ N}`. -/
theorem projFormulaHom_tensor (M M' : C) (N : D) :
    adj.projFormulaHom (M ⊗ M') N ≫ G.map (δ F M M' ▷ N) ≫
        G.map (α_ (F.obj M) (F.obj M') N).hom =
      (α_ M M' (G.obj N)).hom ≫ (M ◁ adj.projFormulaHom M' N) ≫
        adj.projFormulaHom M (F.obj M' ⊗ N) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [← G.map_comp, homEquiv_naturality_right_symm, homEquiv_symm_projFormulaHom,
    homEquiv_naturality_left_symm, homEquiv_naturality_left_symm, homEquiv_symm_projFormulaHom,
    ← δ_natural_right_assoc, ← whiskerLeft_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [← adj.homEquiv_counit, homEquiv_symm_projFormulaHom, assoc, whisker_exchange_assoc,
    associator_naturality_right, associativity_assoc, whiskerLeft_comp]

/-- The unit case: `θ_𝟙 = (λ_ (G N)).hom ≫ G((λ_ N).inv ≫ (η⁻¹ ▷ N))`, when `η` is an iso. -/
theorem projFormulaHom_unit_eq [IsIso (η F)] (N : D) :
    adj.projFormulaHom (𝟙_ C) N =
      (λ_ (G.obj N)).hom ≫ G.map ((λ_ N).inv ≫ (inv (η F) ▷ N)) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_projFormulaHom, homEquiv_naturality_left_symm, adj.homEquiv_counit,
    adj.counit_naturality]
  have hδ : δ F (𝟙_ C) (G.obj N) =
      F.map (λ_ (G.obj N)).hom ≫ (λ_ (F.obj (G.obj N))).inv ≫ (inv (η F) ▷ F.obj (G.obj N)) := by
    rw [oplax_left_unitality F (G.obj N), assoc, assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
      F.map_id, id_comp, ← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight, comp_id]
  rw [hδ, assoc, assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

theorem isIso_projFormulaHom_unit [IsIso (η F)] (N : D) :
    IsIso (adj.projFormulaHom (𝟙_ C) N) := by
  rw [projFormulaHom_unit_eq]
  infer_instance

/-- Whiskering with `M'` is injective when `M ⊗ M' ≅ 𝟙`. -/
theorem whiskerLeft_injective_of_iso {M M' : C} (e : M ⊗ M' ≅ 𝟙_ C) {Z W : C} {u v : Z ⟶ W}
    (h : M' ◁ u = M' ◁ v) : u = v := by
  have key : ∀ w : Z ⟶ W, w = (λ_ Z).inv ≫ (e.inv ▷ Z) ≫ (α_ M M' Z).hom ≫ (M ◁ M' ◁ w) ≫
      (α_ M M' W).inv ≫ (e.hom ▷ W) ≫ (λ_ W).hom := by
    intro w
    rw [associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc, ← whisker_exchange_assoc,
      ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, id_comp,
      ← id_whiskerLeft_symm]
  rw [key u, key v, h]

/-- θ_{M⊗M'} is an isomorphism when `M ⊗ M' ≅ 𝟙` and `η` is an iso. -/
theorem isIso_projFormulaHom_of_iso_unit [IsIso (η F)] {P : C} (e : P ≅ 𝟙_ C) (N : D) :
    IsIso (adj.projFormulaHom P N) := by
  have := adj.isIso_projFormulaHom_unit N
  exact IsIso.of_isIso_fac_right (adj.projFormulaHom_naturality_left e.hom N).symm

/-- **Abstract projection formula.** If `M` is invertible (`e : M ⊗ M' ≅ 𝟙`, `e' : M' ⊗ M ≅ 𝟙`) and
`η`, `δ_{M,M'}`, `δ_{M',M}` are isomorphisms, then `θ_{M,N}` is an isomorphism for every `N`. -/
theorem isIso_projFormulaHom_of_invertible [IsIso (η F)] {M M' : C}
    (e : M ⊗ M' ≅ 𝟙_ C) (e' : M' ⊗ M ≅ 𝟙_ C)
    [IsIso (δ F M M')] [IsIso (δ F M' M)] (N : D) :
    IsIso (adj.projFormulaHom M N) := by
  -- from the multiplicativity for (M, M'): θ_{M, F M' ⊗ N₀} is a split epi for every N₀
  have hsplit : ∀ N₀ : D, IsSplitEpi (adj.projFormulaHom M (F.obj M' ⊗ N₀)) := by
    intro N₀
    have := adj.isIso_projFormulaHom_of_iso_unit e N₀
    have : IsIso ((M ◁ adj.projFormulaHom M' N₀) ≫ adj.projFormulaHom M (F.obj M' ⊗ N₀)) :=
      IsIso.of_isIso_fac_left (adj.projFormulaHom_tensor M M' N₀).symm
    exact IsSplitEpi.mk' ⟨inv ((M ◁ adj.projFormulaHom M' N₀) ≫
      adj.projFormulaHom M (F.obj M' ⊗ N₀)) ≫ (M ◁ adj.projFormulaHom M' N₀), by
        rw [assoc, IsIso.inv_hom_id]⟩
  -- from the multiplicativity for (M', M): M' ◁ θ_{M,N} is a split mono
  have hmono : IsSplitMono (M' ◁ adj.projFormulaHom M N) := by
    have := adj.isIso_projFormulaHom_of_iso_unit e' N
    have : IsIso ((M' ◁ adj.projFormulaHom M N) ≫ adj.projFormulaHom M' (F.obj M ⊗ N)) :=
      IsIso.of_isIso_fac_left (adj.projFormulaHom_tensor M' M N).symm
    exact IsSplitMono.mk' ⟨adj.projFormulaHom M' (F.obj M ⊗ N) ≫
      inv ((M' ◁ adj.projFormulaHom M N) ≫ adj.projFormulaHom M' (F.obj M ⊗ N)), by
        rw [← assoc, IsIso.hom_inv_id]⟩
  -- θ_{M,N} is mono
  have hM : Mono (adj.projFormulaHom M N) := by
    constructor
    intro Z u v huv
    apply whiskerLeft_injective_of_iso e
    rw [← cancel_mono (M' ◁ adj.projFormulaHom M N), ← whiskerLeft_comp, huv, whiskerLeft_comp]
  -- θ_{M,N} is a split epi: transport along N ≅ F M' ⊗ (F M ⊗ N)
  let κ : F.obj M' ⊗ (F.obj M ⊗ N) ⟶ N :=
    (α_ _ _ _).inv ≫ (inv (δ F M' M) ▷ N) ≫ (F.map e'.hom ▷ N) ≫ (η F ▷ N) ≫ (λ_ N).hom
  have : IsIso κ := by infer_instance
  have hE : IsSplitEpi (adj.projFormulaHom M N) := by
    have hnat := adj.projFormulaHom_naturality_right M κ
    have hθ : adj.projFormulaHom M N = inv (M ◁ G.map κ) ≫
        adj.projFormulaHom M (F.obj M' ⊗ (F.obj M ⊗ N)) ≫ G.map (F.obj M ◁ κ) := by
      rw [← hnat, IsIso.inv_hom_id_assoc]
    have := hsplit (F.obj M ⊗ N)
    rw [hθ]
    infer_instance
  exact isIso_of_mono_of_isSplitEpi _

end CategoryTheory.Adjunction
