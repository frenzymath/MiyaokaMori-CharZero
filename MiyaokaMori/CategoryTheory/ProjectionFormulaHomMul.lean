import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.ModulesProjectionFormulaHomAbstract

/-! # The projection-formula map is multiplicative

**The projection-formula map is compatible with multiplication** (abstract form). For a monoidal adjunction
`F ⊣ G` with `F` strong monoidal and braided, `G` lax monoidal with the compatibility
`homEquiv (δ_{M,N}) = (η_M ⊗ η_N) ≫ μ_G` (this is `Modules.homEquiv_pullbackTensorObjHom` for `f^* ⊣ f_*`),
and `θ_{M,N} := projFormulaHom` the projection-formula map, writing `a_M := θ_{M,𝟙} ≫ G(ρ_{FM}) : M ⊗ G𝟙 ⟶ G(FM)`
("`m ⊗ f ↦ f · Fm`") and `w := μ_G(𝟙,𝟙) ≫ G(λ_𝟙) : G𝟙 ⊗ G𝟙 ⟶ G𝟙` (the multiplication of `G𝟙`):

  `(a_M ⊗ₘ a_{M'}) ≫ μ_G(FM, FM') ≫ G(μ_F(M, M')) = tensorμ ≫ ((M ⊗ M') ◁ w) ≫ a_{M ⊗ M'}`.

Source: monoidal coherence; the concrete instance is the multiplicativity of the projection formula
`M ⊗ f_*O ⟶ f_*f^*M` for `f^* ⊣ f_*` on sheaves of modules (Stacks 01E8), needed for the convolution formula of
ξ-coefficients (`xiSectionMul_xiMonomial_xiMonomial`).

Proof: transpose both sides along `homEquiv` (injective). `homEquiv.symm (μ_G A B) = δ_{GA,GB} ≫ (ε_A ⊗ ε_B)`
(`homEquiv_symm_μ`, from the compatibility hypothesis, `μ_natural` and the right triangle identity), so the left side
transposes to `δ ≫ (δ ⊗ δ) ≫ (((FM ◁ ε) ≫ ρ) ⊗ ((FM' ◁ ε) ≫ ρ)) ≫ μ_F` and the right side to
`F(tensorμ) ≫ δ ≫ (F(M⊗M') ◁ (δ ≫ (ε ⊗ ε) ≫ λ)) ≫ ρ`; `tensorμ_comp_μ_tensorHom_μ_comp_μ` (F lax braided) turns
`F(tensorμ) ≫ δ ≫ (δ ⊗ δ)` into `δ ≫ (δ ⊗ δ) ≫ tensorμ`, and what remains is the coherence identity
`tensorμ X 𝟙 Y 𝟙 ≫ ((X ⊗ Y) ◁ λ_𝟙) ≫ ρ_{X⊗Y} = ρ_X ⊗ ρ_Y` (`tensorμ_unit_unit`, from `braiding_rightUnitor` and the
`monoidal` coherence tactic) plus naturality of `tensorμ` and `ρ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

/-- `tensorμ X 𝟙 Y 𝟙 ≫ ((X ⊗ Y) ◁ λ_𝟙) ≫ ρ_{X ⊗ Y} = ρ_X ⊗ ρ_Y` (coherence; the braiding `β_{𝟙,Y}` is `λ_Y ≫ ρ_Y⁻¹`). -/
@[reassoc]
theorem tensorμ_unit_unit (X Y : C) :
    tensorμ X (𝟙_ C) Y (𝟙_ C) ≫ ((X ⊗ Y) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X ⊗ Y)).hom = (ρ_ X).hom ⊗ₘ (ρ_ Y).hom := by
  have hβ : (β_ (𝟙_ C) Y).hom = (λ_ Y).hom ≫ (ρ_ Y).inv := by
    rw [← braiding_rightUnitor, assoc, Iso.hom_inv_id, comp_id]
  simp only [tensorμ, hβ]
  monoidal

/-- The coherence core of `projFormulaHom_mul`: for `e : A ⟶ 𝟙`, `e' : B ⟶ 𝟙` and `m : X ⊗ Y ⟶ Z`,
`(((X ◁ e) ≫ ρ) ⊗ ((Y ◁ e') ≫ ρ)) ≫ m = tensorμ ≫ (m ⊗ ((e ⊗ e') ≫ λ)) ≫ ρ`. -/
theorem tensorμ_counit_core {X Y Z A B : C} (e : A ⟶ 𝟙_ C) (e' : B ⟶ 𝟙_ C) (m : X ⊗ Y ⟶ Z) :
    (((X ◁ e) ≫ (ρ_ X).hom) ⊗ₘ ((Y ◁ e') ≫ (ρ_ Y).hom)) ≫ m =
      tensorμ X A Y B ≫ (m ⊗ₘ ((e ⊗ₘ e') ≫ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ Z).hom := by
  have h1 : (m ⊗ₘ ((e ⊗ₘ e') ≫ (λ_ (𝟙_ C)).hom)) = ((𝟙 X ⊗ₘ 𝟙 Y) ⊗ₘ (e ⊗ₘ e')) ≫ (m ⊗ₘ (λ_ (𝟙_ C)).hom) := by
    rw [tensorHom_comp_tensorHom, id_tensorHom_id, id_comp]
  have h2 : ((𝟙 X ⊗ₘ e) ⊗ₘ (𝟙 Y ⊗ₘ e')) ≫ tensorμ X (𝟙_ C) Y (𝟙_ C) =
      tensorμ X A Y B ≫ ((𝟙 X ⊗ₘ 𝟙 Y) ⊗ₘ (e ⊗ₘ e')) := tensorμ_natural (𝟙 X) e (𝟙 Y) e'
  have h3 : (m ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (ρ_ Z).hom = ((X ⊗ Y) ◁ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (X ⊗ Y)).hom ≫ m := by
    rw [tensorHom_def', assoc, rightUnitor_naturality]
  rw [h1, assoc, ← assoc (tensorμ X A Y B), ← h2, assoc, h3, tensorμ_unit_unit_assoc, ← assoc,
    tensorHom_comp_tensorHom, id_tensorHom, id_tensorHom]

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

section LaxTranspose

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal]

/-- The transpose of the lax structure of `G`: `homEquiv.symm (μ_G A B) = δ_{GA,GB} ≫ (ε_A ⊗ ε_B)`, given
`homEquiv δ_{M,N} = (η_M ⊗ η_N) ≫ μ_G`. -/
theorem homEquiv_symm_μ
    (hμ : ∀ M N : C, adj.homEquiv _ _ (δ F M N) = (adj.unit.app M ⊗ₘ adj.unit.app N) ≫ μ G (F.obj M) (F.obj N))
    (A B : D) :
    (adj.homEquiv _ _).symm (μ G A B) = δ F (G.obj A) (G.obj B) ≫ (adj.counit.app A ⊗ₘ adj.counit.app B) := by
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_right, hμ, assoc, ← μ_natural, ← assoc,
    tensorHom_comp_tensorHom, adj.right_triangle_components, adj.right_triangle_components]
  simp

end LaxTranspose

section Mul

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided] [G.LaxMonoidal]

/-- **Multiplicativity of the projection-formula map** (see the module docstring). -/
theorem projFormulaHom_mul
    (hμ : ∀ M N : C, adj.homEquiv _ _ (δ F M N) = (adj.unit.app M ⊗ₘ adj.unit.app N) ≫ μ G (F.obj M) (F.obj N))
    (M M' : C) :
    ((adj.projFormulaHom M (𝟙_ D) ≫ G.map (ρ_ (F.obj M)).hom) ⊗ₘ
        (adj.projFormulaHom M' (𝟙_ D) ≫ G.map (ρ_ (F.obj M')).hom)) ≫
      μ G (F.obj M) (F.obj M') ≫ G.map (μ F M M') =
    tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D)) ≫
      ((M ⊗ M') ◁ (μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom)) ≫
      adj.projFormulaHom (M ⊗ M') (𝟙_ D) ≫ G.map (ρ_ (F.obj (M ⊗ M'))).hom := by
  apply (adj.homEquiv _ _).symm.injective
  -- transposes of the two factors
  have ha : ∀ P : C, (adj.homEquiv _ _).symm (adj.projFormulaHom P (𝟙_ D) ≫ G.map (ρ_ (F.obj P)).hom) =
      δ F P (G.obj (𝟙_ D)) ≫ (F.obj P ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ (F.obj P)).hom := by
    intro P
    rw [homEquiv_naturality_right_symm, homEquiv_symm_projFormulaHom, assoc]
  have hfa : ∀ P : C, F.map (adj.projFormulaHom P (𝟙_ D) ≫ G.map (ρ_ (F.obj P)).hom) ≫ adj.counit.app (F.obj P) =
      δ F P (G.obj (𝟙_ D)) ≫ (F.obj P ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ (F.obj P)).hom :=
    fun P => (adj.homEquiv_counit _ _ _).symm.trans (ha P)
  have hw : (adj.homEquiv _ _).symm (μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom) =
      δ F (G.obj (𝟙_ D)) (G.obj (𝟙_ D)) ≫ (adj.counit.app (𝟙_ D) ⊗ₘ adj.counit.app (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom := by
    rw [homEquiv_naturality_right_symm, homEquiv_symm_μ adj hμ, assoc]
  have hfw : F.map (μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom) ≫ adj.counit.app (𝟙_ D) =
      δ F (G.obj (𝟙_ D)) (G.obj (𝟙_ D)) ≫ (adj.counit.app (𝟙_ D) ⊗ₘ adj.counit.app (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom :=
    (adj.homEquiv_counit _ _ _).symm.trans hw
  -- left side
  have hL : (adj.homEquiv _ _).symm
      (((adj.projFormulaHom M (𝟙_ D) ≫ G.map (ρ_ (F.obj M)).hom) ⊗ₘ
        (adj.projFormulaHom M' (𝟙_ D) ≫ G.map (ρ_ (F.obj M')).hom)) ≫
        μ G (F.obj M) (F.obj M') ≫ G.map (μ F M M')) =
      δ F (M ⊗ G.obj (𝟙_ D)) (M' ⊗ G.obj (𝟙_ D)) ≫ (δ F M (G.obj (𝟙_ D)) ⊗ₘ δ F M' (G.obj (𝟙_ D))) ≫
        (((F.obj M ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ (F.obj M)).hom) ⊗ₘ
          ((F.obj M' ◁ adj.counit.app (𝟙_ D)) ≫ (ρ_ (F.obj M')).hom)) ≫ μ F M M' := by
    rw [← assoc, homEquiv_naturality_right_symm, homEquiv_naturality_left_symm, homEquiv_symm_μ adj hμ]
    simp only [assoc]
    rw [← δ_natural_assoc, tensorHom_comp_tensorHom_assoc, hfa, hfa, ← tensorHom_comp_tensorHom_assoc]
  -- right side
  have hR : (adj.homEquiv _ _).symm
      (tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D)) ≫
        ((M ⊗ M') ◁ (μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom)) ≫
        adj.projFormulaHom (M ⊗ M') (𝟙_ D) ≫ G.map (ρ_ (F.obj (M ⊗ M'))).hom) =
      F.map (tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D))) ≫ δ F (M ⊗ M') (G.obj (𝟙_ D) ⊗ G.obj (𝟙_ D)) ≫
        (F.obj (M ⊗ M') ◁ (δ F (G.obj (𝟙_ D)) (G.obj (𝟙_ D)) ≫
          (adj.counit.app (𝟙_ D) ⊗ₘ adj.counit.app (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom)) ≫
        (ρ_ (F.obj (M ⊗ M'))).hom := by
    rw [homEquiv_naturality_left_symm, homEquiv_naturality_left_symm, homEquiv_naturality_right_symm,
      homEquiv_symm_projFormulaHom]
    simp only [assoc]
    rw [← δ_natural_right_assoc, ← whiskerLeft_comp_assoc, hfw]
  rw [hL, hR]
  -- braided compatibility of δ with tensorμ: F(tensorμ) ≫ δ ≫ (δ ⊗ δ) = δ ≫ (δ ⊗ δ) ≫ tensorμ
  have hT : F.map (tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D))) ≫ δ F (M ⊗ M') (G.obj (𝟙_ D) ⊗ G.obj (𝟙_ D)) ≫
      (δ F M M' ⊗ₘ δ F (G.obj (𝟙_ D)) (G.obj (𝟙_ D))) =
      δ F (M ⊗ G.obj (𝟙_ D)) (M' ⊗ G.obj (𝟙_ D)) ≫ (δ F M (G.obj (𝟙_ D)) ⊗ₘ δ F M' (G.obj (𝟙_ D))) ≫
        tensorμ (F.obj M) (F.obj (G.obj (𝟙_ D))) (F.obj M') (F.obj (G.obj (𝟙_ D))) := by
    have h := tensorμ_comp_μ_tensorHom_μ_comp_μ F M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D))
    have hinv : δ F (M ⊗ G.obj (𝟙_ D)) (M' ⊗ G.obj (𝟙_ D)) ≫ (δ F M (G.obj (𝟙_ D)) ⊗ₘ δ F M' (G.obj (𝟙_ D))) ≫
        (μ F M (G.obj (𝟙_ D)) ⊗ₘ μ F M' (G.obj (𝟙_ D))) ≫ μ F (M ⊗ G.obj (𝟙_ D)) (M' ⊗ G.obj (𝟙_ D)) = 𝟙 _ := by
      rw [tensorHom_comp_tensorHom_assoc, Functor.Monoidal.δ_μ, Functor.Monoidal.δ_μ, id_tensorHom_id, id_comp,
        Functor.Monoidal.δ_μ]
    rw [← id_comp (F.map (tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D)))), ← hinv]
    simp only [assoc]
    rw [← reassoc_of% h, Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom, Functor.Monoidal.μ_δ,
      Functor.Monoidal.μ_δ, id_tensorHom_id, comp_id]
  -- insert (δ ⊗ δ) ≫ (μ ⊗ μ) = 𝟙 after the second δ on the right, then use hT
  have hins : F.map (tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D))) ≫ δ F (M ⊗ M') (G.obj (𝟙_ D) ⊗ G.obj (𝟙_ D)) ≫
      (F.obj (M ⊗ M') ◁ (δ F (G.obj (𝟙_ D)) (G.obj (𝟙_ D)) ≫
        (adj.counit.app (𝟙_ D) ⊗ₘ adj.counit.app (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom)) ≫ (ρ_ (F.obj (M ⊗ M'))).hom =
      δ F (M ⊗ G.obj (𝟙_ D)) (M' ⊗ G.obj (𝟙_ D)) ≫ (δ F M (G.obj (𝟙_ D)) ⊗ₘ δ F M' (G.obj (𝟙_ D))) ≫
        tensorμ (F.obj M) (F.obj (G.obj (𝟙_ D))) (F.obj M') (F.obj (G.obj (𝟙_ D))) ≫
        (μ F M M' ⊗ₘ ((adj.counit.app (𝟙_ D) ⊗ₘ adj.counit.app (𝟙_ D)) ≫ (λ_ (𝟙_ D)).hom)) ≫
        (ρ_ (F.obj (M ⊗ M'))).hom := by
    rw [← reassoc_of% hT, tensorHom_comp_tensorHom_assoc, Functor.Monoidal.δ_μ, id_tensorHom]
  rw [hins]
  congr 1
  congr 1
  exact tensorμ_counit_core (adj.counit.app (𝟙_ D)) (adj.counit.app (𝟙_ D)) (μ F M M')

/-- **Multiplicativity, general form used for the monomial product rule.** Given `u : T ⟶ G𝟙`, `v : T' ⟶ G𝟙`,
`W : T ⊗ T' ⟶ T''`, `u'' : T'' ⟶ G𝟙` with `(u ⊗ v) ≫ w = W ≫ u''` (`w := μ_G(𝟙,𝟙) ≫ G(λ)` the multiplication of `G𝟙`),
and an isomorphism `τ : N ≅ M ⊗ M'`:
`(((M ◁ u) ≫ a_M) ⊗ ((M' ◁ v) ≫ a_{M'})) ≫ μ_G ≫ G(μ_F ≫ F(τ⁻¹)) = tensorμ ≫ (τ⁻¹ ⊗ W) ≫ (N ◁ u'') ≫ a_N`
(`a_P := θ_{P,𝟙} ≫ G(ρ_{FP})`). Proof: `(τ⁻¹ ⊗ W) ≫ (N ◁ u'') = ((M ⊗ M') ◁ (W ≫ u'')) ≫ (τ⁻¹ ▷ G𝟙)`, move `τ⁻¹` through
`θ` (`projFormulaHom_naturality_left`) and `ρ`, replace `W ≫ u''` by `(u ⊗ v) ≫ w`, pull `u ⊗ v` in front of `tensorμ`
(`tensorμ_natural`) and apply `projFormulaHom_mul`. -/
theorem projFormulaHom_mul_general
    (hμ : ∀ M N : C, adj.homEquiv _ _ (δ F M N) = (adj.unit.app M ⊗ₘ adj.unit.app N) ≫ μ G (F.obj M) (F.obj N))
    {M M' N T T' T'' : C} (τ : N ≅ M ⊗ M') (u : T ⟶ G.obj (𝟙_ D)) (v : T' ⟶ G.obj (𝟙_ D))
    (W : T ⊗ T' ⟶ T'') (u'' : T'' ⟶ G.obj (𝟙_ D))
    (hW : (u ⊗ₘ v) ≫ μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom = W ≫ u'') :
    (((M ◁ u) ≫ adj.projFormulaHom M (𝟙_ D) ≫ G.map (ρ_ (F.obj M)).hom) ⊗ₘ
        ((M' ◁ v) ≫ adj.projFormulaHom M' (𝟙_ D) ≫ G.map (ρ_ (F.obj M')).hom)) ≫
      μ G (F.obj M) (F.obj M') ≫ G.map (μ F M M' ≫ F.map τ.inv) =
    tensorμ M T M' T' ≫ (τ.inv ⊗ₘ W) ≫ (N ◁ u'') ≫
      adj.projFormulaHom N (𝟙_ D) ≫ G.map (ρ_ (F.obj N)).hom := by
  -- right side: move τ⁻¹ to the end
  have h1 : (τ.inv ⊗ₘ W) ≫ (N ◁ u'') = ((M ⊗ M') ◁ (W ≫ u'')) ≫ (τ.inv ▷ G.obj (𝟙_ D)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, comp_id, ← tensorHom_id, ← id_tensorHom,
      tensorHom_comp_tensorHom, id_comp, comp_id]
  have h2 : (τ.inv ▷ G.obj (𝟙_ D)) ≫ adj.projFormulaHom N (𝟙_ D) ≫ G.map (ρ_ (F.obj N)).hom =
      adj.projFormulaHom (M ⊗ M') (𝟙_ D) ≫ G.map ((ρ_ (F.obj (M ⊗ M'))).hom ≫ F.map τ.inv) := by
    rw [← assoc, adj.projFormulaHom_naturality_left, assoc, ← G.map_comp, rightUnitor_naturality]
  have h3 : tensorμ M T M' T' ≫ ((M ⊗ M') ◁ ((u ⊗ₘ v) ≫ μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom)) =
      ((M ◁ u) ⊗ₘ (M' ◁ v)) ≫ tensorμ M (G.obj (𝟙_ D)) M' (G.obj (𝟙_ D)) ≫
        ((M ⊗ M') ◁ (μ G (𝟙_ D) (𝟙_ D) ≫ G.map (λ_ (𝟙_ D)).hom)) := by
    have := tensorμ_natural (𝟙 M) u (𝟙 M') v
    rw [id_tensorHom_id, id_tensorHom, id_tensorHom, id_tensorHom] at this
    rw [whiskerLeft_comp, ← assoc, ← this]
    simp only [assoc]
  have hmul := adj.projFormulaHom_mul hμ M M'
  rw [reassoc_of% h1, h2, ← hW, reassoc_of% h3]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hmul, ← tensorHom_comp_tensorHom_assoc]

end Mul

end CategoryTheory.Adjunction

namespace CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

/-- **Variable-level assembly for the monomial product rule.** With `Φ := cmi⁻¹ ≫ τ ≫ f` the "monomial maps",
`(fa ⊗ fb) ≫ g = tensorμ ≫ (τ⁻¹ ⊗ W) ≫ fN` (the multiplicativity of the projection formula) gives
`τAA'.hom ≫ (Φa ⊗ Φb) ≫ g = tCH ≫ ΦN` where `tCH = τAA'.hom ≫ ((cmiA⁻¹ ≫ τa) ⊗ (cmiB⁻¹ ≫ τb)) ≫ tensorμ ≫ (τ⁻¹ ⊗ W) ≫ τN⁻¹ ≫ cmiN`. -/
theorem monomial_mul_bridge {A A' P P' PA PN AN M M' Ta Tb Tab N Q Q' Q'' : C}
    (τAA' : PA ≅ A ⊗ A') (cmiA : P ≅ A) (τa : P ≅ M ⊗ Ta) (fa : M ⊗ Ta ⟶ Q)
    (cmiB : P' ≅ A') (τb : P' ≅ M' ⊗ Tb) (fb : M' ⊗ Tb ⟶ Q') (g : Q ⊗ Q' ⟶ Q'')
    (τ : N ≅ M ⊗ M') (W : Ta ⊗ Tb ⟶ Tab)
    (τN : PN ≅ N ⊗ Tab) (cmiN : PN ≅ AN) (fN : N ⊗ Tab ⟶ Q'')
    (hgen : (fa ⊗ₘ fb) ≫ g = tensorμ M Ta M' Tb ≫ (τ.inv ⊗ₘ W) ≫ fN) :
    τAA'.hom ≫ ((cmiA.inv ≫ τa.hom ≫ fa) ⊗ₘ (cmiB.inv ≫ τb.hom ≫ fb)) ≫ g =
      (τAA'.hom ≫ ((cmiA.inv ≫ τa.hom) ⊗ₘ (cmiB.inv ≫ τb.hom)) ≫ tensorμ M Ta M' Tb ≫
          (τ.inv ⊗ₘ W) ≫ τN.inv ≫ cmiN.hom) ≫
        (cmiN.inv ≫ τN.hom ≫ fN) := by
  simp only [assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← hgen]
  simp only [tensorHom_comp_tensorHom_assoc, assoc]

end CategoryTheory.MonoidalCategory
