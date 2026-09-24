import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # Functoriality of tensor powers and symmetric powers

Functoriality of tensor and symmetric powers: a morphism of modules `f : V ⟶ W` induces
`V^{⊗n} ⟶ W^{⊗n}` (`monoidalPowMap`, defined in `ProjectiveBundleUniversalProperty` together with its
compatibility `monoidalPowTransp_naturality` with adjacent transpositions; this file only adds the
functor laws) and `Sym^m V ⟶ Sym^m W` (`symPowMap`, descended along the quotient map), compatible with
the adjacent transpositions `monoidalPowTransp`, the concatenation `monoidalPowCat`, the quotient map
`symPowπ` and the multiplication `symPowMul`; it preserves identities and composition. We also record
the compatibility of `symPowMul` with the quotient map,
`(π_m ⊗ π_n) ≫ symPowMul = monoidalPowCat.hom ≫ π_{m+n}`.

Proof:
1. `monoidalPowMap f n` is recursive in `n`: `n = 0` is `𝟙`, `n+1` is `monoidalPowMap f n ⊗ₘ f`;
   preservation of identities and composition by induction on `n` (`id_tensorHom_id`,
   `tensorHom_comp_tensorHom`).
2. Compatibility with adjacent transpositions: `monoidalPowTransp_naturality`.
3. Compatibility with concatenation: induction on `n`; `n = 0` is naturality of the right unitor, `n+1`
   uses naturality of the inverse associator.
4. `symPowMap f m := symPowDesc V m (monoidalPowMap f m ≫ π_W)`; invariance follows from 2 and
   `monoidalPowTransp_symPowπ`. `π ≫ symPowMap = map ≫ π`; identities and composition by cancelling the
   epimorphism `π`.
5. `(π_m ⊗ π_n) ≫ symPowDesc₂ f = f`: eliminate the two "curry–descend–uncurry" steps of `symPowDesc₂`
   with `symPowπ_whiskerRight_descCurry`; the two braidings cancel by symmetry. As a special case, the
   compatibility of `symPowMul` with `π`.
6. `π_m ⊗ π_n` is an epimorphism (`symPowπ_whiskerRight_cancel` plus a braiding); precomposing both sides
   with `π ⊗ π` and comparing via 5, 4, 3 gives `symPowMul_symPowMap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

section general
variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem aux_cat_succ {A A' B B' Q Q' V V' : C} (mm : A ⟶ A') (mn : B ⟶ B') (f : V ⟶ V')
    (c : A ⊗ B ⟶ Q) (c' : A' ⊗ B' ⟶ Q') (q : Q ⟶ Q') (ih : (mm ⊗ₘ mn) ≫ c' = c ≫ q) :
    (mm ⊗ₘ (mn ⊗ₘ f)) ≫ (α_ A' B' V').inv ≫ (c' ▷ V') =
      ((α_ A B V).inv ≫ (c ▷ V)) ≫ (q ⊗ₘ f) := by
  rw [MonoidalCategory.associator_inv_naturality_assoc, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ih, Category.assoc,
    ← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

end general


namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem monoidalPowMap_zero {V W : X.Modules} (f : V ⟶ W) : monoidalPowMap f 0 = 𝟙 _ := rfl

theorem monoidalPowMap_succ {V W : X.Modules} (f : V ⟶ W) (n : ℕ) :
    monoidalPowMap f (n + 1) = monoidalPowMap f n ⊗ₘ f := rfl

theorem monoidalPowMap_id (V : X.Modules) : ∀ n, monoidalPowMap (𝟙 V) n = 𝟙 (monoidalPow V n)
  | 0 => rfl
  | n + 1 => by
    show monoidalPowMap (𝟙 V) n ⊗ₘ 𝟙 V = 𝟙 (monoidalPow V n ⊗ V)
    rw [monoidalPowMap_id V n]
    exact MonoidalCategory.id_tensorHom_id _ _

theorem monoidalPowMap_comp {U V W : X.Modules} (f : U ⟶ V) (g : V ⟶ W) :
    ∀ n, monoidalPowMap (f ≫ g) n = monoidalPowMap f n ≫ monoidalPowMap g n
  | 0 => by
    show 𝟙 (𝟙_ X.Modules) = 𝟙 (𝟙_ X.Modules) ≫ 𝟙 (𝟙_ X.Modules)
    rw [Category.id_comp]
  | n + 1 => by
    show monoidalPowMap (f ≫ g) n ⊗ₘ (f ≫ g) = (monoidalPowMap f n ⊗ₘ f) ≫ (monoidalPowMap g n ⊗ₘ g)
    rw [monoidalPowMap_comp f g n, MonoidalCategory.tensorHom_comp_tensorHom]

/-- Concatenation is compatible with functoriality. -/
theorem monoidalPowCat_monoidalPowMap {V W : X.Modules} (f : V ⟶ W) (m : ℕ) :
    ∀ n, (monoidalPowMap f m ⊗ₘ monoidalPowMap f n) ≫ (monoidalPowCat W m n).hom =
      (monoidalPowCat V m n).hom ≫ monoidalPowMap f (m + n)
  | 0 => by
    show (monoidalPowMap f m ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ (monoidalPow W m)).hom =
      (ρ_ (monoidalPow V m)).hom ≫ monoidalPowMap f m
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.rightUnitor_naturality]
  | n + 1 => by
    show (monoidalPowMap f m ⊗ₘ (monoidalPowMap f n ⊗ₘ f)) ≫
        ((α_ (monoidalPow W m) (monoidalPow W n) W).inv ≫ (monoidalPowCat W m n).hom ▷ W) =
      ((α_ (monoidalPow V m) (monoidalPow V n) V).inv ≫ (monoidalPowCat V m n).hom ▷ V) ≫
        (monoidalPowMap f (m + n) ⊗ₘ f)
    exact aux_cat_succ _ _ _ _ _ _ (monoidalPowCat_monoidalPowMap f m n)

/-- Functoriality of symmetric powers `Sym^m V ⟶ Sym^m W` (descended along the quotient map). -/
def symPowMap {V W : X.Modules} (f : V ⟶ W) (m : ℕ) : symPow V m ⟶ symPow W m :=
  symPowDesc V m (monoidalPowMap f m ≫ symPowπ W m) (fun i => by
    rw [← Category.assoc, monoidalPowTransp_naturality, Category.assoc,
      monoidalPowTransp_symPowπ W m i i.2])

@[reassoc]
theorem symPowπ_symPowMap {V W : X.Modules} (f : V ⟶ W) (m : ℕ) :
    symPowπ V m ≫ symPowMap f m = monoidalPowMap f m ≫ symPowπ W m :=
  symPowπ_desc _ _ _ _

theorem symPowMap_id (V : X.Modules) (m : ℕ) : symPowMap (𝟙 V) m = 𝟙 (symPow V m) := by
  rw [← cancel_epi (symPowπ V m), symPowπ_symPowMap, monoidalPowMap_id, Category.id_comp,
    Category.comp_id]

theorem symPowMap_comp {U V W : X.Modules} (f : U ⟶ V) (g : V ⟶ W) (m : ℕ) :
    symPowMap (f ≫ g) m = symPowMap f m ≫ symPowMap g m := by
  rw [← cancel_epi (symPowπ U m), symPowπ_symPowMap, monoidalPowMap_comp, symPowπ_symPowMap_assoc,
    symPowπ_symPowMap, Category.assoc]

/-- An isomorphism induces an isomorphism of symmetric powers. -/
def symPowMapIso {V W : X.Modules} (e : V ≅ W) (m : ℕ) : symPow V m ≅ symPow W m where
  hom := symPowMap e.hom m
  inv := symPowMap e.inv m
  hom_inv_id := by rw [← symPowMap_comp, e.hom_inv_id, symPowMap_id]
  inv_hom_id := by rw [← symPowMap_comp, e.inv_hom_id, symPowMap_id]

/-- Computation rule for the two-variable descent: `(π_m ⊗ π_n) ≫ symPowDesc₂ f = f`. -/
theorem symPowπ_tensor_symPowDesc₂ (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (f : monoidalPow V m ⊗ monoidalPow V n ⟶ T)
    (hf₁ : ∀ i : Fin m, (monoidalPowTransp V m i ▷ monoidalPow V n) ≫ f = f)
    (hf₂ : ∀ j : Fin n, (monoidalPow V m ◁ monoidalPowTransp V n j) ≫ f = f) :
    (symPowπ V m ⊗ₘ symPowπ V n) ≫ symPowDesc₂ V m n f hf₁ hf₂ = f := by
  unfold symPowDesc₂
  simp only []
  rw [BraidedCategory.braiding_naturality_assoc, MonoidalCategory.tensorHom_def', Category.assoc,
    symPowπ_whiskerRight_descCurry, BraidedCategory.braiding_naturality_right_assoc,
    symPowπ_whiskerRight_descCurry, SymmetricCategory.symmetry_assoc]

/-- `symPowMul` is compatible with the quotient map. -/
theorem symPowπ_tensor_symPowMul (V : X.Modules) (m n : ℕ) :
    (symPowπ V m ⊗ₘ symPowπ V n) ≫ symPowMul V m n =
      (monoidalPowCat V m n).hom ≫ symPowπ V (m + n) :=
  symPowπ_tensor_symPowDesc₂ V m n _ _ _

/-- `π_m ⊗ π_n` is an epimorphism. -/
theorem symPowπ_tensor_cancel (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (x y : symPow V m ⊗ symPow V n ⟶ T)
    (h : (symPowπ V m ⊗ₘ symPowπ V n) ≫ x = (symPowπ V m ⊗ₘ symPowπ V n) ≫ y) : x = y := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc] at h
  have h' := symPowπ_whiskerRight_cancel V m _ _ _ h
  have h'' : (symPowπ V n ▷ symPow V m) ≫ ((β_ _ _).hom ≫ x) =
      (symPowπ V n ▷ symPow V m) ≫ ((β_ _ _).hom ≫ y) := by
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc, h',
      ← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]
  exact (cancel_epi (β_ _ _).hom).1 (symPowπ_whiskerRight_cancel V n _ _ _ h'')

/-- The multiplication of symmetric powers is compatible with functoriality. -/
theorem symPowMul_symPowMap {V W : X.Modules} (f : V ⟶ W) (m n : ℕ) :
    symPowMul V m n ≫ symPowMap f (m + n) =
      (symPowMap f m ⊗ₘ symPowMap f n) ≫ symPowMul W m n := by
  apply symPowπ_tensor_cancel
  rw [← Category.assoc, symPowπ_tensor_symPowMul, Category.assoc, symPowπ_symPowMap,
    ← Category.assoc (symPowπ V m ⊗ₘ symPowπ V n), MonoidalCategory.tensorHom_comp_tensorHom,
    symPowπ_symPowMap, symPowπ_symPowMap, ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc, symPowπ_tensor_symPowMul, ← Category.assoc, ← monoidalPowCat_monoidalPowMap,
    Category.assoc]

end AlgebraicGeometry.Scheme.Modules

end
