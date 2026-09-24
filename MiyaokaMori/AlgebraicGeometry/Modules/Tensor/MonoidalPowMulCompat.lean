import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.SymPowMap

/-! # Multiplicativity of the tensor power constructions

Multiplicativity of the three "tensor power" constructions of `ProjectiveBundleUniversalProperty` with respect
to the concatenation isomorphisms `monoidalPowCat V m n : V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗(m+n)}`:

* (a) `pullbackMonoidalPow_monoidalPowCat`: `g^*(cat_W m n) ≫ pullbackMonoidalPow g W (m+n)
      = δ ≫ (pullbackMonoidalPow g W m ⊗ₘ pullbackMonoidalPow g W n) ≫ cat_{g^*W} m n`
  (induction on `n`; `n = 0` is the oplax right unitality of `g^*`, `n+1` is oplax associativity +
  `δ_natural_left`);
* (b) `monoidalPowCat_monoidalPowMap` (already in `SymPowMap`): `monoidalPowMap ψ` is multiplicative;
* (c) `unitPowCollapse_monoidalPowCat`: `cat_𝟙 m n ≫ unitPowCollapse (m+n)
      = (unitPowCollapse m ⊗ₘ unitPowCollapse n) ≫ (λ_ 𝟙).hom`
  (induction on `n`; `n = 0` is `unitors_equal` + right unitor naturality, `n+1` is the triangle identity).

Chaining them with `symPowMul`'s defining property `(π_m ⊗ₘ π_n) ≫ symPowMul = cat.hom ≫ π_{m+n}`
(`tensorHom_symPowπ_symPowMul`) gives the **multiplicativity of the pulled-back symmetric-power descent**
for a functional `ψ : g^*W ⟶ O_T` (`pullback_map_symPowMul_symPowPullbackDesc`):
  `g^*(symPowMul W m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ (λ_ O_T).hom`,
  `Ψ_m := symPowPullbackDesc g ψ m ≫ unitPowCollapse T m : g^*(Sym^m W) ⟶ O_T`.
The two sides are compared after transposing along `g^* ⊣ g_*` and cancelling the epimorphism `π_m ⊗ₘ π_n`
(`symPowπ_tensorHom_cancel`), which avoids any "left adjoints preserve epis" instance.

The abstract monoidal lemmas are stated for an arbitrary (oplax monoidal) functor and applied with `exact`,
so that no rewriting has to see through the recursive definitions `monoidalPow`/`monoidalPowCat`.

Source: Stacks 01LQ / 01M2 (maps out of a symmetric algebra are determined degreewise and are multiplicative
on the tensor-power presentation). Used for the multiplicativity of the algebra map of the total space
induced by a functional, and in `projBundle.localRingHomComponent_mul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u u' v' w v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-! ## Abstract monoidal lemmas -/

namespace AlgebraicGeometry.Scheme.Modules.MonoidalPowAux

open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]

theorem rightUnitor_comp_to_unit {P : C} (a : P ⟶ 𝟙_ C) :
    (ρ_ P).hom ≫ a = (a ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom := by
  rw [tensorHom_id, unitors_equal, rightUnitor_naturality]

theorem unit_assoc_collapse :
    (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).hom ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom =
      (𝟙_ C ◁ (λ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom := by
  monoidal

theorem collapse_step {P Q R : C} (c : P ⊗ Q ⟶ R) (a : P ⟶ 𝟙_ C) (b : Q ⟶ 𝟙_ C) (r : R ⟶ 𝟙_ C)
    (ih : c ≫ r = (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom) :
    ((α_ P Q (𝟙_ C)).inv ≫ (c ▷ 𝟙_ C)) ≫ ((r ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom) =
      (a ⊗ₘ ((b ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom := by
  have h2 : (a ⊗ₘ ((b ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom)) =
      (a ⊗ₘ (b ⊗ₘ 𝟙 (𝟙_ C))) ≫ (𝟙_ C ◁ (λ_ (𝟙_ C)).hom) := by
    rw [tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [h2]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, ih, comp_whiskerRight, Category.assoc,
    ← tensorHom_id (a ⊗ₘ b) (𝟙_ C), ← associator_inv_naturality_assoc, unit_assoc_collapse]

variable {D : Type w} [Category.{v} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.OplaxMonoidal]

theorem map_rightUnitor_hom_eq (P : C) :
    F.map (ρ_ P).hom = δ F P (𝟙_ C) ≫ (F.obj P ◁ η F) ≫ (ρ_ (F.obj P)).hom := by
  calc F.map (ρ_ P).hom = F.map (ρ_ P).hom ≫ (ρ_ (F.obj P)).inv ≫ (ρ_ (F.obj P)).hom := by
        rw [Iso.inv_hom_id, Category.comp_id]
    _ = F.map (ρ_ P).hom ≫ (F.map (ρ_ P).inv ≫ δ F P (𝟙_ C) ≫ F.obj P ◁ η F) ≫
          (ρ_ (F.obj P)).hom := by rw [right_unitality]
    _ = δ F P (𝟙_ C) ≫ (F.obj P ◁ η F) ≫ (ρ_ (F.obj P)).hom := by
        rw [← Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp,
          Category.assoc]

theorem map_rightUnitor_comp {P : C} {Q : D} (x : F.obj P ⟶ Q) :
    F.map (ρ_ P).hom ≫ x = δ F P (𝟙_ C) ≫ (x ⊗ₘ η F) ≫ (ρ_ Q).hom := by
  rw [map_rightUnitor_hom_eq, tensorHom_def']
  simp only [Category.assoc]
  rw [← rightUnitor_naturality]

@[reassoc]
theorem map_associator_inv_δ (P Q V : C) :
    F.map (α_ P Q V).inv ≫ δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V) =
      δ F P (Q ⊗ V) ≫ (F.obj P ◁ δ F Q V) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
  calc F.map (α_ P Q V).inv ≫ δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V)
      = F.map (α_ P Q V).inv ≫ (δ F (P ⊗ Q) V ≫ (δ F P Q ▷ F.obj V) ≫
          (α_ (F.obj P) (F.obj Q) (F.obj V)).hom) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = F.map (α_ P Q V).inv ≫ (F.map (α_ P Q V).hom ≫ δ F P (Q ⊗ V) ≫ F.obj P ◁ δ F Q V) ≫
          (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by rw [associativity]
    _ = δ F P (Q ⊗ V) ≫ (F.obj P ◁ δ F Q V) ≫ (α_ (F.obj P) (F.obj Q) (F.obj V)).inv := by
        rw [← Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
          Category.assoc]

theorem map_cat_step {P Q R V : C} {A B E : D} (c : P ⊗ Q ⟶ R) (x : F.obj P ⟶ A) (y : F.obj Q ⟶ B)
    (r : F.obj R ⟶ E) (c' : A ⊗ B ⟶ E)
    (ih : F.map c ≫ r = δ F P Q ≫ (x ⊗ₘ y) ≫ c') :
    F.map ((α_ P Q V).inv ≫ (c ▷ V)) ≫ (δ F R V ≫ (r ▷ F.obj V)) =
      δ F P (Q ⊗ V) ≫ (x ⊗ₘ (δ F Q V ≫ (y ▷ F.obj V))) ≫ (α_ A B (F.obj V)).inv ≫ (c' ▷ F.obj V) := by
  have h2 : (x ⊗ₘ (δ F Q V ≫ (y ▷ F.obj V))) =
      (F.obj P ◁ δ F Q V) ≫ (x ⊗ₘ (y ⊗ₘ 𝟙 (F.obj V))) := by
    rw [tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [h2, F.map_comp]
  simp only [Category.assoc]
  rw [← δ_natural_left_assoc, ← comp_whiskerRight, ih, comp_whiskerRight, comp_whiskerRight,
    map_associator_inv_δ_assoc, associator_inv_naturality_assoc, tensorHom_id]


/-- `F.map (f ⊗ₘ f') ≫ δ ≫ (a ⊗ₘ a') ≫ h = δ ≫ ((F.map f ≫ a) ⊗ₘ (F.map f' ≫ a')) ≫ h`. -/
theorem map_tensorHom_δ_comp {P P' Q Q' : C} {A A' E : D} (f : P ⟶ Q) (f' : P' ⟶ Q')
    (a : F.obj Q ⟶ A) (a' : F.obj Q' ⟶ A') (h : A ⊗ A' ⟶ E) :
    F.map (f ⊗ₘ f') ≫ δ F Q Q' ≫ (a ⊗ₘ a') ≫ h =
      δ F P P' ≫ ((F.map f ≫ a) ⊗ₘ (F.map f' ≫ a')) ≫ h := by
  rw [← δ_natural_assoc, ← tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.Scheme.Modules.MonoidalPowAux

/-! ## The three compatibilities in `X.Modules` -/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.MonoidalCategory MonoidalPowAux

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- (a) `pullbackMonoidalPow` is multiplicative. -/
@[reassoc]
theorem pullbackMonoidalPow_monoidalPowCat (g : T ⟶ X) (W : X.Modules) (m : ℕ) : ∀ n : ℕ,
    (pullback g).map (monoidalPowCat W m n).hom ≫ pullbackMonoidalPow g W (m + n) =
      pullbackTensorObjHom g (monoidalPow W m) (monoidalPow W n) ≫
        (pullbackMonoidalPow g W m ⊗ₘ pullbackMonoidalPow g W n) ≫
        (monoidalPowCat ((pullback g).obj W) m n).hom
  | 0 => by
    have h := map_rightUnitor_comp (pullback g) (pullbackMonoidalPow g W m)
    rw [pullback_η] at h
    exact h
  | n + 1 =>
    map_cat_step (pullback g) (monoidalPowCat W m n).hom (pullbackMonoidalPow g W m)
      (pullbackMonoidalPow g W n) (pullbackMonoidalPow g W (m + n))
      (monoidalPowCat ((pullback g).obj W) m n).hom (pullbackMonoidalPow_monoidalPowCat g W m n)

/-- (c) `unitPowCollapse` is multiplicative. -/
@[reassoc]
theorem unitPowCollapse_monoidalPowCat (X : AlgebraicGeometry.Scheme.{u}) (m : ℕ) : ∀ n : ℕ,
    (monoidalPowCat (𝟙_ X.Modules) m n).hom ≫ unitPowCollapse X (m + n) =
      (unitPowCollapse X m ⊗ₘ unitPowCollapse X n) ≫
        (λ_ (𝟙_ X.Modules)).hom
  | 0 => rightUnitor_comp_to_unit (unitPowCollapse X m)
  | n + 1 =>
    collapse_step (monoidalPowCat (𝟙_ X.Modules) m n).hom (unitPowCollapse X m) (unitPowCollapse X n)
      (unitPowCollapse X (m + n)) (unitPowCollapse_monoidalPowCat X m n)

/-- `symPowπ W m` followed by `symPowPullbackDesc` is the raw tensor-power map (definition + `symPowπ_desc`). -/
@[reassoc]
theorem pullback_map_symPowπ_symPowPullbackDesc (g : T ⟶ X)
    (W : X.Modules) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M) (m : ℕ) :
    (pullback g).map (symPowπ W m) ≫ symPowPullbackDesc g ψ m =
      pullbackMonoidalPow g W m ≫ monoidalPowMap ψ m := by
  unfold symPowPullbackDesc
  rw [← Adjunction.homEquiv_naturality_left_symm, symPowπ_desc, Equiv.symm_apply_apply]

/-- **Multiplicativity of the pulled-back symmetric-power descent** along a functional `ψ : g^*W ⟶ O_T`:
with `Ψ_m := symPowPullbackDesc g ψ m ≫ unitPowCollapse T m`,
`g^*(symPowMul W m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ (λ_ O_T).hom`. -/
theorem pullback_map_symPowMul_symPowPullbackDesc (g : T ⟶ X) (W : X.Modules)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) (m n : ℕ) :
    (pullback g).map (symPowMul W m n) ≫ symPowPullbackDesc g ψ (m + n) ≫ unitPowCollapse T (m + n) =
      pullbackTensorObjHom g (symPow W m) (symPow W n) ≫
        ((symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) ⊗ₘ
          (symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)) ≫
        (λ_ (𝟙_ T.Modules)).hom := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply symPowπ_tensorHom_cancel W m n
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  congr 1
  have hR : (pullback g).map (symPowπ W m ⊗ₘ symPowπ W n) ≫
      pullbackTensorObjHom g (symPow W m) (symPow W n) ≫
        ((symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) ⊗ₘ
          (symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)) ≫
        (λ_ (𝟙_ T.Modules)).hom =
      pullbackTensorObjHom g (monoidalPow W m) (monoidalPow W n) ≫
        (((pullback g).map (symPowπ W m) ≫ symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) ⊗ₘ
          ((pullback g).map (symPowπ W n) ≫ symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)) ≫
        (λ_ (𝟙_ T.Modules)).hom :=
    map_tensorHom_δ_comp (pullback g) (symPowπ W m) (symPowπ W n)
      (symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) (symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)
      (λ_ (𝟙_ T.Modules)).hom
  have hb := monoidalPowCat_monoidalPowMap ψ m n
  have hL1 : (pullback g).map (symPowπ W m ⊗ₘ symPowπ W n) ≫ (pullback g).map (symPowMul W m n) ≫
        symPowPullbackDesc g ψ (m + n) ≫ unitPowCollapse T (m + n) =
      (pullback g).map (monoidalPowCat W m n).hom ≫ (pullback g).map (symPowπ W (m + n)) ≫
        symPowPullbackDesc g ψ (m + n) ≫ unitPowCollapse T (m + n) := by
    rw [← Functor.map_comp_assoc, tensorHom_symPowπ_symPowMul, Functor.map_comp_assoc]
  have hL2 : (pullback g).map (symPowπ W (m + n)) ≫ symPowPullbackDesc g ψ (m + n) ≫
        unitPowCollapse T (m + n) =
      pullbackMonoidalPow g W (m + n) ≫ monoidalPowMap ψ (m + n) ≫ unitPowCollapse T (m + n) :=
    pullback_map_symPowπ_symPowPullbackDesc_assoc g W ψ (m + n) _
  have hL3 : (pullback g).map (monoidalPowCat W m n).hom ≫ pullbackMonoidalPow g W (m + n) ≫
        monoidalPowMap ψ (m + n) ≫ unitPowCollapse T (m + n) =
      pullbackTensorObjHom g (monoidalPow W m) (monoidalPow W n) ≫
        (pullbackMonoidalPow g W m ⊗ₘ pullbackMonoidalPow g W n) ≫
        (monoidalPowCat ((pullback g).obj W) m n).hom ≫ monoidalPowMap ψ (m + n) ≫
        unitPowCollapse T (m + n) :=
    pullbackMonoidalPow_monoidalPowCat_assoc g W m n _
  have hL4 : (monoidalPowCat ((pullback g).obj W) m n).hom ≫ monoidalPowMap ψ (m + n) ≫
        unitPowCollapse T (m + n) =
      (monoidalPowMap ψ m ⊗ₘ monoidalPowMap ψ n) ≫
        (monoidalPowCat (𝟙_ T.Modules) m n).hom ≫
        unitPowCollapse T (m + n) :=
    ((reassoc_of% hb) (unitPowCollapse T (m + n))).symm
  have hL5 : (monoidalPowCat (𝟙_ T.Modules) m n).hom ≫
        unitPowCollapse T (m + n) =
      (unitPowCollapse T m ⊗ₘ unitPowCollapse T n) ≫
        (λ_ (𝟙_ T.Modules)).hom :=
    unitPowCollapse_monoidalPowCat T m n
  have hR2 : (pullback g).map (symPowπ W m) ≫ symPowPullbackDesc g ψ m ≫ unitPowCollapse T m =
      pullbackMonoidalPow g W m ≫ monoidalPowMap ψ m ≫ unitPowCollapse T m :=
    pullback_map_symPowπ_symPowPullbackDesc_assoc g W ψ m _
  have hR3 : (pullback g).map (symPowπ W n) ≫ symPowPullbackDesc g ψ n ≫ unitPowCollapse T n =
      pullbackMonoidalPow g W n ≫ monoidalPowMap ψ n ≫ unitPowCollapse T n :=
    pullback_map_symPowπ_symPowPullbackDesc_assoc g W ψ n _
  rw [hL1, hL2, hL3, hL4, hL5, hR, hR2, hR3]
  simp only [tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.Scheme.Modules

end
