import MiyaokaMori.Prelude
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Isomorphisms of complexes through an adjunction

Three categorical lemmas for an adjunction `F ⊣ G` between preadditive categories, with `F` and `G`
preserving zero morphisms.
1. `liftThrough`: when `G` preserves the product, a family `q_i : P → G(Z'_i)` glues to
   `P → G(∏ Z'_i)`; it commutes with differentials of "signed sum of components" type
   (`liftThrough_comm`).
2. `nonempty_iso_of_isIso_transpose`: if for a chain map `ψ : K → G(L)` every adjoint transpose
   `F(K^i) → L^i` is an isomorphism, then `F(K) ≅ L` as complexes.
3. `isIso_transpose_liftThrough`: for a finite index set, `P` the product of the `Y_i` and `F`
   preserving finite products, if the transpose of each `s_i : Y_i → G(Z'_i)` is an isomorphism, so is
   the transpose of the glued map `P → G(∏ Z'_i)`.

Reference: standard category theory (Mac Lane, *Categories for the Working Mathematician*, IV.1
naturality of adjunctions, V.5 right adjoints preserve limits). Used for the base change of the Čech
complex, `K^• ⊗_A A' ≅ Č(U', M')`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AdjointComplexIso

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Lift

variable (G : D ⥤ C) {ι : Type} (Z' : ι → D) [HasProduct Z']
  [PreservesLimit (Discrete.functor Z') G]

/-- A family `q_i : P → G(Z'_i)` glued to `P → G(∏ Z'_i)` (`G` preserves this product). -/
def liftThrough {P : C} (q : ∀ i, P ⟶ G.obj (Z' i)) : P ⟶ G.obj (∏ᶜ Z') :=
  Fan.IsLimit.lift (isLimitFanMkObjOfIsLimit G Z' _ (productIsProduct Z')) q

@[reassoc]
theorem liftThrough_π {P : C} (q : ∀ i, P ⟶ G.obj (Z' i)) (i : ι) :
    liftThrough G Z' q ≫ G.map (Pi.π Z' i) = q i :=
  Fan.IsLimit.fac (isLimitFanMkObjOfIsLimit G Z' _ (productIsProduct Z')) q i

theorem liftThrough_hom_ext {P : C} {f g : P ⟶ G.obj (∏ᶜ Z')}
    (h : ∀ i, f ≫ G.map (Pi.π Z' i) = g ≫ G.map (Pi.π Z' i)) : f = g :=
  Fan.IsLimit.hom_ext (isLimitFanMkObjOfIsLimit G Z' _ (productIsProduct Z')) _ _ h

end Lift

section Comm

variable [Preadditive C] [Preadditive D] (G : D ⥤ C) [G.Additive]
  {ι κ : Type} {m : ℕ} (Z' : ι → D) (W' : κ → D) [HasProduct Z'] [HasProduct W']
  [PreservesLimit (Discrete.functor Z') G] [PreservesLimit (Discrete.functor W') G]

/-- `liftThrough` commutes with differentials of "signed sum of components" type: if the signed sum of
`P --q_{a τ k}--> G(Z'_{a τ k}) --G(r'_{τ,k})--> G(W'_τ)` equals `P --d--> Q --t_τ--> G(W'_τ)`, the
square commutes. -/
theorem liftThrough_comm {P Q : C} (d : P ⟶ Q) (a : κ → Fin m → ι) (ε : Fin m → ℤ)
    (r' : ∀ (τ : κ) (k : Fin m), Z' (a τ k) ⟶ W' τ)
    (q : ∀ i, P ⟶ G.obj (Z' i)) (t : ∀ τ, Q ⟶ G.obj (W' τ))
    (h : ∀ τ, d ≫ t τ = ∑ k : Fin m, ε k • (q (a τ k) ≫ G.map (r' τ k))) :
    liftThrough G Z' q ≫
        G.map (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z' (a τ k) ≫ r' τ k)) =
      d ≫ liftThrough G W' t := by
  refine liftThrough_hom_ext G W' fun τ => ?_
  rw [Category.assoc, Category.assoc, liftThrough_π, ← G.map_comp, Limits.Pi.lift_π, G.map_sum,
    Preadditive.comp_sum, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [G.map_zsmul, Preadditive.comp_zsmul, G.map_comp, liftThrough_π_assoc]

/-- The common form of `liftThrough_comm`: the source is also a product (transported by an additive
functor `R`) and the differentials have the same shape on both sides. -/
theorem liftThrough_comm_of_components {C₀ : Type*} [Category C₀] [Preadditive C₀]
    (R : C₀ ⥤ C) [R.Additive] (Z : ι → C₀) (W : κ → C₀) [HasProduct Z] [HasProduct W]
    (a : κ → Fin m → ι) (ε : Fin m → ℤ)
    (r : ∀ (τ : κ) (k : Fin m), Z (a τ k) ⟶ W τ) (r' : ∀ (τ : κ) (k : Fin m), Z' (a τ k) ⟶ W' τ)
    (s : ∀ i, R.obj (Z i) ⟶ G.obj (Z' i)) (s' : ∀ τ, R.obj (W τ) ⟶ G.obj (W' τ))
    (h : ∀ τ k, R.map (r τ k) ≫ s' τ = s (a τ k) ≫ G.map (r' τ k)) :
    liftThrough G Z' (fun i => R.map (Pi.π Z i) ≫ s i) ≫
        G.map (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z' (a τ k) ≫ r' τ k)) =
      R.map (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z (a τ k) ≫ r τ k)) ≫
        liftThrough G W' (fun τ => R.map (Pi.π W τ) ≫ s' τ) := by
  refine liftThrough_comm G Z' W' _ a ε r' _ _ fun τ => ?_
  rw [← Category.assoc, ← R.map_comp, Limits.Pi.lift_π, R.map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [R.map_zsmul, Preadditive.zsmul_comp, R.map_comp, Category.assoc, Category.assoc, h]

end Comm

section ComplexIso

variable [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  {α : Type*} {c : ComplexShape α}

/-- If the adjoint transposes of a chain map `ψ : K → G(L)` are isomorphisms in every degree, then
`F(K) ≅ L`. -/
theorem nonempty_iso_of_isIso_transpose {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    (ψ : K ⟶ (G.mapHomologicalComplex c).obj L)
    (h : ∀ i, IsIso ((adj.homEquiv _ _).symm (ψ.f i))) :
    Nonempty ((F.mapHomologicalComplex c).obj K ≅ L) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun i => @asIso _ _ _ _ ((adj.homEquiv _ _).symm (ψ.f i)) (h i)) (fun i j _ => ?_)⟩
  have key : ∀ (f : K.X i ⟶ G.obj (L.X i)) (f' : K.X j ⟶ G.obj (L.X j)),
      f ≫ G.map (L.d i j) = K.d i j ≫ f' →
      (adj.homEquiv _ _).symm f ≫ L.d i j = F.map (K.d i j) ≫ (adj.homEquiv _ _).symm f' := by
    intro f f' hf
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm, hf]
  exact key _ _ (ψ.comm i j)

end ComplexIso

section FiniteProduct

variable [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- On a finite product, if the transposes are isomorphisms componentwise, the transpose of the glued
map is an isomorphism.

Let `ι` be finite, `(P, pr_i : P → Y_i)` a limit fan of `Y` (`hP`), `F` preserving this finite
product, `H : D' ⥤ D` preserving `∏ Z'` and `G` preserving `∏ H(Z')` (in the application
`F = ModuleCat.extendScalars φ`, `G = restrictScalars φ`, `H = restrictScalars a'`). Suppose the
transposes `ŝ_i : F(Y_i) → H(Z'_i)` of `s_i : Y_i → G(H(Z'_i))` are isomorphisms. With
`q_i = pr_i ≫ s_i`, the transpose `F(P) → H(∏ Z')` of `liftThrough (H ⋙ G) Z' q : P → G(H(∏ Z'))`
is an isomorphism.

Proof sketch: let `θ` be the transpose of `liftThrough q`. By `Adjunction.homEquiv_naturality_right_symm`
and `liftThrough_π`, `θ ≫ H(π_i) = transpose(q_i) = F(pr_i) ≫ ŝ_i`
(`Adjunction.homEquiv_naturality_left_symm`). `(F(P), F(pr_i))` is a limit fan of the `F(Y_i)` and
`(H(∏ Z'), H(π_i))` a limit fan of the `H(Z'_i)`; `θ` is the morphism between the two limit fans
induced by the componentwise isomorphisms `ŝ_i`, hence an isomorphism: the inverse is
`Fan.IsLimit.lift (F-fan) (fun i => H(π_i) ≫ inv ŝ_i)`, and both composites are checked componentwise
with `Fan.IsLimit.hom_ext`. For empty `ι` both objects are terminal and the argument applies verbatim. -/
theorem isIso_transpose_liftThrough {D' : Type*} [Category D'] (H : D' ⥤ D)
    {ι : Type} [Finite ι] (Y : ι → C) (Z' : ι → D') [HasProduct Z']
    [PreservesLimit (Discrete.functor Z') H] [PreservesLimit (Discrete.functor Z') (H ⋙ G)]
    [PreservesLimit (Discrete.functor Y) F]
    {P : C} (pr : ∀ i, P ⟶ Y i) (hP : IsLimit (Fan.mk P pr))
    (s : ∀ i, Y i ⟶ G.obj (H.obj (Z' i))) (hs : ∀ i, IsIso ((adj.homEquiv _ _).symm (s i))) :
    IsIso ((adj.homEquiv P (H.obj (∏ᶜ Z'))).symm
      (liftThrough (H ⋙ G) Z' fun i => pr i ≫ s i)) := by
  have cF : IsLimit (Fan.mk (F.obj P) fun i => F.map (pr i)) :=
    isLimitFanMkObjOfIsLimit F Y _ hP
  have cH : IsLimit (Fan.mk (H.obj (∏ᶜ Z')) fun i => H.map (Pi.π Z' i)) :=
    isLimitFanMkObjOfIsLimit H Z' _ (productIsProduct Z')
  have hθ : ∀ i, (adj.homEquiv P (H.obj (∏ᶜ Z'))).symm
      (liftThrough (H ⋙ G) Z' fun i => pr i ≫ s i) ≫ H.map (Pi.π Z' i) =
      F.map (pr i) ≫ (adj.homEquiv _ _).symm (s i) := by
    intro i
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm]
    exact congrArg _ (liftThrough_π (H ⋙ G) Z' (fun i => pr i ≫ s i) i)
  have hfac : ∀ i, (Fan.IsLimit.lift cF fun i =>
      H.map (Pi.π Z' i) ≫ @inv _ _ _ _ ((adj.homEquiv _ _).symm (s i)) (hs i)) ≫ F.map (pr i) =
      H.map (Pi.π Z' i) ≫ @inv _ _ _ _ ((adj.homEquiv _ _).symm (s i)) (hs i) := fun i =>
    Fan.IsLimit.fac cF _ i
  refine ⟨⟨Fan.IsLimit.lift cF fun i =>
    H.map (Pi.π Z' i) ≫ @inv _ _ _ _ ((adj.homEquiv _ _).symm (s i)) (hs i), ?_, ?_⟩⟩
  · refine Fan.IsLimit.hom_ext cF _ _ fun i => ?_
    show (_ ≫ _) ≫ F.map (pr i) = 𝟙 _ ≫ F.map (pr i)
    rw [Category.assoc, hfac, ← Category.assoc, hθ, Category.assoc,
      @IsIso.hom_inv_id _ _ _ _ _ (hs i), Category.comp_id, Category.id_comp]
  · refine Fan.IsLimit.hom_ext cH _ _ fun i => ?_
    show (_ ≫ _) ≫ H.map (Pi.π Z' i) = 𝟙 _ ≫ H.map (Pi.π Z' i)
    rw [Category.assoc, hθ, ← Category.assoc, hfac, Category.assoc,
      @IsIso.inv_hom_id _ _ _ _ _ (hs i), Category.comp_id, Category.id_comp]

end FiniteProduct

end AdjointComplexIso

end
