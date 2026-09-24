import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueConstruction
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue

/-! # Gluing isomorphisms of sheaves of modules

Isomorphisms of `O_X`-modules glue along an open cover: a family of isomorphisms
`M|_{U_i} ≅ N|_{U_i}` whose section maps agree on every open `V ⊆ U_i ∩ U_j` glues to a global
isomorphism `M ≅ N` (Stacks 04TN, gluing of morphisms of sheaves; linearity is local).
Used in the proof of `O_X(f^*D) ≅ f^*O_X(D)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry.Scheme.Modules

/- The map `Γ(M, V) ⟶ Γ(N, V)` induced on `V ≤ W` by `φ : M|_W ⟶ N|_W` is
   `AlgebraicGeometry.Scheme.Modules.restrictSectionMap`. -/

private theorem sectionMap_comp_aux {C : Type*} [Category C] {A A1 B1 B C2 D : C}
    (a : A ⟶ A1) (p : A1 ⟶ B1) (b : B1 ⟶ B) (a' : B ⟶ B1) (q : B1 ⟶ C2) (c : C2 ⟶ D)
    (e : b ≫ a' = 𝟙 _) :
    (a ≫ p ≫ b) ≫ (a' ≫ q ≫ c) = a ≫ (p ≫ q) ≫ c := by
  simp only [Category.assoc]; rw [reassoc_of% e]

private theorem sectionMap_comp {X : AlgebraicGeometry.Scheme.{u}} {M N P : X.Modules} {W : X.Opens}
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) (ψ : N.restrict W.ι ⟶ P.restrict W.ι) (V : X.Opens) (hV : V ≤ W) :
    sectionMapOfRestrictHom φ V hV ≫ sectionMapOfRestrictHom ψ V hV = sectionMapOfRestrictHom (φ ≫ ψ) V hV := by
  have h2 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  have e : N.presheaf.map (homOfLE h2).op ≫ N.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact N.presheaf.map_id _
  exact sectionMap_comp_aux _ _ _ _ _ _ e

private theorem sectionMap_id {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {W : X.Opens}
    (V : X.Opens) (hV : V ≤ W) :
    sectionMapOfRestrictHom (𝟙 (M.restrict W.ι)) V hV = 𝟙 _ := by
  have := app_eq_sectionMap_restrict (𝟙 M) (W := W) V hV
  rw [CategoryTheory.Functor.map_id] at this
  rw [← this]; rfl

theorem AlgebraicGeometry.Scheme.Modules.glueIso {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (φ : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (hφ : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (φ i).hom V hi
        = AlgebraicGeometry.Scheme.Modules.restrictSectionMap (φ j).hom V hj) :
    ∃ e : M ≅ N, ∀ i (V : X.Opens) (hi : V ≤ U i),
      e.hom.app V = AlgebraicGeometry.Scheme.Modules.restrictSectionMap (φ i).hom V hi := by
  have hφ' : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      sectionMapOfRestrictHom (φ i).hom V hi = sectionMapOfRestrictHom (φ j).hom V hj := hφ
  have hψ : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      sectionMapOfRestrictHom (φ i).inv V hi = sectionMapOfRestrictHom (φ j).inv V hj := by
    intro i j V hi hj
    calc sectionMapOfRestrictHom (φ i).inv V hi
        = sectionMapOfRestrictHom (φ i).inv V hi ≫
            (sectionMapOfRestrictHom (φ j).hom V hj ≫ sectionMapOfRestrictHom (φ j).inv V hj) := by
          rw [sectionMap_comp, Iso.hom_inv_id, sectionMap_id, Category.comp_id]
      _ = (sectionMapOfRestrictHom (φ i).inv V hi ≫ sectionMapOfRestrictHom (φ i).hom V hi) ≫
            sectionMapOfRestrictHom (φ j).inv V hj := by
          rw [hφ' j i V hj hi, Category.assoc]
      _ = sectionMapOfRestrictHom (φ j).inv V hj := by
          rw [sectionMap_comp, Iso.inv_hom_id, sectionMap_id, Category.id_comp]
  obtain ⟨g, hg⟩ := exists_hom_of_sectionMap_agree U hU M N (fun i => (φ i).hom) hφ'
  obtain ⟨g', hg'⟩ := exists_hom_of_sectionMap_agree U hU N M (fun i => (φ i).inv) hψ
  have rg : ∀ i, (restrictFunctor (U i).ι).map g = (φ i).hom := fun i =>
    restrict_map_eq_of_app_eq_sectionMap g _ (hg i)
  have rg' : ∀ i, (restrictFunctor (U i).ι).map g' = (φ i).inv := fun i =>
    restrict_map_eq_of_app_eq_sectionMap g' _ (hg' i)
  refine ⟨⟨g, g', ?_, ?_⟩, fun i V hi => hg i V hi⟩
  · refine hom_ext_of_cover U hU _ _ fun i => ?_
    rw [CategoryTheory.Functor.map_comp, rg, rg', Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  · refine hom_ext_of_cover U hU _ _ fun i => ?_
    rw [CategoryTheory.Functor.map_comp, rg', rg, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end
