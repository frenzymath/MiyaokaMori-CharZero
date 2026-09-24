import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetThickening
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone

/-! # The relative based jet functor

The relative jet functor based at `s`: a `C`-scheme `W` is sent to the set of morphisms
`φ : W × Spec k[t]/(t^{k+1}) → Z` over `C` whose constant term is `s|_W` (§2 of the paper, the based relative jet
scheme `J_k^s`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Functoriality of `jetThickening`: compatibility of `W ↦ W ×_k D_r` with the two projections and with the
   constant-term section. -/

section Glue

variable {k : Type u} [Field k] (r : ℕ) {W W' W'' : AlgebraicGeometry.Scheme.{u}}
  [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  [W''.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `jetThickeningMap` is compatible with the projection: `(g × 𝟙) ≫ pr = pr ≫ g`. -/
@[reassoc]
theorem jetThickeningMap_proj (g : W ⟶ W')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r g ≫ jetThickeningProj (k := k) r W' =
      jetThickeningProj (k := k) r W ≫ g :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- `jetThickeningMap` is the identity in the `D_r` direction: `(g × 𝟙) ≫ snd = snd`. -/
@[reassoc]
theorem jetThickeningMap_snd (g : W ⟶ W')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r g ≫
        CategoryTheory.Limits.pullback.snd (W' ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  (CategoryTheory.Limits.pullback.lift_snd _ _ _).trans (CategoryTheory.Category.comp_id _)

/-- Functoriality of `jetThickeningMap`: `(𝟙 × 𝟙) = 𝟙`. -/
theorem jetThickeningMap_id :
    jetThickeningMap (k := k) r (CategoryTheory.CategoryStruct.id W) =
      CategoryTheory.CategoryStruct.id (jetThickening (k := k) r W) := by
  delta jetThickeningMap
  exact CategoryTheory.Limits.pullback.map_id

/-- Functoriality of `jetThickeningMap`: `((g ≫ h) × 𝟙) = (g × 𝟙) ≫ (h × 𝟙)`. -/
theorem jetThickeningMap_comp (g : W ⟶ W') (h : W' ⟶ W'')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [h.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r (g ≫ h) =
      jetThickeningMap (k := k) r g ≫ jetThickeningMap (k := k) r h := by
  delta jetThickeningMap jetThickening
  ext <;>
    simp [CategoryTheory.Limits.pullback.map, CategoryTheory.Limits.pullback.lift_fst,
      CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_fst_assoc]

/-- The constant-term section and the projection: `ct ≫ pr = 𝟙`. -/
@[reassoc]
theorem jetConstantTerm_comp_proj :
    jetConstantTerm (k := k) r W ≫ jetThickeningProj (k := k) r W =
      CategoryTheory.CategoryStruct.id W :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- The constant-term section in the `D_r` direction: `ct ≫ snd = (W → Spec k) ≫ (t ↦ 0)`. -/
@[reassoc]
theorem jetConstantTerm_comp_snd :
    jetConstantTerm (k := k) r W ≫
        CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ jetBaseZero k r :=
  CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- Naturality of the constant-term section: `ct ≫ (g × 𝟙) = g ≫ ct`. -/
theorem jetConstantTerm_naturality (g : W ⟶ W')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetConstantTerm (k := k) r W ≫ jetThickeningMap (k := k) r g =
      g ≫ jetConstantTerm (k := k) r W' := by
  delta jetConstantTerm jetThickeningMap jetThickening
  ext <;>
    simp [CategoryTheory.Limits.pullback.map, CategoryTheory.Limits.pullback.lift_fst,
      CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_fst_assoc]

end Glue

noncomputable def relativeJetFunctor {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (CategoryTheory.Over C)ᵒᵖ ⥤ Type u where
  obj W :=
    letI : W.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    { φ : jetThickening (k := k) r W.unop.left ⟶ Z.left //
      φ ≫ Z.hom = jetThickeningProj (k := k) r W.unop.left ≫ W.unop.hom ∧
      jetConstantTerm (k := k) r W.unop.left ≫ φ = W.unop.hom ≫ s }
  map {W W'} g :=
    letI : W.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : W'.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W'.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : g.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc g.unop _⟩
    TypeCat.ofHom (fun φ => ⟨jetThickeningMap (k := k) r g.unop.left ≫ φ.1, by
      constructor
      · rw [CategoryTheory.Category.assoc, φ.2.1, ← CategoryTheory.Category.assoc,
          jetThickeningMap_proj, CategoryTheory.Category.assoc, CategoryTheory.Over.w]
      · rw [← CategoryTheory.Category.assoc, jetConstantTerm_naturality,
          CategoryTheory.Category.assoc, φ.2.2, ← CategoryTheory.Category.assoc,
          CategoryTheory.Over.w]⟩)
  map_id W := by
    letI : W.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    apply TypeCat.homEquiv.injective
    funext φ
    apply Subtype.ext
    show jetThickeningMap (k := k) r
      (CategoryTheory.CategoryStruct.id W.unop.left) ≫ φ.1 = φ.1
    rw [jetThickeningMap_id, CategoryTheory.Category.id_comp]
  map_comp {W W' W''} g h := by
    letI : W.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : W'.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W'.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : W''.unop.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W''.unop.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : g.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc g.unop _⟩
    haveI : h.unop.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc h.unop _⟩
    apply TypeCat.homEquiv.injective
    funext φ
    apply Subtype.ext
    show jetThickeningMap (k := k) r (h.unop.left ≫ g.unop.left) ≫ φ.1 =
      jetThickeningMap (k := k) r h.unop.left ≫ jetThickeningMap (k := k) r g.unop.left ≫ φ.1
    rw [jetThickeningMap_comp, CategoryTheory.Category.assoc]

end
