import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.MultiplicativeGroupScheme
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # Group scheme actions on `S`-schemes

Actions of a group scheme on an `S`-scheme. They are used to express that `G_m` acts on the based
jet space `J_k^s`, preserving `C` and the constant terms (the nonnegative grading of the coordinate
algebra of the cone, §2.1 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The following five lemmas are the compatibility conditions required by `pullback.lift` /
   `pullback.map` in the types of the fields `one_act` / `mul_act` of the structure
   `GroupSchemeAction`. They hold for every `G` and `T`, so they are proved here first and the
   field types refer to them directly. -/

section Conditions

set_option linter.unusedSectionVars false

variable {K S : AlgebraicGeometry.Scheme.{u}} [S.Over K]
    (G : CategoryTheory.Over K) [CategoryTheory.GrpObj G] (T : CategoryTheory.Over S)

/-- Lift compatibility for `one_act`: `(e ∘ structure morphism) ≫ G.hom = 𝟙 ≫ structure morphism`. -/
theorem GroupSchemeAction.oneAct_cond :
    ((T.hom ≫ (S ↘ K)) ≫ (CategoryTheory.MonObj.one : 𝟙_ _ ⟶ G).left) ≫ G.hom =
      𝟙 T.left ≫ (T.hom ≫ (S ↘ K)) := by
  rw [CategoryTheory.Category.assoc, CategoryTheory.Over.w, CategoryTheory.Category.id_comp]
  exact CategoryTheory.Category.comp_id _

/-- First map compatibility for `mul_act`: `(fst ≫ G.hom) ≫ 𝟙 = mul.left ≫ G.hom`. -/
theorem GroupSchemeAction.mulAct_cond₁ :
    (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) ≫ 𝟙 K =
      (CategoryTheory.MonObj.mul : G ⊗ G ⟶ G).left ≫ G.hom := by
  rw [CategoryTheory.Over.w, CategoryTheory.Category.comp_id]
  rfl

/-- Second map compatibility for `mul_act`: `structure morphism ≫ 𝟙 = 𝟙 ≫ structure morphism`. -/
theorem GroupSchemeAction.mulAct_cond₂ :
    (T.hom ≫ (S ↘ K)) ≫ 𝟙 K = 𝟙 T.left ≫ (T.hom ≫ (S ↘ K)) := by
  rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

/-- Compatibility for the inner lift on the right-hand side of `mul_act`: `(fst ≫ snd) ≫ G.hom = snd ≫ structure morphism`. -/
theorem GroupSchemeAction.mulAct_cond₃ :
    (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom) ≫ G.hom =
      CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫ (T.hom ≫ (S ↘ K)) := by
  have e1 : CategoryTheory.Limits.pullback.snd G.hom G.hom ≫ G.hom = CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom :=
    CategoryTheory.Limits.pullback.condition.symm
  rw [CategoryTheory.Category.assoc, e1]
  exact CategoryTheory.Limits.pullback.condition

/-- Compatibility for the outer lift on the right-hand side of `mul_act`: `(fst ≫ fst) ≫ G.hom = (inner lift ≫ act) ≫ structure morphism`. -/
theorem GroupSchemeAction.mulAct_cond₄ (act : pullback G.hom (T.hom ≫ (S ↘ K)) ⟶ T.left)
    (hact : act ≫ T.hom = CategoryTheory.Limits.pullback.snd _ _ ≫ T.hom) :
    (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫ CategoryTheory.Limits.pullback.fst G.hom G.hom) ≫ G.hom =
      (CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫ CategoryTheory.Limits.pullback.snd G.hom G.hom)
        (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)))
        (GroupSchemeAction.mulAct_cond₃ G T) ≫ act) ≫ (T.hom ≫ (S ↘ K)) := by
  have e1 : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫
      CategoryTheory.Limits.pullback.fst G.hom G.hom) ≫ G.hom =
      CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom) (T.hom ≫ (S ↘ K)) ≫ (T.hom ≫ (S ↘ K)) := by
    rw [CategoryTheory.Category.assoc]; exact CategoryTheory.Limits.pullback.condition
  refine e1.trans ?_
  rw [CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc act, hact,
    CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd_assoc]

end Conditions

/-- An action of a group scheme `G` over `K` on an `S`-scheme `T` (where `S` is a `K`-scheme):
a morphism `act : G ×_K T → T` over `S` satisfying the unit and associativity axioms. -/
structure GroupSchemeAction {K S : AlgebraicGeometry.Scheme.{u}} [S.Over K]
    (G : CategoryTheory.Over K) [CategoryTheory.GrpObj G] (T : CategoryTheory.Over S) where
  /-- The action `G ×_K T → T` (`T` is regarded as a `K`-scheme via `T.hom ≫ (S ↘ K)`). -/
  act : CategoryTheory.Limits.pullback G.hom (T.hom ≫ (S ↘ K)) ⟶ T.left
  /-- The action commutes with the structure morphism to `S`. -/
  act_over : act ≫ T.hom = CategoryTheory.Limits.pullback.snd _ _ ≫ T.hom
  /-- The unit acts trivially: `(e, t) ↦ t`. -/
  one_act : CategoryTheory.Limits.pullback.lift
      ((T.hom ≫ (S ↘ K)) ≫ (CategoryTheory.MonObj.one : CategoryTheory.MonoidalCategory.tensorUnit _ ⟶ G).left)
      (CategoryTheory.CategoryStruct.id T.left)
      (GroupSchemeAction.oneAct_cond G T) ≫ act = CategoryTheory.CategoryStruct.id T.left
  /-- Associativity `(gh)·t = g·(h·t)`; `(G ⊗ G).left` is by definition `pullback G.hom G.hom`. -/
  mul_act :
    CategoryTheory.Limits.pullback.map (CategoryTheory.Limits.pullback.fst G.hom G.hom ≫ G.hom)
        (T.hom ≫ (S ↘ K)) G.hom (T.hom ≫ (S ↘ K))
        (CategoryTheory.MonObj.mul : G ⊗ G ⟶ G).left (CategoryTheory.CategoryStruct.id T.left)
        (CategoryTheory.CategoryStruct.id K)
        (GroupSchemeAction.mulAct_cond₁ G) (GroupSchemeAction.mulAct_cond₂ T) ≫ act =
      CategoryTheory.Limits.pullback.lift
        (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.fst _ _)
        (CategoryTheory.Limits.pullback.lift
            (CategoryTheory.Limits.pullback.fst _ _ ≫ CategoryTheory.Limits.pullback.snd _ _)
            (CategoryTheory.Limits.pullback.snd _ _) (GroupSchemeAction.mulAct_cond₃ G T) ≫ act)
        (GroupSchemeAction.mulAct_cond₄ G T act act_over) ≫ act

/-- A `G_m`-action on the `S`-scheme `T`, where `S` is a scheme over `Spec k`. -/
abbrev GmActionOver (k : Type u) [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (T : CategoryTheory.Over S) :=
  GroupSchemeAction ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))) T

/- The two compatibility conditions for `pullback.map` in `IsNonnegative`: `G_m ↪ A¹ = Spec k[λ]` is a `k`-morphism, and the other side is the identity. -/

section NonnegativeConditions

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `G_m ⟶ A¹` (the `Spec` of `k[λ] → k[λ^{±1}]`) is a morphism over `Spec k`. -/
theorem GroupSchemeAction.isNonnegative_cond₁ :
    ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [CategoryTheory.Category.comp_id]
  show AlgebraicGeometry.Spec.map _ = AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  exact ((Polynomial.toLaurentAlg (R := k)).comp_algebraMap).symm

/-- The other side is the identity: `structure morphism ≫ 𝟙 = 𝟙 ≫ structure morphism`. -/
theorem GroupSchemeAction.isNonnegative_cond₂ (T : CategoryTheory.Over S) :
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
        CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      CategoryTheory.CategoryStruct.id T.left ≫ (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  rw [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

end NonnegativeConditions

/-- Nonnegativity: the `G_m`-action extends to an action of the monoid `A¹ = Spec k[λ]` on the
`S`-scheme `T` (the coaction then lands in `O[λ]`, corresponding to an `ℕ`-grading). Two conditions:
(1) the extension `act' : A¹ ×_k T → T` restricts to `act` along `G_m ↪ A¹`; (2) `act'` is an
`S`-morphism (`act' ≫ π = pr₂ ≫ π`).

Condition (2) is in fact a consequence of (1): `G_m ×_k T ⊆ A¹ ×_k T` is schematically dense, and
one argues pointwise using the generic point of the fibre `A¹_{κ(t)}` (see
`IsNonnegative.exists_act'_over` in `WeightDecomposition.lean`). It is nevertheless part of the
definition, since for the jet rescaling action `jetRescalingAction` the extension
`affineLineRescalingAct` is a morphism over `S` by construction (`affineLineRescalingAct_over`).
See §2.1 of the paper: the action extended to `A¹` is an action of `C`-schemes, giving the
nonnegative grading of the coordinate algebra of the cone. -/

def GroupSchemeAction.IsNonnegative {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    (α : GmActionOver k T) : Prop :=
  ∃ act' : CategoryTheory.Limits.pullback
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ T.left,
    CategoryTheory.Limits.pullback.map _ _ _ _
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := k)).toRingHom))
        (CategoryTheory.CategoryStruct.id _) (CategoryTheory.CategoryStruct.id _)
        GroupSchemeAction.isNonnegative_cond₁ (GroupSchemeAction.isNonnegative_cond₂ T) ≫ act' =
      α.act ∧
    act' ≫ T.hom = CategoryTheory.Limits.pullback.snd _ _ ≫ T.hom

end
