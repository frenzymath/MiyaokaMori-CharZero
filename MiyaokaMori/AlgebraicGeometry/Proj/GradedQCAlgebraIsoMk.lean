import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory

/-! # Building an isomorphism of graded quasi-coherent algebras from its graded pieces

Given a family of isomorphisms `app m : S.part m ≅ T.part m` whose forward maps are compatible with
multiplication and the unit, the family assembles to an isomorphism in `X.GradedQCAlgebra` (the
compatibility of the inverse maps follows from that of the forward maps by multiplying by the
inverses on both sides). The file also provides the extensionality lemma for morphisms and the
graded pieces `partIso` of an isomorphism of graded algebras.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism of graded algebras is determined by its graded pieces. -/
theorem Hom.ext' {S T : X.GradedQCAlgebra} (φ ψ : S ⟶ T)
    (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  cases φ with
  | mk φ hmul hone =>
    cases ψ with
    | mk ψ hmul' hone' =>
      simp only at h
      cases funext h
      rfl

@[simp] theorem comp_app {S T U : X.GradedQCAlgebra} (φ : S ⟶ T) (ψ : T ⟶ U) (m : ℕ) :
    (φ ≫ ψ).app m = φ.app m ≫ ψ.app m := rfl

@[simp] theorem id_app (S : X.GradedQCAlgebra) (m : ℕ) : (𝟙 S : S ⟶ S).app m = 𝟙 _ := rfl

/-- The `m`-th graded piece of an isomorphism of graded algebras. -/
def partIso {S T : X.GradedQCAlgebra} (e : S ≅ T) (m : ℕ) : S.part m ≅ T.part m where
  hom := e.hom.app m
  inv := e.inv.app m
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

/-- Build an isomorphism of graded algebras from a family of piecewise isomorphisms compatible with multiplication and the unit. -/
def isoMk {S T : X.GradedQCAlgebra} (app : ∀ m, S.part m ≅ T.part m)
    (map_mul : ∀ m n, S.mul m n ≫ (app (m + n)).hom = ((app m).hom ⊗ₘ (app n).hom) ≫ T.mul m n)
    (map_one : S.one ≫ (app 0).hom = T.one) : S ≅ T where
  hom := ⟨fun m => (app m).hom, map_mul, map_one⟩
  inv := ⟨fun m => (app m).inv, fun m n => by
      rw [← cancel_epi ((app m).hom ⊗ₘ (app n).hom), ← Category.assoc _ ((app m).inv ⊗ₘ (app n).inv),
        MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id, Iso.hom_inv_id,
        MonoidalCategory.id_tensorHom_id, Category.id_comp, ← Category.assoc, ← map_mul, Category.assoc,
        Iso.hom_inv_id, Category.comp_id],
    by rw [← map_one, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := Hom.ext' _ _ fun m => by simp
  inv_hom_id := Hom.ext' _ _ fun m => by simp

@[simp] theorem isoMk_hom_app {S T : X.GradedQCAlgebra} (app : ∀ m, S.part m ≅ T.part m)
    (map_mul) (map_one) (m : ℕ) : (isoMk app map_mul map_one).hom.app m = (app m).hom := rfl

@[simp] theorem isoMk_inv_app {S T : X.GradedQCAlgebra} (app : ∀ m, S.part m ≅ T.part m)
    (map_mul) (map_one) (m : ℕ) : (isoMk app map_mul map_one).inv.app m = (app m).inv := rfl

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
