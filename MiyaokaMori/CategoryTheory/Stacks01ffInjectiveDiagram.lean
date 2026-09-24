import MiyaokaMori.Prelude
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # Functorial injective embedding of a diagram

Functorial injective embedding of a diagram: for any diagram `F : J ⥤ D` in a category with enough
injectives and enough products, there is a diagram `I : J ⥤ D` of injective objects and a natural
transformation `ι : F ⟶ I` that is a monomorphism at every `j`.

This is the second step of the proof of Stacks 01FF (cohomology-lemma-quasi-separated-cohomology-colimit):
"by Stacks 01DI we can find a system of injective sheaves `I_i` with injective maps `F_i → I_i`" (Stacks uses a
functorial injective embedding of the category of sheaves; here the diagram is embedded directly).

Construction (right Kan extension along the points of `J`). For `k : J` the evaluation functor
`(evaluation J D).obj k` has the right adjoint `evaluationRightAdjoint D k : A ↦ (l ↦ ∏_{l ⟶ k} A)`
(Mathlib `CategoryTheory.evaluationAdjunctionLeft`). Put `A k := Injective.under (F.obj k)` (an injective
object receiving the monomorphism `Injective.ι (F.obj k) : F.obj k ⟶ A k`), and
`I := ∏_k (evaluationRightAdjoint D k).obj (A k)` (a product in the functor category `J ⥤ D`).
* `I.obj l ≅ ∏_k ∏_{l ⟶ k} A k` (limits in functor categories are computed pointwise,
  `limitObjIsoLimitCompEvaluation`), a product of injectives, hence injective.
* `ι : F ⟶ I` is `Pi.lift` of the adjuncts of the maps `Injective.ι (F.obj k)`. Composing `ι.app l` with the
  projection to the `k = l` factor and then with the counit (the projection to the factor `𝟙 l`) gives back
  `Injective.ι (F.obj l)`, which is a monomorphism; hence `ι.app l` is a monomorphism. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Functor

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D]

section

variable [∀ a b : J, HasProductsOfShape (a ⟶ b) D]

/-- `((evaluationRightAdjoint D k).obj A).obj l = ∏_{l ⟶ k} A` is injective when `A` is. -/
theorem injective_evaluationRightAdjoint_obj_obj (k : J) (A : D) [Injective A] (l : J) :
    Injective (((evaluationRightAdjoint D k).obj A).obj l) := by
  rw [evaluationRightAdjoint_obj_obj]
  infer_instance

variable [HasProductsOfShape J D]

variable (D) in
/-- The diagram `l ↦ ∏_k ∏_{l ⟶ k} A k`, i.e. the product over `k : J` of the right Kan extensions of the
objects `A k` along the inclusions of the points `k` of `J`. -/
abbrev coinducedPi (A : J → D) : J ⥤ D :=
  ∏ᶜ fun k => (evaluationRightAdjoint D k).obj (A k)

/-- Each value of `coinducedPi D A` is injective when all `A k` are. -/
theorem injective_coinducedPi_obj (A : J → D) [∀ k, Injective (A k)] (l : J) :
    Injective ((coinducedPi D A).obj l) := by
  have hinj : ∀ k, Injective (((evaluationRightAdjoint D k).obj (A k)).obj l) := fun k =>
    injective_evaluationRightAdjoint_obj_obj k (A k) l
  have e : (coinducedPi D A).obj l ≅
      ∏ᶜ fun k => ((evaluationRightAdjoint D k).obj (A k)).obj l :=
    (limitObjIsoLimitCompEvaluation (Discrete.functor fun k =>
      (evaluationRightAdjoint D k).obj (A k)) l).trans
      (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ ((evaluation J D).obj l)))
  exact Injective.of_iso e.symm inferInstance

/-- The canonical map `F ⟶ coinducedPi D A` induced by a family `φ k : F.obj k ⟶ A k`
(the adjuncts of the `φ k` under `evaluationAdjunctionLeft`). -/
def toCoinducedPi (F : J ⥤ D) (A : J → D) (φ : ∀ k, F.obj k ⟶ A k) : F ⟶ coinducedPi D A :=
  Pi.lift fun k => (evaluationAdjunctionLeft D k).homEquiv F (A k) (φ k)

/-- Composing `(toCoinducedPi F A φ).app l` with the projection to the factor `k = l` and the counit
(the projection to the factor `𝟙 l`) recovers `φ l`. -/
theorem toCoinducedPi_app_comp (F : J ⥤ D) (A : J → D) (φ : ∀ k, F.obj k ⟶ A k) (l : J) :
    (toCoinducedPi F A φ).app l ≫
      ((Pi.π (fun k => (evaluationRightAdjoint D k).obj (A k)) l).app l ≫
        (evaluationAdjunctionLeft D l).counit.app (A l)) = φ l := by
  rw [← Category.assoc, ← NatTrans.comp_app, toCoinducedPi, Pi.lift_π]
  have := (evaluationAdjunctionLeft D l).homEquiv_counit
    (g := (evaluationAdjunctionLeft D l).homEquiv F (A l) (φ l))
  simpa using this.symm

/-- If every `φ k` is a monomorphism, so is every component of `toCoinducedPi F A φ`. -/
theorem mono_toCoinducedPi_app (F : J ⥤ D) (A : J → D) (φ : ∀ k, F.obj k ⟶ A k)
    [∀ k, Mono (φ k)] (l : J) : Mono ((toCoinducedPi F A φ).app l) :=
  mono_of_mono_fac (toCoinducedPi_app_comp F A φ l)

/-- **Functorial injective embedding of a diagram.** Every diagram `F : J ⥤ D` in a category with enough
injectives, `J`-indexed products and `(a ⟶ b)`-indexed products admits a natural transformation
`ι : F ⟶ I` to a diagram of injective objects which is a monomorphism at every `j`.
(Stacks 01FF, proof, second paragraph; Stacks 01DI for the existence of injective embeddings.) -/
theorem exists_mono_injective_diagram [EnoughInjectives D] (F : J ⥤ D) :
    ∃ (I : J ⥤ D) (ι : F ⟶ I), (∀ j, Mono (ι.app j)) ∧ ∀ j, Injective (I.obj j) :=
  ⟨coinducedPi D fun k => Injective.under (F.obj k),
    toCoinducedPi F _ fun k => Injective.ι (F.obj k),
    mono_toCoinducedPi_app F _ _, injective_coinducedPi_obj _⟩

end

end CategoryTheory.Functor

end
