import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleOnOpen
import Mathlib.AlgebraicGeometry.Gluing
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio
import MiyaokaMori.RingTheory.PolynomialJetNonscalar
import Mathlib.Algebra.Polynomial.AlgebraMap
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Field points of the standard projective charts

The chart data of `D₊(Xⱼ) ⊆ P^n` — the coordinate ratios `Xᵢ/Xⱼ` (`ratioElement`, `ratioSection`),
the ring map `(k[X]_{Xⱼ})_0 → S` induced by an evaluation `e` with `e(Xⱼ)` a unit (`chartEvaluation`),
the chart morphism `T → D₊(Xⱼ)` (`chartMap`) and the lemmas `chartEvaluation_ratio_mul`, `chartMap_ι`,
`chartMap_appTop_ratio`, `chartMap_appTop_ratio_mul` — are **`ProjectiveSpaceOverChart.*`**
(`ProjectiveSpaceOverChartRatio`, over any commutative ring `R`).
This file contains the field-specific constructions about that definition:

* `fieldEvaluation`: a tuple `p : Fin (n+1) → F` in a field extension `F/k` as an evaluation
  `k[X] → Γ(Spec F, O)`;
* `fieldTupleMorphism`: the induced morphism `Spec F → P^n_k` over `k` (`Proj.fromOfGlobalSections`);
* `fieldTuple_pullback_ratio`: under `Γ(Spec F, O) ≅ F`, the pullback of `Xᵢ/Xⱼ` along the chart map is `pᵢ/pⱼ`.

`fieldTupleMorphism` is a scheme morphism, over `k` by `fieldTupleMorphism_over`.

Sources: Theorem 4.2 of the paper (§4); Stacks Project, `constructions.tex`,
`lemma-proj-scheme`, `lemma-projective-space`, and `lemma-standard-covering-projective-space`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj.ProjectiveCoordinateRatio

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveSpaceOverChart

section FieldTuple

variable {F : Type u} [Field F] [Algebra k F]

/-- Homogeneous tuple evaluation in the actual global sections of `Spec F`. -/
def fieldEvaluation (n : ℕ) (p : Fin (n + 1) → F) :
    MvPolynomial (Fin (n + 1)) k →+* Γ(Spec (CommRingCat.of F), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.comp
    (MvPolynomial.eval₂Hom (algebraMap k F) p)

private theorem fieldEvaluation_variable_isUnit (n : ℕ) (p : Fin (n + 1) → F)
    (j : Fin (n + 1)) (hj : p j ≠ 0) :
    IsUnit (fieldEvaluation (k := k) n p (MvPolynomial.X j)) := by
  simpa only [fieldEvaluation, RingHom.comp_apply, MvPolynomial.eval₂Hom_X'] using
    (isUnit_iff_ne_zero.mpr hj).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

private theorem fieldEvaluation_irrelevant (n : ℕ) (p : Fin (n + 1) → F)
    (j : Fin (n + 1)) (hj : p j ≠ 0) :
    (HomogeneousIdeal.irrelevant (projectiveGrading k n)).toIdeal.map
      (fieldEvaluation n p) = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (fieldEvaluation n p)
      (HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k n) Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X k j)))
    (fieldEvaluation_variable_isUnit n p j hj)

/-- The canonical projective tuple morphism `Spec F ⟶ P^n`; it is a morphism over `k` (structure
morphism of `Spec F` induced by `algebraMap k F`) by `fieldTupleMorphism_over`. No auxiliary field
model is introduced. -/
def fieldTupleMorphism (n : ℕ) (p : Fin (n + 1) → F) (j : Fin (n + 1)) (hj : p j ≠ 0) :
    Spec (CommRingCat.of F) ⟶ (ProjectiveSpace n k) :=
  Proj.fromOfGlobalSections (projectiveGrading k n) (fieldEvaluation n p)
    (fieldEvaluation_irrelevant n p j hj)

/-- The canonical projective tuple morphism is a morphism over `k`. -/
theorem fieldTupleMorphism_over (n : ℕ) (p : Fin (n + 1) → F) (j : Fin (n + 1)) (hj : p j ≠ 0) :
    fieldTupleMorphism (k := k) n p j hj ≫ (ProjectiveSpace n k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k F)) := by
    change Proj.fromOfGlobalSections _ _ _ ≫ (Proj.toSpecZero _ ≫ Spec.map _) = _
    rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have heval : ((fieldEvaluation (k := k) n p).comp
        (algebraMap ((projectiveGrading k n) 0) (MvPolynomial (Fin (n + 1)) k))).comp
          (algebraMap k ((projectiveGrading k n) 0)) =
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.comp (algebraMap k F) := by
      ext c
      simp [fieldEvaluation]
    rw [heval, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
    change ((Spec (CommRingCat.of F)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv) ≫ _ = _
    rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- Under `Γ(Spec F,O) ≅ F`, the pullback of the actual projective ratio is `pᵢ/pⱼ`. -/
theorem fieldTuple_pullback_ratio (n : ℕ) (p : Fin (n + 1) → F)
    (j : Fin (n + 1)) (hj : p j ≠ 0) (i : Fin (n + 1)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((chartMap (Spec (CommRingCat.of F)) n (fieldEvaluation (k := k) n p) j
        (fieldEvaluation_variable_isUnit n p j hj)).appTop (ratioSection n i j)) =
      p i / p j := by
  apply (eq_div_iff hj).mpr
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom
    (chartMap_appTop_ratio_mul (Spec (CommRingCat.of F)) n (fieldEvaluation (k := k) n p) j
      (fieldEvaluation_variable_isUnit n p j hj) i)
  simpa only [map_mul, fieldEvaluation, RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
    Iso.inv_hom_id_apply] using h

end FieldTuple


end AlgebraicGeometry.Proj.ProjectiveCoordinateRatio
