import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Explicit projective linear automorphisms of the canonical projective line

An invertible two-by-two matrix acts by linear substitution on the actual
homogeneous coordinate ring `k[X₀, X₁]`. Its adjugate divided by its determinant
gives the inverse substitution. Both substitutions preserve the total-degree
grading, so Mathlib's `Proj.map` constructs inverse scheme morphisms of the
canonical `ProjectiveSpace 1 k`. They preserve its specified morphism to `Spec k`.

The pullback of each homogeneous basic open under the image of the point `[1 : 0]`
(the section `pointOneZero`, private to this file) is computed by evaluating the
polynomial at the first matrix column. This is the coordinate action
`[1 : 0] ↦ [a : c]` for the matrix `[[a,b],[c,d]]`.

The projective line is written `ProjectiveSpace 1 k`, and the `[1 : 0]` section is kept here as a
private copy because this module is genuinely about that point. The distinguished point of `P¹`
elsewhere is `ProjectiveLine.zero k = [0 : 1]` (`ProjectiveLinePointZero`).
Classification of all scheme-valued rational points by homogeneous coordinates
and equality with a separately constructed coordinate morphism are not asserted.

Source: the proof of Lemma 5.1 of the paper, the final change of
parametrization on the selected rational component. These constructions support
`exists_projectiveLine_aut_over_base`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped HomogeneousIdeal

universe u

namespace AlgebraicGeometry.Proj.ProjectiveLineLinearAction

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-! ## The point `[1 : 0]` (private to this file) -/

variable (k) in
/-- Homogeneous coordinates of the point `[1 : 0]`. -/
private def pointOneZeroCoordinates : Fin 2 → k := ![1, 0]

variable (k) in
/-- Evaluation of homogeneous coordinates at `[1 : 0]`, as global sections of `Spec k`. -/
private def pointOneZeroEvaluation : MvPolynomial (Fin 2) k →+* Γ(Base k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
    (MvPolynomial.eval (pointOneZeroCoordinates k))

variable (k) in
private theorem pointOneZeroEvaluation_irrelevant :
    (HomogeneousIdeal.irrelevant (projectiveGrading k 1)).toIdeal.map
      (pointOneZeroEvaluation k) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hX : MvPolynomial.X (0 : Fin 2) ∈
      (HomogeneousIdeal.irrelevant (projectiveGrading k 1)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k 1) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X k 0)
  have hmem := Ideal.mem_map_of_mem (pointOneZeroEvaluation k) hX
  simpa [pointOneZeroEvaluation, pointOneZeroCoordinates] using hmem

variable (k) in
/-- The section `Spec k ⟶ P¹_k` represented by the homogeneous coordinates `[1 : 0]`
(`Proj.fromOfGlobalSections` applied to the evaluation at `[1 : 0]`). -/
private def pointOneZero : Base k ⟶ ProjectiveSpace 1 k :=
  Proj.fromOfGlobalSections (projectiveGrading k 1) (pointOneZeroEvaluation k)
    (pointOneZeroEvaluation_irrelevant k)

/-- The two linear forms obtained from the rows of a two-by-two matrix. -/
def linearForms (a b c d : k) : Fin 2 → MvPolynomial (Fin 2) k :=
  ![MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1,
    MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1]

/-- Linear substitution fixes the coefficient field and substitutes the two row forms. -/
def substitution (a b c d : k) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (linearForms a b c d)

@[simp]
theorem substitution_X_zero (a b c d : k) :
    substitution a b c d (MvPolynomial.X 0) =
      MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 := by
  simp [substitution, linearForms]

@[simp]
theorem substitution_X_one (a b c d : k) :
    substitution a b c d (MvPolynomial.X 1) =
      MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1 := by
  simp [substitution, linearForms]

/-- Polynomial substitution composes in the reverse order of the coordinate matrices. -/
theorem substitution_comp (a b c d e f g h : k) :
    (substitution a b c d).comp (substitution e f g h) =
      substitution (e * a + f * c) (e * b + f * d) (g * a + h * c) (g * b + h * d) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply, MvPolynomial.algebraMap_eq] <;> ring

/-- The identity matrix induces the identity algebra homomorphism. -/
@[simp]
theorem substitution_identity :
    substitution (1 : k) 0 0 1 = AlgHom.id k (MvPolynomial (Fin 2) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp

/-- Substitution by a matrix followed by substitution by its explicit inverse is the identity. -/
theorem substitution_comp_inverse (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (substitution a b c d).comp
        (substitution (d / (a * d - b * c)) (-b / (a * d - b * c))
          (-c / (a * d - b * c)) (a / (a * d - b * c))) =
      AlgHom.id k (MvPolynomial (Fin 2) k) := by
  have hdet' : d * a - b * c ≠ 0 := by rwa [mul_comm d a]
  have h00 : d / (a * d - b * c) * a + -b / (a * d - b * c) * c = 1 := by
    field_simp [hdet, hdet'] <;> ring
  have h01 : d / (a * d - b * c) * b + -b / (a * d - b * c) * d = 0 := by
    field_simp [hdet, hdet'] <;> ring
  have h10 : -c / (a * d - b * c) * a + a / (a * d - b * c) * c = 0 := by
    field_simp [hdet, hdet'] <;> ring
  have h11 : -c / (a * d - b * c) * b + a / (a * d - b * c) * d = 1 := by
    have h : -c / (a * d - b * c) * b + a / (a * d - b * c) * d
        = (a * d - b * c) / (a * d - b * c) := by ring
    rw [h, div_self hdet]
  rw [substitution_comp, h00, h01, h10, h11, substitution_identity]

/-- The explicit inverse substitution also cancels the original substitution on the other side. -/
theorem inverse_comp_substitution (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (substitution (d / (a * d - b * c)) (-b / (a * d - b * c))
        (-c / (a * d - b * c)) (a / (a * d - b * c))).comp
        (substitution a b c d) =
      AlgHom.id k (MvPolynomial (Fin 2) k) := by
  have hdet' : d * a - b * c ≠ 0 := by rwa [mul_comm d a]
  have h00 : a * (d / (a * d - b * c)) + b * (-c / (a * d - b * c)) = 1 := by
    field_simp [hdet, hdet'] <;> ring
  have h01 : a * (-b / (a * d - b * c)) + b * (a / (a * d - b * c)) = 0 := by
    field_simp [hdet, hdet'] <;> ring
  have h10 : c * (d / (a * d - b * c)) + d * (-c / (a * d - b * c)) = 0 := by
    field_simp [hdet, hdet'] <;> ring
  have h11 : c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c)) = 1 := by
    have h : c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c))
        = (a * d - b * c) / (a * d - b * c) := by ring
    rw [h, div_self hdet]
  rw [substitution_comp, h00, h01, h10, h11, substitution_identity]

/-- Every substituted variable is homogeneous of degree one. -/
theorem linearForms_homogeneous (a b c d : k) (i : Fin 2) :
    (linearForms a b c d i).IsHomogeneous 1 := by
  fin_cases i <;> dsimp [linearForms]
  · exact (MvPolynomial.isHomogeneous_C_mul_X a 0).add
      (MvPolynomial.isHomogeneous_C_mul_X b 1)
  · exact (MvPolynomial.isHomogeneous_C_mul_X c 0).add
      (MvPolynomial.isHomogeneous_C_mul_X d 1)

/-- Linear substitution, with its proof of preservation of every homogeneous degree. -/
def gradedSubstitution (a b c d : k) : projectiveGrading k 1 →+*ᵍ projectiveGrading k 1 where
  toRingHom := (substitution a b c d).toRingHom
  map_mem {i} {p} hp := by
    change p.IsHomogeneous i at hp
    change (MvPolynomial.aeval (linearForms a b c d) p).IsHomogeneous i
    simpa only [one_mul] using hp.aeval (linearForms a b c d) (linearForms_homogeneous a b c d)

/-- The inverse matrix induces the inverse graded substitution. -/
def inverseGradedSubstitution (a b c d : k) :
    projectiveGrading k 1 →+*ᵍ projectiveGrading k 1 :=
  gradedSubstitution (d / (a * d - b * c)) (-b / (a * d - b * c))
    (-c / (a * d - b * c)) (a / (a * d - b * c))

@[simp]
theorem gradedSubstitution_comp_inverse (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (gradedSubstitution a b c d).comp (inverseGradedSubstitution a b c d) =
      GradedRingHom.id (projectiveGrading k 1) := by
  apply GradedRingHom.ext
  intro p
  exact AlgHom.congr_fun (substitution_comp_inverse a b c d hdet) p

@[simp]
theorem inverse_comp_gradedSubstitution (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (inverseGradedSubstitution a b c d).comp (gradedSubstitution a b c d) =
      GradedRingHom.id (projectiveGrading k 1) := by
  apply GradedRingHom.ext
  intro p
  exact AlgHom.congr_fun (inverse_comp_substitution a b c d hdet) p

private theorem admissible_of_inverse
    (f g : projectiveGrading k 1 →+*ᵍ projectiveGrading k 1)
    (hfg : f.comp g = GradedRingHom.id (projectiveGrading k 1)) :
    (projectiveGrading k 1)₊ ≤ (projectiveGrading k 1)₊.map f := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro m hm p hp
  have hmem := g.map_mem hp
  have hirr := HomogeneousIdeal.mem_irrelevant_of_mem (projectiveGrading k 1) hm hmem
  have hmap := Ideal.mem_map_of_mem f.toRingHom hirr
  have hcomp : f (g p) = p := congrArg (fun h : projectiveGrading k 1 →+*ᵍ
      projectiveGrading k 1 ↦ h p) hfg
  change p ∈ Ideal.map f.toRingHom (HomogeneousIdeal.irrelevant (projectiveGrading k 1)).toIdeal
  change f (g p) ∈ Ideal.map f.toRingHom
    (HomogeneousIdeal.irrelevant (projectiveGrading k 1)).toIdeal at hmap
  rwa [hcomp] at hmap

/-- The image of the irrelevant ideal under an invertible substitution contains that ideal. -/
theorem gradedSubstitution_admissible (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (projectiveGrading k 1)₊ ≤ (projectiveGrading k 1)₊.map (gradedSubstitution a b c d) :=
  admissible_of_inverse _ _ (gradedSubstitution_comp_inverse a b c d hdet)

/-- The same irrelevant-ideal condition holds for the explicit inverse substitution. -/
theorem inverseGradedSubstitution_admissible (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (projectiveGrading k 1)₊ ≤ (projectiveGrading k 1)₊.map
      (inverseGradedSubstitution a b c d) :=
  admissible_of_inverse _ _ (inverse_comp_gradedSubstitution a b c d hdet)

set_option backward.isDefEq.respectTransparency false in
/-- The actual scheme automorphism of the canonical projective line defined by an
invertible matrix. -/
def schemeIso (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    ProjectiveSpace 1 k ≅ ProjectiveSpace 1 k where
  hom := Proj.map (gradedSubstitution a b c d) (gradedSubstitution_admissible a b c d hdet)
  inv := Proj.map (inverseGradedSubstitution a b c d)
    (inverseGradedSubstitution_admissible a b c d hdet)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [gradedSubstitution_comp_inverse a b c d hdet, Proj.map_id] <;> rfl
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [inverse_comp_gradedSubstitution a b c d hdet, Proj.map_id] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projective linear automorphism preserves the specified structure morphism to `Spec k`. -/
theorem schemeIso_hom_over_base (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (schemeIso a b c d hdet).hom ≫ (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) =
      (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) := by
  have hcoef : (gradedSubstitution a b c d).gradedZeroRingHom.comp
      (algebraMap k ((projectiveGrading k 1) 0)) =
      algebraMap k ((projectiveGrading k 1) 0) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    change substitution a b c d (MvPolynomial.C r) = MvPolynomial.C r
    simp [MvPolynomial.algebraMap_eq]
  change Proj.map (gradedSubstitution a b c d) _ ≫
      (Proj.toSpecZero (projectiveGrading k 1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k ((projectiveGrading k 1) 0)))) = _
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcoef]
  rfl

/-- The inverse automorphism is also over the same base field. -/
theorem schemeIso_inv_over_base (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    (schemeIso a b c d hdet).inv ≫ (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) =
      (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) := by
  apply (cancel_epi (schemeIso a b c d hdet).hom).1
  simp [schemeIso_hom_over_base]

/-- Evaluation after linear substitution sends the coordinates `[1 : 0]` to `[a : c]`. -/
theorem eval_zero_comp_substitution (a b c d : k) :
    (MvPolynomial.eval (pointOneZeroCoordinates k)).comp (substitution a b c d).toRingHom =
      MvPolynomial.eval (![a, c] : Fin 2 → k) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [MvPolynomial.algebraMap_eq]
  · intro i
    fin_cases i <;> simp [pointOneZeroCoordinates]

/-- Pullback of a homogeneous coordinate open along the automorphism. -/
theorem schemeIso_preimage_basicOpen (a b c d : k) (hdet : a * d - b * c ≠ 0)
    (p : MvPolynomial (Fin 2) k) :
    (schemeIso a b c d hdet).hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k 1) p =
      Proj.basicOpen (projectiveGrading k 1) (substitution a b c d p) := rfl

/-- The image of the point `[1 : 0]` has homogeneous coordinates given by the first matrix column.

This identity concerns the actual inverse images of homogeneous basic opens in `Spec k`. -/
theorem zero_comp_schemeIso_preimage_basicOpen
    (a b c d : k) (hdet : a * d - b * c ≠ 0)
    {p : MvPolynomial (Fin 2) k} {n : ℕ} (hn : 0 < n) (hp : p.IsHomogeneous n) :
    (pointOneZero k ≫ (schemeIso a b c d hdet).hom) ⁻¹ᵁ
        Proj.basicOpen (projectiveGrading k 1) p =
      (Base k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        (MvPolynomial.eval (![a, c] : Fin 2 → k) p)) := by
  change pointOneZero k ⁻¹ᵁ Proj.basicOpen (projectiveGrading k 1)
      (substitution a b c d p) = _
  have key : pointOneZero k ⁻¹ᵁ
      Proj.basicOpen (projectiveGrading k 1) (substitution a b c d p) =
      (Base k).basicOpen (pointOneZeroEvaluation k (substitution a b c d p)) :=
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn
      ((gradedSubstitution a b c d).map_mem hp)
  refine key.trans ?_
  change (Base k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((MvPolynomial.eval (pointOneZeroCoordinates k)) (substitution a b c d p))) = _
  have heval := RingHom.congr_fun (eval_zero_comp_substitution a b c d) p
  change (MvPolynomial.eval (pointOneZeroCoordinates k)) (substitution a b c d p) =
    MvPolynomial.eval (![a, c] : Fin 2 → k) p at heval
  rw [heval]

/-- The first column of an invertible matrix is nonzero. -/
theorem firstColumn_nonzero (a b c d : k) (hdet : a * d - b * c ≠ 0) :
    a ≠ 0 ∨ c ≠ 0 := by
  by_cases ha : a = 0
  · right
    intro hc
    apply hdet
    simp [ha, hc]
  · exact Or.inl ha

/-- Every nonzero column over a field extends to an invertible two-by-two matrix. -/
theorem exists_secondColumn (a c : k) (hcol : a ≠ 0 ∨ c ≠ 0) :
    ∃ b d : k, a * d - b * c ≠ 0 := by
  rcases hcol with ha | hc
  · exact ⟨0, 1, by simpa using ha⟩
  · exact ⟨1, 0, by simpa using hc⟩

/-- A nonzero coordinate pair is reached from `[1 : 0]` by an explicitly constructed projective
linear automorphism, expressed on all homogeneous basic opens. -/
theorem exists_schemeIso_with_coordinate_action (a c : k) (hcol : a ≠ 0 ∨ c ≠ 0) :
    ∃ e : ProjectiveSpace 1 k ≅ ProjectiveSpace 1 k,
      e.hom ≫ (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) = (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) ∧
      ∀ (p : MvPolynomial (Fin 2) k) (n : ℕ), 0 < n → p.IsHomogeneous n →
        (pointOneZero k ≫ e.hom) ⁻¹ᵁ Proj.basicOpen (projectiveGrading k 1) p =
          (Base k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
            (MvPolynomial.eval (![a, c] : Fin 2 → k) p)) := by
  obtain ⟨b, d, hdet⟩ := exists_secondColumn a c hcol
  refine ⟨schemeIso a b c d hdet, schemeIso_hom_over_base a b c d hdet, ?_⟩
  intro p n hn hp
  exact zero_comp_schemeIso_preimage_basicOpen a b c d hdet hn hp

end AlgebraicGeometry.Proj.ProjectiveLineLinearAction
