import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Mathlib.Tactic.FinCases
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Varieties.RationalPointDef

/-!
# Coordinates of rational points of the projective line

Construction of the homogeneous coordinates of a rational point of `P^1 = ProjectiveSpace 1 k`
from the standard charts. The full classification theorem of rational points by homogeneous
coordinates is not asserted here.

Source: Stacks, Tags 01NG and 01MB; Mathlib Proj chart and open-immersion API.

`P^1` is `ProjectiveSpace 1 k`, its structure morphism is `ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)`,
and its rational points are `Scheme.rationalPoint k (ProjectiveSpace 1 k)` (`RationalPointDef`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

theorem adjoin_variables :
    Algebra.adjoin ((projectiveGrading k 1) 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact (Algebra.adjoin ((projectiveGrading k 1) 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k))).algebraMap_mem
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin 2) r⟩
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem coordinateOpens_cover :
    (⨆ i : Fin 2, Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (projectiveGrading k 1) MvPolynomial.X
    (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩) adjoin_variables

theorem exists_coordinateOpen (x : (ProjectiveSpace 1 k)) :
    ∃ i : Fin 2, x ∈ Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i) := by
  dsimp only [ProjectiveSpace, ProjectiveSpaceOver] at x ⊢
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [coordinateOpens_cover (k := k)]
  trivial

theorem rationalPoint_exists_coordinateOpen (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) :
    ∃ i : Fin 2, p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i) :=
  exists_coordinateOpen (p.1 (IsLocalRing.closedPoint k))

abbrev chartRing (i : Fin 2) :=
  HomogeneousLocalization.Away (projectiveGrading k 1) (MvPolynomial.X i)

abbrev chartι (i : Fin 2) : Spec (CommRingCat.of (chartRing (k := k) i)) ⟶
    (ProjectiveSpace 1 k) :=
  Proj.awayι (projectiveGrading k 1) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)

def chartCoefficient (i : Fin 2) : k →+* chartRing (k := k) i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading k 1)
    (Submonoid.powers (MvPolynomial.X i))).comp
      (algebraMap k ((projectiveGrading k 1) 0))

set_option backward.isDefEq.respectTransparency false in
theorem chartι_over_base (i : Fin 2) :
    chartι (k := k) i ≫ (ProjectiveSpace 1 k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (chartCoefficient (k := k) i)) := by
  change Proj.awayι (projectiveGrading k 1) (MvPolynomial.X i) _ _ ≫
      (Proj.toSpecZero (projectiveGrading k 1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k ((projectiveGrading k 1) 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem rationalPoint_range_chart (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    Set.range p.1 ⊆ Set.range (chartι (k := k) i) := by
  have : IsOpenImmersion (chartι (k := k) i) := by
    exact Proj.instIsOpenImmersionAwayι (projectiveGrading k 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)
  rintro x ⟨z, rfl⟩
  have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hmem : p.1 z ∈ Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i) :=
    hz.symm ▸ hi
  exact (SetLike.ext_iff.mp
    (Proj.opensRange_awayι (projectiveGrading k 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)) (p.1 z)).mpr hmem

def chartPointHom (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    Base k ⟶ Spec (CommRingCat.of (chartRing (k := k) i)) := by
  have : IsOpenImmersion (chartι (k := k) i) := by
    exact Proj.instIsOpenImmersionAwayι (projectiveGrading k 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)
  exact IsOpenImmersion.lift (chartι (k := k) i) p.1 (rationalPoint_range_chart p i hi)

theorem chartPointHom_fac (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    chartPointHom p i hi ≫ chartι (k := k) i = p.1 := by
  have : IsOpenImmersion (chartι (k := k) i) := by
    exact Proj.instIsOpenImmersionAwayι (projectiveGrading k 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)
  exact IsOpenImmersion.lift_fac _ _ _

def chartEvaluation (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    chartRing (k := k) i →+* k :=
  (Spec.preimage (chartPointHom p i hi)).hom

theorem chartEvaluation_fac (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    Spec.map (CommRingCat.ofHom (chartEvaluation p i hi)) ≫ chartι (k := k) i = p.1 := by
  change Spec.map (Spec.preimage (chartPointHom p i hi)) ≫ chartι (k := k) i = _
  rw [Spec.map_preimage, chartPointHom_fac]

theorem chartEvaluation_coefficient (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    (chartEvaluation p i hi).comp (chartCoefficient (k := k) i) = RingHom.id k := by
  have h : CommRingCat.ofHom ((chartEvaluation p i hi).comp
      (chartCoefficient (k := k) i)) = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_id,
      ← chartι_over_base, ← Category.assoc, chartEvaluation_fac, p.2]
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k ↦ f.hom) h

def coordinateRatio (i j : Fin 2) : chartRing (k := k) i :=
  HomogeneousLocalization.Away.mk (projectiveGrading k 1)
    (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X j)
    (by simpa using MvPolynomial.isHomogeneous_X k j)

@[simp]
theorem coordinateRatio_self (i : Fin 2) : coordinateRatio (k := k) i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one]
  change Localization.mk (MvPolynomial.X i)
    (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X (R := k) i)) = 1
  simpa only [pow_one] using
    (Localization.mk_self (⟨MvPolynomial.X i, 1, by simp⟩ :
      Submonoid.powers (MvPolynomial.X (R := k) i)))

def dehomogenization (i : Fin 2) : MvPolynomial (Fin 2) k →+* chartRing (k := k) i :=
  MvPolynomial.eval₂Hom (chartCoefficient (k := k) i) (coordinateRatio (k := k) i)

def normalizedCoordinates (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) : Fin 2 → k :=
  fun j ↦ chartEvaluation p i hi (coordinateRatio (k := k) i j)

@[simp]
theorem normalizedCoordinates_self (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    normalizedCoordinates p i hi i = 1 := by
  simp [normalizedCoordinates]

theorem normalizedCoordinates_nonzero (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    normalizedCoordinates p i hi 0 ≠ 0 ∨ normalizedCoordinates p i hi 1 ≠ 0 := by
  fin_cases i
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem chartEvaluation_dehomogenization
    (p : AlgebraicGeometry.Scheme.rationalPoint k (ProjectiveSpace 1 k)) (i : Fin 2)
    (hi : p.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k 1) (MvPolynomial.X i)) :
    (chartEvaluation p i hi).comp (dehomogenization (k := k) i) =
      MvPolynomial.eval (normalizedCoordinates p i hi) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, dehomogenization, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval_C]
    exact RingHom.congr_fun (chartEvaluation_coefficient p i hi) r
  · intro j
    simp [dehomogenization, normalizedCoordinates]

/-- The constant fraction is represented by the ordinary localization numerator and unit denominator. -/
theorem val_chartCoefficient (i : Fin 2) (r : k) :
    (chartCoefficient (k := k) i r).val =
      Localization.mk (MvPolynomial.C r)
        (1 : Submonoid.powers (MvPolynomial.X i)) := rfl

/-- Coordinate ratios are represented by the expected ordinary localization fractions. -/
theorem val_coordinateRatio (i j : Fin 2) :
    (coordinateRatio (k := k) i j).val =
      Localization.mk (MvPolynomial.X j)
        (⟨MvPolynomial.X i, 1, by simp⟩ : Submonoid.powers (MvPolynomial.X i)) := by
  change Localization.mk (MvPolynomial.X j)
    (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X (R := k) i)) = _
  simp only [pow_one]

/-- Dehomogenization of one monomial in the ordinary localization.  The denominator exponent is
the (unweighted) degree of the monomial, so this helper does not make a homogeneity assumption. -/
private theorem val_dehomogenization_monomial (i : Fin 2) (d : Fin 2 →₀ ℕ) (r : k) :
    (dehomogenization (k := k) i (MvPolynomial.monomial d r)).val =
      Localization.mk (MvPolynomial.monomial d r)
        (⟨MvPolynomial.X i ^ d.degree, d.degree, rfl⟩ : Submonoid.powers (MvPolynomial.X i)) := by
  change algebraMap (chartRing (k := k) i) (Localization.Away (MvPolynomial.X (R := k) i))
    (dehomogenization (k := k) i (MvPolynomial.monomial d r)) = _
  rw [dehomogenization, MvPolynomial.eval₂Hom_monomial]
  rw [MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow,
    HomogeneousLocalization.algebraMap_apply, val_chartCoefficient, val_coordinateRatio,
    Localization.mk_pow, Localization.mk_prod, Localization.mk_mul, one_mul]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-- A homogeneous polynomial of degree `n` dehomogenizes to the fraction `f / Xᵢⁿ`.

This is an equality in the degree-zero localization, proved by weighted-homogeneous induction
and the localization normal forms. -/
theorem dehomogenization_of_homogeneous (i : Fin 2)
    {n : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous n) :
    dehomogenization (k := k) i f =
      HomogeneousLocalization.Away.mk (projectiveGrading k 1)
        (MvPolynomial.isHomogeneous_X k i) n f (by simpa using hf)
  := by
  apply HomogeneousLocalization.val_injective
  change (dehomogenization (k := k) i f).val =
    Localization.mk f
      (⟨MvPolynomial.X i ^ n, n, rfl⟩ : Submonoid.powers (MvPolynomial.X (R := k) i))
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [dehomogenization, Localization.mk_zero]
  | add p q hp hq ihp ihq =>
      rw [map_add, HomogeneousLocalization.val_add, ihp, ihq, Localization.add_mk_self]
  | monomial d r hd =>
      have hdeg : d.degree = n := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      simpa [hdeg] using val_dehomogenization_monomial i d r

end AlgebraicGeometry.Proj.ProjectiveLinePointCoordinates
