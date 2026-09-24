import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.HomogenizationCommonFactor
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectiveLineFormsBridges
import MiyaokaMori.RingTheory.PolynomialTupleHomogenization

/-! # Degree of the map `P¹ → P^N` induced by a polynomial tuple

A tuple of polynomials of degree `≤ r_0` induces on a fiber `P¹` a map whose `O(1)`-degree `m`
satisfies `m ≤ r_0`; if the map is nonconstant then `m ≥ 1`.

Source: Theorem 4.2 and Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem p1_map_degree_of_polynomial_tuple {K : Type u} [Field K] [IsAlgClosed K] {N r₀ : ℕ}
    (P : Fin (N + 1) → Polynomial K)
    (hdeg : ∀ ℓ, (P ℓ).degree ≤ (r₀ : WithBot ℕ)) (hne : ∃ ℓ, P ℓ ≠ 0) :
    ∃ (m : ℕ) (g : (ProjectiveLine.asSmoothProjectiveCurve K).toVariety.toScheme ⟶ ProjectiveSpace N K),
      m ≤ r₀ ∧
      (¬ IsConstantMorphism g → 1 ≤ m) ∧
      (LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve K).toVariety)
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (projectiveSpaceTwist K N 1))).degree
        = (m : ℤ) ∧
      ∀ (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of K))).Opens)
        (hO : ∀ v : O.toScheme, ∃ ℓ, ¬ IsZeroAt (polynomialSection O (P ℓ)) v),
        O.ι ≫ ProjectiveLine.stdChart K ≫ g
          = projectivizationMorphism (k := K) (SheafOfModules.unit O.toScheme.ringCatSheaf)
              (fun ℓ => polynomialSection O (P ℓ)) hO := by
  have hnat : ∀ ℓ, (P ℓ).natDegree ≤ r₀ := fun ℓ ↦
    Polynomial.natDegree_le_of_degree_le (hdeg ℓ)
  obtain ⟨m, dD, Q, D, hsum, hm, hQ, hD, hD0, hQ0, hfac⟩ :=
    MiyaokaMori.RingTheory.homogenize_and_remove_common_factor P hnat hne
  -- `homogenize_and_remove_common_factor` uses Mathlib's `Polynomial.homogenize`
  -- (`X 0` = affine variable), but `stdChart` is the chart `t ↦ [1 : t]`; so we swap the two variables
  -- (`homog = rename (swap 0 1) ∘ homogenize`) before building the morphism of forms.
  let Q' : Fin (N + 1) → MvPolynomial (Fin 2) K :=
    fun j => MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (Q j)
  let D' : MvPolynomial (Fin 2) K := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) D
  have hQ' : ∀ j, (Q' j).IsHomogeneous m := fun j => (hQ j).rename_isHomogeneous
  have hD' : D'.IsHomogeneous dD := hD.rename_isHomogeneous
  have hD0' : D' ≠ 0 := by
    intro h
    apply hD0
    exact MvPolynomial.rename_injective (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _)
      (by rw [map_zero]; exact h)
  have hQ0' : ∀ v : Fin 2 → K, v ≠ 0 → ∃ j, MvPolynomial.eval v (Q' j) ≠ 0 := by
    intro v hv
    obtain ⟨j, hj⟩ := hQ0 (v ∘ Equiv.swap (0 : Fin 2) 1) (by
      intro h
      apply hv
      funext i
      have := congrFun h ((Equiv.swap (0 : Fin 2) 1).symm i)
      simpa using this)
    exact ⟨j, by simpa [Q', MvPolynomial.eval_rename] using hj⟩
  have hfac' : ∀ j, MiyaokaMori.RingTheory.PolynomialTupleHomogenization.homog (P j) r₀ = D' * Q' j := by
    intro j
    rw [MiyaokaMori.RingTheory.PolynomialTupleHomogenization.homog, hfac j, map_mul]
  let g : (ProjectiveLine.asSmoothProjectiveCurve K).toVariety.toScheme ⟶
      ProjectiveSpace N K := ProjectiveLine.morphismOfForms Q' hQ' hQ0'
  refine ⟨m, g, hm, ?_, ?_, ?_⟩
  · intro hnc
    exact ProjectiveLine.one_le_degree_of_nonconstant_morphismOfForms Q' hQ' hQ0' hnc
  · change LineBundle.degree (C := ProjectiveLine.asSmoothProjectiveCurve K)
        (LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve K).toVariety)
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (ProjectiveLine.morphismOfForms Q' hQ' hQ0')).obj
              (projectiveSpaceTwist K N 1))) = (m : ℤ)
    exact ProjectiveLine.degree_pullback_twist_of_forms Q' hQ' hQ0'
  · intro O hO
    exact ProjectiveLine.morphismOfForms_stdChart_polynomialSection_homog P hnat Q' D' hQ' hD' hD0'
      hQ0' hfac' O hO

end
