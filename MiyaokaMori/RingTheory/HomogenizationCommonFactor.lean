import MiyaokaMori.RingTheory.Polynomial.PrimitivePolynomialTuple

/-!
# Homogenizing a polynomial tuple and removing its common factor

The finite gcd and reduced tuple are those of `PrimitivePolynomialTuple`. All padding to
the prescribed degree belongs to the common homogeneous factor. The reduced homogeneous
tuple therefore has its actual maximum degree and no common nonzero zero.

The existing tuple API uses `[1:t]`. Swapping both the factor and reduced coordinates back
gives Mathlib's `[t:1]` homogenization in the conclusion. These are polynomial identities;
no projective morphism, pullback line bundle, or geometric degree is constructed here.

Source: the proof of Theorem 4.2 of the paper (removing the common factor of the
homogenized tuple).
-/

noncomputable section

namespace MiyaokaMori.RingTheory

open PrimitivePolynomialTuple PolynomialTupleHomogenization

universe u

/-- A nonzero bounded polynomial tuple admits a homogeneous factorization whose reduced
coordinates have no common nonzero zero, with all padding absorbed by the common factor. -/
theorem homogenize_and_remove_common_factor {K : Type u} [Field K] {N r₀ : ℕ}
    (P : Fin (N + 1) → Polynomial K)
    (hdeg : ∀ ℓ, (P ℓ).natDegree ≤ r₀) (hne : ∃ ℓ, P ℓ ≠ 0) :
    ∃ (m dD : ℕ) (Q : Fin (N + 1) → MvPolynomial (Fin 2) K)
      (D : MvPolynomial (Fin 2) K),
      m + dD = r₀ ∧ m ≤ r₀ ∧
      (∀ ℓ, (Q ℓ).IsHomogeneous m) ∧ D.IsHomogeneous dD ∧ D ≠ 0 ∧
      (∀ x : Fin 2 → K, x ≠ 0 → ∃ ℓ, MvPolynomial.eval x (Q ℓ) ≠ 0) ∧
      (∀ ℓ, (P ℓ).homogenize r₀ = D * Q ℓ) := by
  classical
  let s : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let m := maxDegree (reduced P)
  let d := (commonFactor P).natDegree
  let e := r₀ - (d + m)
  let D₀ : MvPolynomial (Fin 2) K :=
    MvPolynomial.X 0 ^ e * homog (commonFactor P) d
  let Q : Fin (N + 1) → MvPolynomial (Fin 2) K :=
    fun ℓ ↦ MvPolynomial.rename s (homogeneousCoordinates P ℓ)
  let D : MvPolynomial (Fin 2) K := MvPolynomial.rename s D₀
  have hsum : d + m ≤ r₀ :=
    (maxDegree_factorization P hne).le.trans (maxDegree_le P hdeg)
  have htotal : m + (e + d) = r₀ := calc
    m + (e + d) = e + (d + m) := by ac_rfl
    _ = r₀ := Nat.sub_add_cancel hsum
  have hswap : (s : Fin 2 → Fin 2) ∘ s = id := by
    funext i
    exact Equiv.swap_apply_self 0 1 i
  have hrename (p : Polynomial K) (r : ℕ) :
      MvPolynomial.rename s (homog p r) = p.homogenize r := by
    change MvPolynomial.rename s (MvPolynomial.rename s (p.homogenize r)) = _
    rw [MvPolynomial.rename_rename, hswap, MvPolynomial.rename_id_apply]
  have hg : homog (commonFactor P) d ≠ 0 := by
    intro hz
    apply commonFactor_ne_zero P hne
    apply Polynomial.eq_zero_of_homogenize_eq_zero (n := d) le_rfl
    exact (MvPolynomial.rename_eq_zero_iff_of_injective _ s.injective).mp hz
  have hD₀ : D₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero e (MvPolynomial.X_ne_zero (0 : Fin 2))) hg
  refine ⟨m, e + d, Q, D, htotal, maxDegree_reduced_le P hne hdeg, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ
    exact (isHomogeneous_homogeneousCoordinates P ℓ).rename_isHomogeneous
  · exact ((MvPolynomial.isHomogeneous_X_pow (0 : Fin 2) e).mul
      (isHomogeneous_homog (commonFactor P) d)).rename_isHomogeneous
  · exact fun hz ↦ hD₀ ((MvPolynomial.rename_eq_zero_iff_of_injective _ s.injective).mp hz)
  · intro x hx
    have hpair : x 1 ≠ 0 ∨ x 0 ≠ 0 := by
      by_cases h₁ : x 1 = 0
      · right
        intro h₀
        apply hx
        funext i
        fin_cases i <;> simp [h₀, h₁]
      · exact Or.inl h₁
    obtain ⟨ℓ, hℓ⟩ := exists_homogeneousCoordinates_eval₂_ne_zero P hne
      (RingHom.id K) (x 1) (x 0) hpair
    refine ⟨ℓ, ?_⟩
    change MvPolynomial.eval x (MvPolynomial.rename s (homogeneousCoordinates P ℓ)) ≠ 0
    rw [MvPolynomial.eval_rename]
    have hcoordinates : x ∘ s = ![x 1, x 0] := by
      funext i
      fin_cases i <;> simp [s]
    rw [hcoordinates]
    simpa only [MvPolynomial.eval₂_id] using hℓ
  · intro ℓ
    have h := congrArg (MvPolynomial.rename s)
      (homogenize_original_factorization P hne hdeg ℓ)
    rw [hrename] at h
    change (P ℓ).homogenize r₀ = MvPolynomial.rename s D₀ *
      MvPolynomial.rename s (homogeneousCoordinates P ℓ)
    simpa only [D₀, e, d, m, map_mul] using h

end MiyaokaMori.RingTheory
