import MiyaokaMori.Prelude

/-! # Polynomial rings over an integrally closed domain are integrally closed

`A` an integrally closed domain ⇒ `MvPolynomial σ A` is integrally closed, for **any** set of variables `σ`
(`MvPolynomial.isIntegrallyClosed`).

Reference: Stacks 030A (`R` normal ⇒ `R[x]` normal), by induction on the number of variables, then reduction
from finitely many variables to arbitrary `σ`. Mathlib has the one-variable instance
(`[IsDomain R] [IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`, the one-variable case of 030A) but no
`MvPolynomial` version.

Why the general (possibly infinite) `σ` is needed: the normality of the product of weighted projective charts
(`WeightedProjChartProdNormal`) is stated for an arbitrary index type `σ : Type u` (the paper only uses finite
`σ`, and its only user `weightedProjectiveSpace_prod_isNormal` has `[Fintype σ]`), so the infinite case must be
covered.

This is the single module for the statement: the finite case (`Fin n` by induction, then any finite `σ` by
`renameEquiv`) is a private step of the general proof, and every user takes
`MvPolynomial.isIntegrallyClosed σ A`.

## Natural-language proof

Step A (finitely many variables; private lemmas `isIntegrallyClosed_fin` / `isIntegrallyClosed_of_finite`):
1. Induction on `n` for `IsIntegrallyClosed (MvPolynomial (Fin n) A)`.
   `n = 0`: `MvPolynomial.isEmptyAlgEquiv A (Fin 0) : MvPolynomial (Fin 0) A ≃ₐ[A] A`, transport from `A` by
   `IsIntegrallyClosed.of_equiv`.
   `n+1`: `MvPolynomial.finSuccEquiv A n : MvPolynomial (Fin (n+1)) A ≃ₐ[A] (MvPolynomial (Fin n) A)[X]`; the
   induction hypothesis gives `MvPolynomial (Fin n) A` integrally closed, and it is a domain
   (`MvPolynomial.instIsDomain`), so Mathlib's one-variable instance gives `(MvPolynomial (Fin n) A)[X]`
   integrally closed; transport back by `of_equiv`.
2. General finite `σ`: take `e : σ ≃ Fin (Nat.card σ)`, `MvPolynomial.renameEquiv A e` and `of_equiv`.

Step B (any `σ`; reduction to finitely many variables):
Write `R := A[x_σ]`, `K := Frac R`. By `isIntegrallyClosed_iff K` it suffices: every `x ∈ K`
integral over `R` lies in `R`. Let `x = num/den` (`den ≠ 0`) and let `P ∈ R[T]` be monic with
`P(x) = 0`. Only finitely many variables occur in `num`, `den` and the finitely many coefficients
`P.coeff j` (`j ≤ deg P`): let `s ⊆ σ` be the finite set of all of them.
Let `R' := A[x_s]` and `φ : R' → R` the inclusion (`MvPolynomial.rename Subtype.val`, injective).
Then `num = φ num'`, `den = φ den'` (`MvPolynomial.mem_supported` / `supported_eq_range_rename`),
and `P = P'.map φ` for a monic `P' ∈ R'[T]` (`Polynomial.lifts_and_natDegree_eq_and_monic`).
Since `φ` is injective and `R` is a domain, `φ` maps nonzerodivisors to nonzerodivisors, so it
induces a (necessarily injective) field homomorphism `ψ : K' := Frac R' → K` with
`ψ (num'/den') = num/den = x`. Applying `ψ` to `P'(num'/den')` gives `P(x) = 0`, so
`P'(num'/den') = 0` by injectivity, i.e. `x' := num'/den'` is integral over `R'`. `R'` is
integrally closed (`s` finite), so `x' = y'/1` with `y' ∈ R'`, hence `x = ψ x' = φ y'/1 ∈ R`. ∎

Edge cases: `σ` empty or `s` empty are covered (then `R' = A` up to iso; in Step A, for `σ` empty the
conclusion is the integral closedness of `A` itself). `A` is a domain by hypothesis, so `R` is a domain
(`MvPolynomial.instIsDomain`); if `A` is a field both sides are UFDs and the conclusion is trivial.
`IsIntegrallyClosed` is defined in Mathlib for general commutative rings, but the one-variable instance requires
`IsDomain`, so this statement also carries `[IsDomain A]` (in our uses `A` is always a domain).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

noncomputable section

/-- Step A.1: polynomial rings in `Fin n` variables preserve integral closedness (induction on `n`). -/
private theorem MvPolynomial.isIntegrallyClosed_fin (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) A)
  | 0 => IsIntegrallyClosed.of_equiv
      (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv
  | (n + 1) => by
      haveI := MvPolynomial.isIntegrallyClosed_fin A n
      haveI : IsIntegrallyClosed (Polynomial (MvPolynomial (Fin n) A)) := inferInstance
      exact IsIntegrallyClosed.of_equiv
        (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv

/-- Step A.2: `A` an integrally closed domain, `σ` finite ⇒ `MvPolynomial σ A` is integrally closed. -/
private theorem MvPolynomial.isIntegrallyClosed_of_finite (σ : Type v) [Finite σ] (A : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] : IsIntegrallyClosed (MvPolynomial σ A) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  haveI := MvPolynomial.isIntegrallyClosed_fin A n
  exact IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv A e).symm.toRingEquiv

/-- `A` an integrally closed domain ⇒ `MvPolynomial σ A` is integrally closed, for **any** `σ`. -/
theorem MvPolynomial.isIntegrallyClosed (σ : Type v) (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : IsIntegrallyClosed (MvPolynomial σ A) := by
  classical
  let K := FractionRing (MvPolynomial σ A)
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨P, hPm, hP⟩ := hx
  obtain ⟨⟨num, den⟩, hxeq⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial σ A)) x
  dsimp only at hxeq
  subst hxeq
  let s : Finset σ := num.vars ∪ (den : MvPolynomial σ A).vars ∪
    (Finset.range (P.natDegree + 1)).biUnion fun j => (P.coeff j).vars
  let φ : MvPolynomial {x // x ∈ s} A →ₐ[A] MvPolynomial σ A :=
    MvPolynomial.rename Subtype.val
  have hφ : Function.Injective φ := MvPolynomial.rename_injective _ Subtype.val_injective
  have hmem : ∀ p : MvPolynomial σ A, p.vars ⊆ s → ∃ q, φ q = p := by
    intro p hp
    have := (MvPolynomial.mem_supported (R := A) (s := (↑s : Set σ))).mpr
      (Finset.coe_subset.mpr hp)
    rw [MvPolynomial.supported_eq_range_rename] at this
    exact this
  obtain ⟨num', hnum⟩ := hmem num (Finset.subset_union_left.trans Finset.subset_union_left)
  obtain ⟨den', hden⟩ := hmem den (Finset.subset_union_right.trans Finset.subset_union_left)
  have hden0 : den' ∈ nonZeroDivisors (MvPolynomial {x // x ∈ s} A) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    exact nonZeroDivisors.ne_zero den.2 (by rw [← hden, map_zero])
  have hPl : P ∈ Polynomial.lifts (φ : MvPolynomial {x // x ∈ s} A →+* MvPolynomial σ A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    by_cases hj : j ≤ P.natDegree
    · obtain ⟨q, hq⟩ := hmem (P.coeff j) (Finset.subset_union_right.trans'
        (Finset.subset_biUnion_of_mem (fun j => (P.coeff j).vars)
          (Finset.mem_range.mpr (by omega))))
      exact ⟨q, hq⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, map_zero _⟩
  obtain ⟨P', hP'map, -, hP'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hPl hPm
  let K' := FractionRing (MvPolynomial {x // x ∈ s} A)
  have : IsIntegrallyClosed (MvPolynomial {x // x ∈ s} A) :=
    MvPolynomial.isIntegrallyClosed_of_finite _ A
  have hle : nonZeroDivisors (MvPolynomial {x // x ∈ s} A) ≤
      (nonZeroDivisors (MvPolynomial σ A)).comap
        (φ : MvPolynomial {x // x ∈ s} A →+* MvPolynomial σ A) := by
    intro r hr
    rw [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff φ hφ).mpr (nonZeroDivisors.ne_zero hr))
  let ψ : K' →+* K := IsLocalization.map K (φ : MvPolynomial {x // x ∈ s} A →+* MvPolynomial σ A) hle
  have hψ : Function.Injective ψ := ψ.injective
  let x' : K' := IsLocalization.mk' K' num' ⟨den', hden0⟩
  have hx' : ψ x' = IsLocalization.mk' K num den := by
    simp only [x', ψ, IsLocalization.map_mk', AlgHom.coe_toRingHom, hnum]
    congr 1
    exact Subtype.ext hden
  have hint : IsIntegral (MvPolynomial {x // x ∈ s} A) x' := by
    refine ⟨P', hP'm, hψ ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, IsLocalization.map_comp, hx', ← Polynomial.eval₂_map,
      hP'map]
    exact hP
  obtain ⟨y', hy'⟩ := (isIntegrallyClosed_iff K').mp inferInstance hint
  refine ⟨φ y', ?_⟩
  rw [← hx', ← hy']
  exact (IsLocalization.map_eq (S := K') (Q := K) hle y').symm

end
