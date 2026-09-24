import MiyaokaMori.Prelude

/-! # Conjugation of an upper triangular matrix by `Λ(λ) = diag(λ, …, λ^r)`

The **explicit** form of the `Λ(λ)`-conjugate of an upper triangular matrix `g`:
`(lambdaConjugate g) i j = C (g i j) * X^(j-i)`, with coefficients in `R[X]`. At `λ = 1` it is `g`,
at `λ = 0` it is `diag(g_ii)`, and where `λ` is invertible it is `Λ(λ)⁻¹ g Λ(λ)`. Conjugation
commutes with transporting the coefficients along a ring homomorphism, and it is **multiplicative on
upper triangular matrices**: `lambdaConjugate g * lambdaConjugate h = lambdaConjugate (g * h)`.
The last statement is the direct verification that conjugation preserves the cocycle condition also
at `λ = 0`, used in the reduction to a split weighted bundle (Lemma 2.3 of the
paper); writing the matrices
explicitly makes the cocycle condition checkable.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open Polynomial

namespace Matrix

/-- The `Λ(λ)`-conjugate of an upper triangular matrix `g`: the `(i, j)` entry is
`g i j · λ^{j - i}` (truncated subtraction; for `j < i` one has `g i j = 0`). -/
def lambdaConjugate {R : Type*} [CommRing R] {r : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    Matrix (Fin r) (Fin r) R[X] :=
  fun i j => Polynomial.C (g i j) * Polynomial.X ^ ((j : ℕ) - (i : ℕ))

theorem lambdaConjugate_apply {R : Type*} [CommRing R] {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (i j : Fin r) :
    g.lambdaConjugate i j = Polynomial.C (g i j) * Polynomial.X ^ ((j : ℕ) - (i : ℕ)) := rfl

theorem lambdaConjugate_blockTriangular {R : Type*} [CommRing R] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (hg : g.BlockTriangular id) :
    g.lambdaConjugate.BlockTriangular id := by
  intro i j hji
  simp [lambdaConjugate, hg hji]

/-- Conjugation commutes with mapping the coefficients along a ring homomorphism. -/
theorem lambdaConjugate_map {R S : Type*} [CommRing R] [CommRing S] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : R →+* S) :
    g.lambdaConjugate.map (Polynomial.mapRingHom f) = (g.map f).lambdaConjugate := by
  ext i j
  simp [lambdaConjugate, Matrix.map_apply]

/-- At `λ = 1` the conjugate is `g`. -/
theorem lambdaConjugate_eval_one {R : Type*} [CommRing R] {r : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    g.lambdaConjugate.map (Polynomial.evalRingHom 1) = g := by
  ext i j
  simp [lambdaConjugate, Matrix.map_apply]

/-- At `λ = 0` the conjugate is the diagonal matrix `diag(g_ii)` (uses upper triangularity). -/
theorem lambdaConjugate_eval_zero {R : Type*} [CommRing R] {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hg : g.BlockTriangular id) :
    g.lambdaConjugate.map (Polynomial.evalRingHom 0) = Matrix.diagonal (fun a => g a a) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [lambdaConjugate, Matrix.map_apply]
  · rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ hij]
    by_cases hlt : i < j
    · have hsub : (j : ℕ) - (i : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)
      simp [lambdaConjugate, hsub]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp [lambdaConjugate, hg hji]

/-- For upper triangular matrices conjugation is multiplicative:
`(gh)_{ij} λ^{j-i} = Σ_l g_{il} λ^{l-i} · h_{lj} λ^{j-l}` (only the terms with `i ≤ l ≤ j` are
nonzero, and then `(l-i)+(j-l) = j-i`). -/
theorem lambdaConjugate_mul {R : Type*} [CommRing R] {r : ℕ} (g h : Matrix (Fin r) (Fin r) R)
    (hg : g.BlockTriangular id) (hh : h.BlockTriangular id) :
    g.lambdaConjugate * h.lambdaConjugate = (g * h).lambdaConjugate := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, lambdaConjugate]
  rw [_root_.map_sum (Polynomial.C : R →+* R[X]), Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hli : l < i
  · have : g i l = 0 := hg hli
    simp [this]
  by_cases hjl : j < l
  · have : h l j = 0 := hh hjl
    simp [this]
  have hil : (i : ℕ) ≤ (l : ℕ) := le_of_not_gt hli
  have hlj : (l : ℕ) ≤ (j : ℕ) := le_of_not_gt hjl
  have hexp : (l : ℕ) - (i : ℕ) + ((j : ℕ) - (l : ℕ)) = (j : ℕ) - (i : ℕ) := by omega
  rw [← hexp, pow_add, _root_.map_mul]
  ring

/-- If `g` is upper triangular with invertible determinant, so is its conjugate (the determinant is
the product of the diagonal entries, i.e. `C (det g)`). -/
theorem lambdaConjugate_det_isUnit {R : Type*} [CommRing R] {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hg : g.BlockTriangular id) (hinv : IsUnit g.det) : IsUnit g.lambdaConjugate.det := by
  rw [Matrix.det_of_isUpperTriangular (lambdaConjugate_blockTriangular g hg)]
  have hdiag : ∏ i, g.lambdaConjugate i i = Polynomial.C (∏ i, g i i) := by
    simp [lambdaConjugate, map_prod]
  rw [hdiag, ← Matrix.det_of_isUpperTriangular hg]
  exact Polynomial.isUnit_C.mpr hinv

end Matrix

end
