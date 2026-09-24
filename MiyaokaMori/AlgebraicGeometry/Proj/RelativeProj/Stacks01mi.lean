import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjToSpecZeroIsoOfDegreeOneGenerator

/-! # Proj of `A[T]` is `Spec A` (Stacks 01MI)

Stacks 01MI (Constructions, Example): the structure morphism of `Proj A[T]` (with `T` of degree 1)
is an isomorphism onto `Spec A`; that is, the blowup along the unit ideal (empty centre) is the
identity. This is the step "`X' = X` when the centre is empty" in the proof of Stacks 02OS(1), used
for the resolution in Corollary 4.3 of the paper.

**Proof.** Apply the abstract form `Proj.isIso_toSpecZero_of_degreeOne_generator`
(`ProjToSpecZeroIsoOfDegreeOneGenerator.lean`) to `𝒜 = homogeneousSubmodule (Fin 1) A`
and `t = X 0 ∈ 𝒜 1`. The two hypotheses are that multiplication by `X 0` is a bijection
`𝒜 n → 𝒜 (n+1)`; both follow from the one-variable normal form
`IsHomogeneous.eq_C_mul_X_pow_fin_one`: a homogeneous polynomial `p` of degree `m` in one variable is
`C (coeff (single 0 m) p) * X 0 ^ m` (every exponent vector on `Fin 1` is `single 0 k`, and the only
one of degree `m` is `single 0 m`).
- injectivity: `x = C c * X 0 ^ n`, `x * X 0 = C c * X 0 ^ (n+1) = 0` ⇒ the coefficient `c` at
  `single 0 (n+1)` is `0` ⇒ `x = 0`;
- surjectivity: `y = C c * X 0 ^ (n+1) = (C c * X 0 ^ n) * X 0` with `C c * X 0 ^ n ∈ 𝒜 n`.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open MvPolynomial

noncomputable section

/-- A homogeneous polynomial of degree `m` in one variable is `c * X ^ m`, where `c` is its
coefficient at the monomial `X ^ m`. -/
theorem MvPolynomial.IsHomogeneous.eq_C_mul_X_pow_fin_one {A : Type u} [CommRing A]
    {p : MvPolynomial (Fin 1) A} {m : ℕ} (hp : p.IsHomogeneous m) :
    p = C (coeff (Finsupp.single 0 m) p) * X 0 ^ m := by
  ext d
  rw [coeff_C_mul, coeff_X_pow]
  have hd : d = Finsupp.single (0 : Fin 1) (d 0) := Finsupp.unique_single d
  by_cases h : Finsupp.single (0 : Fin 1) m = d
  · subst h; simp
  · rw [if_neg h, mul_zero]
    apply hp.coeff_eq_zero
    intro hdeg
    apply h
    rw [hd, Finsupp.degree_single] at hdeg
    rw [hd, hdeg]

theorem AlgebraicGeometry.Proj.toSpecZero_isIso_polynomial (A : Type u) [CommRing A] :
    letI := MvPolynomial.gradedAlgebra (σ := Fin 1) (R := A)
    CategoryTheory.IsIso
      (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 1) A)) := by
  let _ := MvPolynomial.gradedAlgebra (σ := Fin 1) (R := A)
  refine AlgebraicGeometry.Proj.isIso_toSpecZero_of_degreeOne_generator
    (homogeneousSubmodule (Fin 1) A) (t := X 0) (isHomogeneous_X A 0) ?_ ?_
  · intro n x hx hx0
    rw [mem_homogeneousSubmodule] at hx
    rw [hx.eq_C_mul_X_pow_fin_one] at hx0 ⊢
    have hc := congrArg (coeff (Finsupp.single (0 : Fin 1) (n + 1))) hx0
    rw [mul_assoc, ← pow_succ, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, coeff_zero] at hc
    rw [hc, C_0, zero_mul]
  · intro n y hy
    rw [mem_homogeneousSubmodule] at hy
    refine ⟨C (coeff (Finsupp.single (0 : Fin 1) (n + 1)) y) * X 0 ^ n,
      isHomogeneous_C_mul_X_pow _ _ _, ?_⟩
    rw [mul_assoc, ← pow_succ]
    exact hy.eq_C_mul_X_pow_fin_one.symm

end
