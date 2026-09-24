import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Pure degree eval weighted homogeneous

Pure algebra behind `BasedJet.symCoeffHom_jetPoint_partι_of_ne`:
a family of additive "coefficient" maps `c p : T →+ M p` (`p : ℕ`) on a commutative ring `T` such that the
product of an element of pure degree `m` and one of pure degree `n` has pure degree `m + n`
("pure degree `m`" = all coefficients `c p`, `p ≠ m`, vanish). Then

* powers and finite products of pure elements are pure of the summed degree (`isPure_pow`, `isPure_prod`);
* if `Ψ : MvPolynomial σ R →+* T` sends constants to pure degree `0` and the variable `X i` to pure degree
  `w i`, then it sends every `w`-weighted-homogeneous polynomial of weight `m` to pure degree `m`
  (`isPure_eval_of_isWeightedHomogeneous`; induction `MvPolynomial.IsWeightedHomogeneous.induction_on`,
  monomial case via `MvPolynomial.monomial_eq` and `Finsupp.weight_apply`).

In the application `T = Γ(Tot(L), p⁻¹V)`, `c p = symCoeffHom L p` (the `p`-th ξ-coefficient), the product
hypothesis is `BasedJet.symCoeffHom_mul_of_homogeneous` (proved), and `Ψ = φ_J^♯ ∘ χ_U ∘ mk` on the jet chart
ring `J_κ(B_U, ε_U) = MvPolynomial (Fin κ × B_U) Γ(C,U) ⧸ relations`.

Source: §3 of the paper (functions on `Tot(L)` are graded by ξ-degree, multiplication adds degrees).
-/

set_option autoImplicit false

namespace PureDegree

variable {T : Type*} [CommRing T] {M : ℕ → Type*} [∀ p, AddCommGroup (M p)] (c : ∀ p, T →+ M p)

/-- `x` has pure degree `m`: every coefficient `c p x` with `p ≠ m` vanishes. -/
def IsPure (m : ℕ) (x : T) : Prop := ∀ p, p ≠ m → c p x = 0

/-- The product hypothesis: pure of degree `m` times pure of degree `n` is pure of degree `m + n`. -/
def MulClosed : Prop :=
  ∀ (m n : ℕ) (x y : T), IsPure c m x → IsPure c n y → IsPure c (m + n) (x * y)

variable {c}

theorem IsPure.of_eq {m n : ℕ} {x : T} (h : IsPure c m x) (e : m = n) : IsPure c n x := e ▸ h

theorem isPure_zero (c : ∀ p, T →+ M p) (m : ℕ) : IsPure c m (0 : T) := fun p _ => map_zero (c p)

theorem IsPure.add {m : ℕ} {x y : T} (hx : IsPure c m x) (hy : IsPure c m y) : IsPure c m (x + y) :=
  fun p hp => by rw [map_add, hx p hp, hy p hp, add_zero]

theorem isPure_pow (hmul : MulClosed c) (hone : IsPure c 0 (1 : T)) {d : ℕ} {x : T} (hx : IsPure c d x)
    (n : ℕ) : IsPure c (n * d) (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, Nat.zero_mul]; exact hone
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact hmul _ _ _ _ ih hx

theorem isPure_prod (hmul : MulClosed c) (hone : IsPure c 0 (1 : T)) {ι : Type*} (s : Finset ι)
    (x : ι → T) (deg : ι → ℕ) (h : ∀ i ∈ s, IsPure c (deg i) (x i)) :
    IsPure c (∑ i ∈ s, deg i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact hone
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Evaluation of weighted-homogeneous polynomials: if `Ψ` sends constants to pure degree `0` and `X i` to
pure degree `w i`, then it sends `w`-homogeneous polynomials of weight `m` to pure degree `m`. -/
theorem isPure_eval_of_isWeightedHomogeneous (hmul : MulClosed c) {R σ : Type*} [CommRing R]
    (Ψ : MvPolynomial σ R →+* T) (w : σ → ℕ) (hC : ∀ a : R, IsPure c 0 (Ψ (MvPolynomial.C a)))
    (hX : ∀ i : σ, IsPure c (w i) (Ψ (MvPolynomial.X i))) {m : ℕ} {f : MvPolynomial σ R}
    (hf : f.IsWeightedHomogeneous w m) : IsPure c m (Ψ f) := by
  have hone : IsPure c 0 (1 : T) := by
    have h := hC 1
    rwa [MvPolynomial.C_1, map_one] at h
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isPure_zero c m
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d a hd =>
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    have hprod : IsPure c (∑ i ∈ d.support, d i * w i) (∏ i ∈ d.support, Ψ (MvPolynomial.X i ^ d i)) :=
      isPure_prod hmul hone d.support _ (fun i => d i * w i) fun i _ => by
        rw [map_pow]; exact isPure_pow hmul hone (hX i) (d i)
    refine (hmul _ _ _ _ (hC a) hprod).of_eq ?_
    rw [Nat.zero_add, ← hd, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => (smul_eq_mul _ _).symm

end PureDegree
