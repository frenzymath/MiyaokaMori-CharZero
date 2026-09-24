import MiyaokaMori.Prelude

/-! # Weight decomposition for a `𝔾_m`-action: the algebraic core

The **purely algebraic part** of the relative, non-negative version of Stacks 0EKK ("`A` is generated
by `Σ A_n`"), stated with hypotheses "on generators", so that on the geometric side one only has to
compute ring homomorphisms on generators (the image of `pr₂^♯` and `λ`). Write
`L := k[λ^{±1}] = LaurentPolynomial k` and let `R` be a `k`-algebra.

* `laurentCoeff`: coefficient extraction `Θ : L ⊗[k] R ≃ₗ[k] (ℤ →₀ R)`, `Θ(T n ⊗ a) = single n a`;
  `sum_laurentCoeff`: `z = Σ_n T n ⊗ (Θ z)_n`.
* `laurentTensor_ringHom_ext` / `polyTensor_ringHom_ext`: a ring homomorphism out of `L ⊗[k] R`
  (resp. `k[X] ⊗[k] R`) is determined by its values on `1 ⊗ a` and `T 1 ⊗ 1` (resp. `X ⊗ 1`).
* `counit_sum`: if `s'(1 ⊗ a) = a` and `s'(T 1 ⊗ 1) = 1`, then `s'(z) = Σ_n (Θ z)_n`.
* `laurentCoeff_map_toLaurent_of_neg`: the image of `k[X] ⊗ R` under `toLaurent ⊗ id` has no
  negative-degree coefficients.
* `coaction_coeff_eigen`: coassociativity `(Δ ⊗ id)∘co = (id ⊗ co)∘co` implies
  `co((Θ(co a))_n) = T n ⊗ (Θ(co a))_n`.
* `exists_weight_decomposition_of_charts`: the **main theorem** (assembly).

Reference: Stacks 0EKK (the argument relativized over `R` verbatim); Mathlib's
`LaurentPolynomial.instHopfAlgebra` (`comul_T`, `counit_T`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open scoped TensorProduct
open LaurentPolynomial

noncomputable section

namespace WeightDecomposition

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

/-! ## Coefficient extraction -/

/-- `Θ : k[λ^{±1}] ⊗[k] R ≃ₗ[k] (ℤ →₀ R)`, `T n ⊗ a ↦ single n a` (via the coordinates of
`AddMonoidAlgebra.basis` and `TensorProduct.finsuppScalarLeft`). -/
def laurentCoeff (k R : Type u) [Field k] [CommRing R] [Algebra k R] :
    LaurentPolynomial k ⊗[k] R ≃ₗ[k] (ℤ →₀ R) :=
  (TensorProduct.congr (AddMonoidAlgebra.basis ℤ k).repr (LinearEquiv.refl k R)).trans
    (TensorProduct.finsuppScalarLeft k R ℤ)

theorem laurentCoeff_tmul (n : ℤ) (a : R) :
    laurentCoeff k R (T n ⊗ₜ[k] a) = Finsupp.single n a := by
  have hT : (T n : LaurentPolynomial k) = AddMonoidAlgebra.basis ℤ k n := by
    rw [AddMonoidAlgebra.basis_apply]; rfl
  simp only [laurentCoeff, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, hT, Module.Basis.repr_self,
    TensorProduct.finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index, one_smul,
    Finsupp.single_zero, zero_smul]

theorem laurentCoeff_symm_single (n : ℤ) (a : R) :
    (laurentCoeff k R).symm (Finsupp.single n a) = T n ⊗ₜ[k] a := by
  rw [LinearEquiv.symm_apply_eq, laurentCoeff_tmul]

theorem sum_laurentCoeff (z : LaurentPolynomial k ⊗[k] R) :
    ((laurentCoeff k R z).sum fun n a => (T n : LaurentPolynomial k) ⊗ₜ[k] a) = z := by
  conv_rhs => rw [← (laurentCoeff k R).symm_apply_apply z]
  conv_rhs => rw [← Finsupp.sum_single (laurentCoeff k R z), map_finsuppSum]
  exact Finsupp.sum_congr fun n _ => (laurentCoeff_symm_single n _).symm

/-- For `c : ℤ →₀ R` and `F` with `F m 0 = 0`, `(Σ_m single m (F m (c m))) n = F n (c n)`. -/
theorem sum_single_apply {M : Type v} [AddCommMonoid M] (c : ℤ →₀ R) (F : ℤ → R → M)
    (hF : ∀ m, F m 0 = 0) (n : ℤ) :
    (c.sum fun m r => Finsupp.single m (F m r)) n = F n (c n) := by
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single n]
  · rw [Finsupp.single_eq_same]
  · intro m _ hmn; rw [Finsupp.single_eq_of_ne hmn.symm]
  · intro _; rw [hF, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

/-! ## Extensionality on generators -/

/-- `(C c * T n) ⊗ a = T n ⊗ (c • a)`. -/
theorem C_mul_T_tmul (c : k) (n : ℤ) (a : R) :
    ((C c * T n : LaurentPolynomial k) ⊗ₜ[k] a) = (T n : LaurentPolynomial k) ⊗ₜ[k] (c • a) := by
  rw [C_eq_algebraMap, ← Algebra.smul_def, TensorProduct.smul_tmul]

/-- `T n ⊗ a = (T n ⊗ 1) * (1 ⊗ a)`. -/
theorem T_tmul_eq_mul (n : ℤ) (a : R) :
    ((T n : LaurentPolynomial k) ⊗ₜ[k] a) =
      ((T n : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) * ((1 : LaurentPolynomial k) ⊗ₜ[k] a) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- In a commutative ring, `x u = 1 = y u` implies `x = y`. -/
theorem eq_of_mul_eq_one_of_mul_eq_one {C : Type v} [CommRing C] {x y u : C}
    (hx : x * u = 1) (hy : y * u = 1) : x = y := by
  calc x = x * (y * u) := by rw [hy, mul_one]
    _ = y * (x * u) := by ring
    _ = y := by rw [hx, mul_one]

/-- A ring homomorphism out of `k[λ^{±1}] ⊗[k] R` is determined by its values on `1 ⊗ a` (`a ∈ R`)
and `T 1 ⊗ 1`. -/
theorem laurentTensor_ringHom_ext {C : Type v} [CommRing C]
    {f g : LaurentPolynomial k ⊗[k] R →+* C}
    (h1 : ∀ a : R, f ((1 : LaurentPolynomial k) ⊗ₜ[k] a) = g ((1 : LaurentPolynomial k) ⊗ₜ[k] a))
    (hT : f ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) =
      g ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R))) : f = g := by
  -- agreement on T(-1) ⊗ 1: both sides are the inverse of the image of T 1 ⊗ 1
  have hunit : ((T (-1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) *
      ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← T_add, mul_one]; norm_num [T_zero]
    rfl
  have hTneg : f ((T (-1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) =
      g ((T (-1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) := by
    refine eq_of_mul_eq_one_of_mul_eq_one (u := g ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R))) ?_ ?_
    · rw [← hT, ← map_mul, hunit, map_one]
    · rw [← map_mul, hunit, map_one]
  -- all T n ⊗ 1
  have hTn : ∀ n : ℤ, f ((T n : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) =
      g ((T n : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) := by
    intro n
    induction n using Int.induction_on with
    | zero => rw [T_zero]; exact h1 1
    | succ n ih =>
      have : ((T ((n : ℤ) + 1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) =
          ((T (n : ℤ) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) *
            ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← T_add, mul_one]
      rw [this, map_mul, map_mul, ih, hT]
    | pred n ih =>
      have : ((T (-(n : ℤ) - 1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) =
          ((T (-(n : ℤ)) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) *
            ((T (-1) : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← T_add, mul_one, sub_eq_add_neg]
      rw [this, map_mul, map_mul, ih, hTneg]
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul p a =>
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [TensorProduct.add_tmul, map_add, map_add, hp, hq]
    | C_mul_T n c =>
      rw [C_mul_T_tmul, T_tmul_eq_mul, map_mul, map_mul, hTn, h1]

/-- A ring homomorphism out of `k[X] ⊗[k] R` is determined by its values on `1 ⊗ a` and `X ⊗ 1`. -/
theorem polyTensor_ringHom_ext {C : Type v} [CommRing C]
    {f g : Polynomial k ⊗[k] R →+* C}
    (h1 : ∀ a : R, f ((1 : Polynomial k) ⊗ₜ[k] a) = g ((1 : Polynomial k) ⊗ₜ[k] a))
    (hX : f ((Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : R)) =
      g ((Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : R))) : f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul p a =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [TensorProduct.add_tmul, map_add, map_add, hp, hq]
    | monomial n c =>
      have : ((Polynomial.monomial n c : Polynomial k) ⊗ₜ[k] a) =
          ((Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : R)) ^ n *
            ((1 : Polynomial k) ⊗ₜ[k] (c • a)) := by
        rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_eq_algebraMap,
          ← Algebra.smul_def, TensorProduct.smul_tmul]
      rw [this, map_mul, map_mul, map_pow, map_pow, hX, h1]

/-! ## Counit, non-negativity, coassociativity -/

/-- The counit map `ε ⊗ id : L ⊗[k] R → R`, `T n ⊗ a ↦ a`. -/
def counitHom (k R : Type u) [Field k] [CommRing R] [Algebra k R] :
    LaurentPolynomial k ⊗[k] R →ₐ[k] R :=
  (Algebra.TensorProduct.lid k R).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k (LaurentPolynomial k)) (AlgHom.id k R))

theorem counitHom_tmul_T (n : ℤ) (a : R) : counitHom k R ((T n : LaurentPolynomial k) ⊗ₜ[k] a) = a := by
  simp only [counitHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Bialgebra.counitAlgHom_apply, LaurentPolynomial.counit_T]
  exact (Algebra.TensorProduct.lid_tmul (1 : k) a).trans (one_smul k a)

/-- Counit formula: if `s'(1 ⊗ a) = a` and `s'(T 1 ⊗ 1) = 1`, then `s'(z) = Σ_n (Θ z)_n`. -/
theorem counit_sum (s' : LaurentPolynomial k ⊗[k] R →+* R)
    (h1 : ∀ a : R, s' ((1 : LaurentPolynomial k) ⊗ₜ[k] a) = a)
    (hT : s' ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) = 1)
    (z : LaurentPolynomial k ⊗[k] R) :
    s' z = (laurentCoeff k R z).sum fun _ a => a := by
  have hs : s' = (counitHom k R).toRingHom := by
    refine laurentTensor_ringHom_ext (fun a => ?_) ?_
    · rw [h1]; exact (by rw [← T_zero]; exact (counitHom_tmul_T 0 a).symm)
    · rw [hT]; exact (counitHom_tmul_T 1 1).symm
  rw [hs, ← sum_laurentCoeff z, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_finsuppSum]
  rw [sum_laurentCoeff]
  exact Finsupp.sum_congr fun n _ => counitHom_tmul_T n _

/-- Non-negativity: the image of `k[X] ⊗ R` under `toLaurent ⊗ id` has no negative-degree coefficients. -/
theorem laurentCoeff_map_toLaurent_of_neg (w : Polynomial k ⊗[k] R) (n : ℤ) (hn : n < 0) :
    laurentCoeff k R (Algebra.TensorProduct.map Polynomial.toLaurentAlg (AlgHom.id k R) w) n = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul p a =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [TensorProduct.add_tmul, map_add, map_add, Finsupp.add_apply, hp, hq, add_zero]
    | monomial m c =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Polynomial.toLaurentAlg_apply,
        Polynomial.toLaurent_C_mul_T, C_mul_T_tmul, laurentCoeff_tmul, Finsupp.single_eq_of_ne]
      intro h
      have : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      omega

/-- `(Δ ⊗ id)` followed by reassociation: `L ⊗[k] R → L ⊗[k] (L ⊗[k] R)`, `T n ⊗ a ↦ T n ⊗ (T n ⊗ a)`. -/
def comulLeft (k R : Type u) [Field k] [CommRing R] [Algebra k R] :
    LaurentPolynomial k ⊗[k] R →ₐ[k] LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R) :=
  (Algebra.TensorProduct.assoc k k k (LaurentPolynomial k) (LaurentPolynomial k) R).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k (LaurentPolynomial k)) (AlgHom.id k R))

theorem comulLeft_tmul_T (n : ℤ) (a : R) :
    comulLeft k R ((T n : LaurentPolynomial k) ⊗ₜ[k] a) =
      (T n : LaurentPolynomial k) ⊗ₜ[k] ((T n : LaurentPolynomial k) ⊗ₜ[k] a) := by
  simp only [comulLeft, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Bialgebra.comulAlgHom_apply, LaurentPolynomial.comul_T]
  change (Algebra.TensorProduct.assoc k k k (LaurentPolynomial k) (LaurentPolynomial k) R)
    (((T n : LaurentPolynomial k) ⊗ₜ[k] (T n : LaurentPolynomial k)) ⊗ₜ[k] a) = _
  rw [Algebra.TensorProduct.assoc_tmul]

/-- Coassociativity makes the coefficients eigenvectors: if `(Δ ⊗ id)(co a) = (id ⊗ co)(co a)`, then
for every `n`, `co((Θ(co a))_n) = T n ⊗ (Θ(co a))_n`. -/
theorem coaction_coeff_eigen (co : R →ₐ[k] LaurentPolynomial k ⊗[k] R) (a : R)
    (h : comulLeft k R (co a) = Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) co (co a))
    (n : ℤ) :
    co (laurentCoeff k R (co a) n) = (T n : LaurentPolynomial k) ⊗ₜ[k] laurentCoeff k R (co a) n := by
  set c := laurentCoeff k R (co a) with hc
  have hL : comulLeft k R (co a) =
      c.sum fun m r => (T m : LaurentPolynomial k) ⊗ₜ[k] ((T m : LaurentPolynomial k) ⊗ₜ[k] r) := by
    conv_lhs => rw [← sum_laurentCoeff (co a), map_finsuppSum]
    exact Finsupp.sum_congr fun m _ => comulLeft_tmul_T m _
  have hR : Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) co (co a) =
      c.sum fun m r => (T m : LaurentPolynomial k) ⊗ₜ[k] co r := by
    conv_lhs => rw [← sum_laurentCoeff (co a), map_finsuppSum]
    exact Finsupp.sum_congr fun m _ => by rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have h2 := congrArg (fun z => laurentCoeff k (LaurentPolynomial k ⊗[k] R) z n) h
  simp only [hL, hR, map_finsuppSum, laurentCoeff_tmul] at h2
  rw [sum_single_apply c (fun m r => (T m : LaurentPolynomial k) ⊗ₜ[k] r) (fun m => TensorProduct.tmul_zero _ _),
    sum_single_apply c (fun _ r => co r) (fun _ => map_zero co)] at h2
  exact h2.symm

/-! ## Main theorem (assembly) -/

/-- **Main theorem (purely algebraic).** Let `R` be a `k`-algebra and `B`, `B₂`, `B'` commutative rings with
* a chart `e : B ≃+* L ⊗[k] R`, `e(φ a) = 1 ⊗ a`, `e(lam) = T 1 ⊗ 1` (geometrically `B = Γ(G_m ×_k V)`,
  `φ = pr₂^♯`, `lam = λ`);
* `act^♯ =: actS : R →+* B`, agreeing with `φ` on `k` (`k`-linearity);
* a counit `s : B →+* R` with `s∘φ = id`, `s(lam) = 1`, `s∘actS = id` (geometrically `σ^♯` for the unit
  section `σ = (e, 𝟙)`; the axiom `one_act`);
* a coassociativity chart: `B₂` with `ψ : B →+* B₂`, `lam₁ ∈ B₂`, `e₂ : B₂ ≃+* L ⊗[k] B` (for any
  `Algebra k B` compatible with `φ`), and `m, a₂ : B →+* B₂` with `m∘φ = ψ∘φ`, `m(lam) = lam₁·ψ(lam)`,
  `a₂∘φ = ψ∘actS`, `a₂(lam) = lam₁`, and coassociativity `m∘actS = a₂∘actS` (geometrically
  `B₂ = Γ(G_m ×_k G_m ×_k V)`, `m = (μ × 1)^♯`, `a₂ = (1 × act)^♯`; the axiom `mul_act`);
* non-negativity: `B'` with `φ', actS' : R →+* B'`, `lam' ∈ B'`, `e' : B' ≃+* k[X] ⊗[k] R`
  (`e'(φ' a) = 1 ⊗ a`, `e'(lam') = X ⊗ 1`) and `ι : B' →+* B` with `ι∘φ' = φ`, `ι(lam') = lam`,
  `ι∘actS' = actS` (geometrically `B' = Γ(A¹ ×_k V)`; `IsNonnegative`).
Then every `a ∈ R` is a finite sum of eigenvectors: `∃ y : ℕ →₀ R`, `actS(y_n) = lam^n · φ(y_n)`,
`Σ y_n = a`.

Proof (Stacks 0EKK): put `co := e ∘ actS` and `c := Θ(co a)`. The counit gives `Σ_n c_n = a`
(`counit_sum`); non-negativity gives `c_n = 0` for `n < 0` (`laurentCoeff_map_toLaurent_of_neg`);
coassociativity gives `co(c_n) = T n ⊗ c_n` (`coaction_coeff_eigen`), i.e. `actS(c_n) = lam^n φ(c_n)`.
Take `y := c` pulled back along `ℕ ↪ ℤ` (`Finsupp.comapDomain`). -/
theorem exists_weight_decomposition_of_charts
    {B B₂ B' : Type u} [CommRing B] [CommRing B₂] [CommRing B'] [Algebra k B]
    (φ actS : R →+* B) (lam : B)
    (e : B ≃+* LaurentPolynomial k ⊗[k] R)
    (he_φ : ∀ a, e (φ a) = (1 : LaurentPolynomial k) ⊗ₜ[k] a)
    (he_lam : e lam = (T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R))
    (hφk : ∀ c : k, φ (algebraMap k R c) = algebraMap k B c)
    (hact_k : ∀ c : k, actS (algebraMap k R c) = φ (algebraMap k R c))
    -- counit
    (s : B →+* R) (hsφ : ∀ a, s (φ a) = a) (hs_lam : s lam = 1) (hs_act : ∀ a, s (actS a) = a)
    -- coassociativity
    (ψ m a₂ : B →+* B₂) (lam₁ : B₂) (e₂ : B₂ ≃+* LaurentPolynomial k ⊗[k] B)
    (he₂_ψ : ∀ b, e₂ (ψ b) = (1 : LaurentPolynomial k) ⊗ₜ[k] b)
    (he₂_lam₁ : e₂ lam₁ = (T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : B))
    (hmφ : ∀ a, m (φ a) = ψ (φ a)) (hm_lam : m lam = lam₁ * ψ lam)
    (ha₂φ : ∀ a, a₂ (φ a) = ψ (actS a)) (ha₂_lam : a₂ lam = lam₁)
    (hcoassoc : ∀ a, m (actS a) = a₂ (actS a))
    -- non-negativity
    (φ' actS' : R →+* B') (lam' : B') (e' : B' ≃+* Polynomial k ⊗[k] R)
    (he'_φ : ∀ a, e' (φ' a) = (1 : Polynomial k) ⊗ₜ[k] a)
    (he'_lam : e' lam' = (Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : R))
    (ι : B' →+* B) (hιφ : ∀ a, ι (φ' a) = φ a) (hι_lam : ι lam' = lam)
    (hι_act : ∀ a, ι (actS' a) = actS a)
    (a : R) :
    ∃ y : ℕ →₀ R, (∀ n, actS (y n) = lam ^ n * φ (y n)) ∧ y.sum (fun _ b => b) = a := by
  -- e and actS as k-algebra homomorphisms
  have he_alg : ∀ c : k, e (algebraMap k B c) = algebraMap k (LaurentPolynomial k ⊗[k] R) c := by
    intro c
    rw [← hφk, he_φ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let eA : B ≃ₐ[k] LaurentPolynomial k ⊗[k] R := AlgEquiv.ofRingEquiv he_alg
  let actA : R →ₐ[k] B := { actS with commutes' := fun c => by simp only [RingHom.toMonoidHom_eq_coe,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]; rw [hact_k, hφk] }
  let co : R →ₐ[k] LaurentPolynomial k ⊗[k] R := eA.toAlgHom.comp actA
  have hco : ∀ b, co b = e (actS b) := fun b => rfl
  have heA : ∀ b, eA b = e b := fun b => rfl
  -- values of e⁻¹ on generators
  have hsymm_φ : ∀ b : R, e.symm ((1 : LaurentPolynomial k) ⊗ₜ[k] b) = φ b := by
    intro b; rw [RingEquiv.symm_apply_eq, he_φ]
  have hsymm_lam : e.symm ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) = lam := by
    rw [RingEquiv.symm_apply_eq, he_lam]
  have hsymm'_φ : ∀ b : R, e'.symm ((1 : Polynomial k) ⊗ₜ[k] b) = φ' b := by
    intro b; rw [RingEquiv.symm_apply_eq, he'_φ]
  have hsymm'_lam : e'.symm ((Polynomial.X : Polynomial k) ⊗ₜ[k] (1 : R)) = lam' := by
    rw [RingEquiv.symm_apply_eq, he'_lam]
  set c := laurentCoeff k R (co a) with hc
  -- (1) counit ⇒ Σ c_n = a
  have hsum : (c.sum fun _ b => b) = a := by
    have h1 : ∀ b : R, (s.comp e.symm.toRingHom) ((1 : LaurentPolynomial k) ⊗ₜ[k] b) = b := by
      intro b
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hsymm_φ, hsφ]
    have hT : (s.comp e.symm.toRingHom) ((T 1 : LaurentPolynomial k) ⊗ₜ[k] (1 : R)) = 1 := by
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hsymm_lam, hs_lam]
    have := counit_sum (s.comp e.symm.toRingHom) h1 hT (co a)
    rw [hco, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, hs_act] at this
    exact this.symm
  -- (2) non-negativity ⇒ c_n = 0 for n < 0
  have hneg : ∀ n : ℤ, n < 0 → c n = 0 := by
    intro n hn
    have hΨ : e.toRingHom.comp (ι.comp e'.symm.toRingHom) =
        (Algebra.TensorProduct.map Polynomial.toLaurentAlg (AlgHom.id k R)).toRingHom := by
      refine polyTensor_ringHom_ext (k := k) (R := R) (C := LaurentPolynomial k ⊗[k] R)
        (f := e.toRingHom.comp (ι.comp e'.symm.toRingHom))
        (g := (Algebra.TensorProduct.map Polynomial.toLaurentAlg (AlgHom.id k R)).toRingHom)
        (fun b => ?_) ?_
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
        rw [hsymm'_φ, hιφ, he_φ]
      · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
        rw [hsymm'_lam, hι_lam, he_lam]
    have hlift : co a = Algebra.TensorProduct.map Polynomial.toLaurentAlg (AlgHom.id k R)
        (e' (actS' a)) := by
      have := congrArg (fun F : Polynomial k ⊗[k] R →+* LaurentPolynomial k ⊗[k] R => F (e' (actS' a))) hΨ
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.symm_apply_apply, AlgHom.toRingHom_eq_coe] at this
      rw [hco, ← hι_act]; exact this
    rw [hc, hlift]
    exact laurentCoeff_map_toLaurent_of_neg _ n hn
  -- (3) coassociativity ⇒ co(c_n) = T n ⊗ c_n
  have heigen : ∀ n : ℤ, co (c n) = (T n : LaurentPolynomial k) ⊗ₜ[k] c n := by
    have hcoassoc' : comulLeft k R (co a) =
        Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) co (co a) := by
      -- both sides are the value of (id ⊗ e) ∘ e₂ ∘ (m resp. a₂) ∘ e⁻¹ at co a
      let G : LaurentPolynomial k ⊗[k] B →+* LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R) :=
        (Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) eA.toAlgHom).toRingHom
      have hG : ∀ (x : LaurentPolynomial k) (b : B), G (x ⊗ₜ[k] b) = x ⊗ₜ[k] e b := by
        intro x b
        show Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) eA.toAlgHom (x ⊗ₜ[k] b) = _
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]; rfl
      let Fm : LaurentPolynomial k ⊗[k] R →+* LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R) :=
        G.comp (e₂.toRingHom.comp (m.comp e.symm.toRingHom))
      let Fa : LaurentPolynomial k ⊗[k] R →+* LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R) :=
        G.comp (e₂.toRingHom.comp (a₂.comp e.symm.toRingHom))
      have hFm_apply : ∀ z, Fm z = G (e₂ (m (e.symm z))) := fun z => rfl
      have hFa_apply : ∀ z, Fa z = G (e₂ (a₂ (e.symm z))) := fun z => rfl
      have hFm : Fm = (comulLeft k R).toRingHom := by
        refine laurentTensor_ringHom_ext (k := k) (R := R)
          (C := LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R)) (f := Fm) (g := (comulLeft k R).toRingHom)
          (fun b => ?_) ?_
        · rw [hFm_apply, hsymm_φ, hmφ, he₂_ψ, hG, he_φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
          have := comulLeft_tmul_T (k := k) 0 b
          rw [T_zero] at this
          exact this.symm
        · rw [hFm_apply, hsymm_lam, hm_lam, map_mul, he₂_lam₁, he₂_ψ,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hG, he_lam,
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comulLeft_tmul_T]
      have hFa : Fa = (Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) co).toRingHom := by
        refine laurentTensor_ringHom_ext (k := k) (R := R)
          (C := LaurentPolynomial k ⊗[k] (LaurentPolynomial k ⊗[k] R)) (f := Fa)
          (g := (Algebra.TensorProduct.map (AlgHom.id k (LaurentPolynomial k)) co).toRingHom)
          (fun b => ?_) ?_
        · rw [hFa_apply, hsymm_φ, ha₂φ, he₂_ψ, hG, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hco]
        · rw [hFa_apply, hsymm_lam, ha₂_lam, he₂_lam₁, hG, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, map_one]
      have h1 : Fm (co a) = Fa (co a) := by
        rw [hFm_apply, hFa_apply, hco, RingEquiv.symm_apply_apply, hcoassoc]
      rw [hFm, hFa] at h1
      exact h1
    exact coaction_coeff_eigen co a hcoassoc'
  -- (4) assembly: y := c pulled back along ℕ → ℤ
  have hbij : Set.BijOn (fun n : ℕ => (n : ℤ)) ((fun n : ℕ => (n : ℤ)) ⁻¹' ↑c.support) ↑c.support := by
    refine ⟨fun n hn => hn, fun n₁ _ n₂ _ h => Nat.cast_injective h, fun n hn => ?_⟩
    have hn0 : 0 ≤ n := by
      by_contra hlt
      exact (Finsupp.mem_support_iff.mp hn) (hneg n (not_le.mp hlt))
    exact ⟨n.toNat, by simpa [Int.toNat_of_nonneg hn0] using hn, Int.toNat_of_nonneg hn0⟩
  refine ⟨Finsupp.comapDomain (fun n : ℕ => (n : ℤ)) c hbij.injOn, fun n => ?_, ?_⟩
  · rw [Finsupp.comapDomain_apply]
    apply e.injective
    rw [← hco, heigen, map_mul, map_pow, he_lam, he_φ, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, T_pow, mul_one]
  · rw [← hsum]
    exact Finsupp.sum_comapDomain (fun n : ℕ => (n : ℤ)) c (fun _ b => b) hbij

end WeightDecomposition

end
