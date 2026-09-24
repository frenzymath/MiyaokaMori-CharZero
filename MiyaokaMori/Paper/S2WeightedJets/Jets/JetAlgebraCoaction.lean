import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.TruncatedJetRingRescale
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraGrading

/-! # The coaction on the based jet algebra

The `𝔸¹`-coaction `coaction : J →+* J[λ]` on the jet algebra `J = J_r(B, ε)` induced by the parameter rescaling
`t ↦ λt`: it is the ring homomorphism obtained by the universal property (`BasedJetAlgebra.lift`) from the rescaled
universal jet `B → J[λ][t]/(t^{r+1})`.
Theorems: `coaction (D_n b) = D_n b · λ^n` (`coaction_coeffClass`); on the `m`-th piece `coaction x = x · λ^m`
(`coaction_of_mem_grading`); conversely the `λ^m`-eigenvectors of the coaction are exactly the `m`-th piece
(`mem_grading_iff_coaction`). The counit law `λ ↦ 1` gives the identity (`coaction_eval_one`).

Both the grading and the coaction are constructed at the level of rings, and their correspondence is a theorem;
the coaction lands in the polynomial ring `J[λ]` (not the Laurent ring), so nonnegativity is part of the type
rather than an existential statement.

References: §2 of the paper (parameter rescaling grades the coordinate algebra); Stacks 0EKK; Demailly [Dem11, (0.3)].

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace MiyaokaMori.Jet.TruncatedJetRing

/-- Taking coefficients commutes with a change of coefficients. -/
theorem coeff_map {S T : Type u} [CommRing S] [CommRing T] (r n : ℕ) (hn : n ≤ r) (φ : S →+* T)
    (x : TruncatedJetRing S r) :
    coeff r n hn (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r φ x) = φ (coeff r n hn x) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  show coeff r n hn (MiyaokaMori.Jet.jetProjection T r (p.map φ)) = φ (p.coeff n)
  rw [coeff_mk, Polynomial.coeff_map]


variable {J : Type u} [CommRing J] (r : ℕ)

/-- Lift the coefficients to `J[λ]` and rescale by `λ`: `J[t]/(t^{r+1}) → J[λ][t]/(t^{r+1})`,
`Σ a_n t^n ↦ Σ (a_n λ^n) t^n`. -/
def polyRescale : TruncatedJetRing J r →+* TruncatedJetRing J[X] r :=
  (rescale r (X : J[X])).comp (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (C : J →+* J[X]))

@[simp] theorem coeff_polyRescale (n : ℕ) (hn : n ≤ r) (x : TruncatedJetRing J r) :
    coeff r n hn (polyRescale r x) = C (coeff r n hn x) * X ^ n := by
  show coeff r n hn (rescale r X (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r C x)) = _
  rw [coeff_rescale, coeff_map, mul_comm]

@[simp] theorem polyRescale_eta (a : J) :
    polyRescale r (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (C a) := by
  refine ext_coeff r fun n hn => ?_
  rw [coeff_polyRescale]
  show C ((C a : J[X]).coeff n) * X ^ n = ((C (C a) : J[X][X])).coeff n
  rw [Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

@[simp] theorem epsilon_polyRescale (x : TruncatedJetRing J r) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyRescale r x) =
      C (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r x) := by
  show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
    (rescale r X (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r C x)) = _
  rw [epsilon_rescale]
  exact congrArg (fun φ : TruncatedJetRing J r →+* J[X] => φ x)
    (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_map r (C : J →+* J[X]))

/-- The constant term is the coefficient of order `0`. -/
theorem epsilon_eq_coeff_zero (x : TruncatedJetRing J r) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r x = coeff r 0 (Nat.zero_le r) x := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  show p.eval 0 = p.coeff 0
  exact (Polynomial.coeff_zero_eq_eval_zero p).symm

end MiyaokaMori.Jet.TruncatedJetRing

namespace BasedJetAlgebra

open MiyaokaMori.Jet.TruncatedJetRing

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (r : ℕ)

section Aux

variable {J : Type u} [CommRing J] [Algebra R J]
  (u : B →+* MiyaokaMori.Jet.TruncatedJetRing J r)
  (hu : ∀ (a : R) (b : B), u (a • b) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (algebraMap R J a) * u b)
  (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (u b) = algebraMap R J (ε b))

include hu in
theorem coactionAux_smul (a : R) (b : B) :
    ((polyRescale r).comp u) (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (((C : J →+* J[X]).comp (algebraMap R J)) a) *
        ((polyRescale r).comp u) b := by
  show polyRescale r (u (a • b)) = _
  rw [hu, map_mul, polyRescale_eta]
  rfl

include hε in
theorem coactionAux_epsilon (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (((polyRescale r).comp u) b) =
      ((C : J →+* J[X]).comp (algebraMap R J)) (ε b) := by
  show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyRescale r (u b)) = _
  rw [epsilon_polyRescale, hε]
  rfl

/-- General form: the map `J_r(B, ε) → J[λ]` corresponding to the rescaling of a `J`-valued based jet `u`. -/
def coactionAux : BasedJetAlgebra ε r →+* J[X] :=
  lift ε r ((C : J →+* J[X]).comp (algebraMap R J)) ((polyRescale r).comp u)
    (coactionAux_smul r u hu) (coactionAux_epsilon ε r u hε)

theorem coactionAux_coeffClass (n : ℕ) (hn : n ≤ r) (b : B) :
    coactionAux ε r u hu hε (coeffClass ε r n b) = C (coeff r n hn (u b)) * X ^ n := by
  unfold coactionAux
  rw [lift_coeffClass ε r _ _ _ _ n hn b]
  exact coeff_polyRescale r n hn (u b)

theorem coactionAux_algebraMap (a : R) :
    coactionAux ε r u hu hε (algebraMap R (BasedJetAlgebra ε r) a) = C (algebraMap R J a) := by
  show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
  rw [MvPolynomial.eval₂Hom_C]; rfl

end Aux

theorem coeff_universalJet (n : ℕ) (hn : n ≤ r) (b : B) :
    coeff r n hn (universalJet ε r b) = coeffClass ε r n b := by
  show coeff r n hn (MiyaokaMori.Jet.jetProjection _ r _) = _
  rw [coeff_mk, universalJet_poly_coeff ε r b n hn]

theorem universalJet_smul (a : R) (b : B) :
    (universalJet ε r).toRingHom (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (algebraMap R (BasedJetAlgebra ε r) a) *
        (universalJet ε r).toRingHom b := by
  show universalJet ε r (a • b) = _
  rw [map_smul]; exact Algebra.smul_def a (universalJet ε r b)

theorem universalJet_epsilon (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r ((universalJet ε r).toRingHom b) =
      algebraMap R (BasedJetAlgebra ε r) (ε b) := by
  show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (universalJet ε r b) = _
  rw [epsilon_eq_coeff_zero, coeff_universalJet, coeffClass_zero_order]
  rfl

/-- **The `𝔸¹`-coaction** (parameter rescaling `t ↦ λt`): `J → J[λ]`, given by the universal property from the
rescaled universal jet. -/
def coaction : BasedJetAlgebra ε r →+* (BasedJetAlgebra ε r)[X] :=
  coactionAux ε r (universalJet ε r).toRingHom (universalJet_smul ε r) (universalJet_epsilon ε r)

/-- **The weight convention as a theorem**: the coaction sends the coefficient `D_n b` of order `n` to `D_n b · λ^n`. -/
theorem coaction_coeffClass (n : ℕ) (hn : n ≤ r) (b : B) :
    coaction ε r (coeffClass ε r n b) = C (coeffClass ε r n b) * X ^ n := by
  unfold coaction
  rw [coactionAux_coeffClass ε r _ _ _ n hn b]
  exact congrArg (fun y => C y * X ^ n) (coeff_universalJet ε r n hn b)

theorem coaction_algebraMap (a : R) :
    coaction ε r (algebraMap R (BasedJetAlgebra ε r) a) = C (algebraMap R (BasedJetAlgebra ε r) a) :=
  coactionAux_algebraMap ε r _ _ _ a

theorem coaction_mk_X (q : Fin r) (b : B) :
    coaction ε r (Ideal.Quotient.mk (relations ε r) (MvPolynomial.X (q, b))) =
      C (Ideal.Quotient.mk (relations ε r) (MvPolynomial.X (q, b))) * X ^ (q.1 + 1) := by
  have h := coaction_coeffClass ε r (q.1 + 1) (Nat.succ_le_of_lt q.2) b
  rwa [coeffClass_succ ε r q.1 q.2 b] at h

private theorem mul_pow_pow {P : Type*} [CommRing P] (a x : P) (k n : ℕ) :
    (a * x ^ k) ^ n = a ^ n * x ^ (n * k) := by
  rw [mul_pow, ← pow_mul, mul_comm k n]

theorem coaction_mk_X_pow (i : Fin r × B) (n : ℕ) :
    coaction ε r (Ideal.Quotient.mk (relations ε r) (MvPolynomial.X i ^ n)) =
      C (Ideal.Quotient.mk (relations ε r) (MvPolynomial.X i ^ n)) * X ^ (n * weight r B i) := by
  obtain ⟨q, b⟩ := i
  rw [map_pow, map_pow, coaction_mk_X, map_pow]
  exact mul_pow_pow (P := (BasedJetAlgebra ε r)[X]) _ _ _ _

/-- On the class of a homogeneous polynomial of weight `m`, the coaction is multiplication by `λ^m`. -/
theorem coaction_mk_of_isWeightedHomogeneous {m : ℕ} {p : MvPolynomial (Fin r × B) R}
    (hp : p.IsWeightedHomogeneous (weight r B) m) :
    coaction ε r (Ideal.Quotient.mk (relations ε r) p) =
      C (Ideal.Quotient.mk (relations ε r) p) * X ^ m := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => rw [map_add, map_add, ihp, ihq, map_add, add_mul]
  | monomial d c hd =>
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, Finsupp.prod, map_prod, map_prod]
    have hC : coaction ε r (Ideal.Quotient.mk (relations ε r) (MvPolynomial.C c)) =
        C (Ideal.Quotient.mk (relations ε r) (MvPolynomial.C c)) := coaction_algebraMap ε r c
    rw [hC, Finset.prod_congr rfl fun i _ => coaction_mk_X_pow ε r i (d i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, ← map_prod C, map_mul C, mul_assoc]
    congr 2
    rw [← hd, Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul]

/-- On the `m`-th piece the coaction is multiplication by `λ^m`. -/
theorem coaction_of_mem_grading {m : ℕ} {x : BasedJetAlgebra ε r} (hx : x ∈ grading ε r m) :
    coaction ε r x = C x * X ^ m := by
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff ε r m x).mp hx
  exact coaction_mk_of_isWeightedHomogeneous ε r hp

/-- The counit law: after `λ ↦ 1` the coaction is the identity. -/
theorem coaction_eval_one (x : BasedJetAlgebra ε r) : (coaction ε r x).eval 1 = x := by
  classical
  rw [← DirectSum.sum_support_decompose (grading ε r) x, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coaction_of_mem_grading ε r (SetLike.coe_mem _)]
  simp

/-- The `λ^m`-eigenvectors of the coaction are exactly the `m`-th piece (the nonnegative version of Stacks 0EKK, at
the level of rings). -/
theorem mem_grading_iff_coaction (m : ℕ) (x : BasedJetAlgebra ε r) :
    x ∈ grading ε r m ↔ coaction ε r x = C x * X ^ m := by
  classical
  refine ⟨coaction_of_mem_grading ε r, fun h => ?_⟩
  have hsum : coaction ε r x =
      ∑ i ∈ (DirectSum.decompose (grading ε r) x).support,
        C ((DirectSum.decompose (grading ε r) x i : BasedJetAlgebra ε r)) * X ^ i := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (grading ε r) x, map_sum]
    exact Finset.sum_congr rfl fun i _ => coaction_of_mem_grading ε r (SetLike.coe_mem _)
  have hcoeff : ∀ i, i ≠ m → (DirectSum.decompose (grading ε r) x i : BasedJetAlgebra ε r) = 0 := by
    intro i hi
    have h1 := congrArg (fun p : (BasedJetAlgebra ε r)[X] => p.coeff i) (hsum.symm.trans h)
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h1
    rw [if_neg hi, mul_zero] at h1
    rw [← h1, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (Ne.symm hj), mul_zero]
    · intro hi'
      rw [if_pos rfl, mul_one]
      simpa using hi'
  rw [← DirectSum.sum_support_decompose (grading ε r) x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i = m
  · subst hi; exact SetLike.coe_mem _
  · rw [hcoeff i hi]; exact Submodule.zero_mem _

end BasedJetAlgebra

end
