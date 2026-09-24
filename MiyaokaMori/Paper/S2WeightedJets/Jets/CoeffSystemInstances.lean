import MiyaokaMori.Paper.S2WeightedJets.Jets.CoeffSystem
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraCoaction

/-! # Instances of coefficient systems

The basic instances of coefficient systems (`CoeffSystem`) and their comparison with the direct constructions:
1. `CoeffSystem.ofTruncated`: an untwisted truncated jet `ψ : B → S[t]/(t^{r+1})` (with `hψ`, `hε`) gives the
   coefficient system `c_n b =` the coefficient of order `n` of `ψ(b)`; `lift_ofTruncated`: its lift **equals**
   `BasedJetAlgebra.lift ε r ρ ψ hψ hε`.
2. `CoeffSystem.rescaling`: `c_n b = D_n b · λ^n ∈ J[λ]`; `lift_rescaling`: its lift **equals** the `𝔸¹`-coaction
   `BasedJetAlgebra.coaction`.
3. `CoeffSystem.constant`: the constant jet (`c_0 = ε`, all others `0`); it yields the augmentation `augmentation`
   of `J` and `algebraMap_injective` (`R → J` is injective; together with `grading_zero` this is `S_0 = O_C`).
Also: the totalized coefficient `TruncatedJetRing.coeffTotal` of the truncated ring (`0` for `n > r`, so that no
proof of `n ≤ r` enters the sums) with its formulas for addition, multiplication (Cauchy product) and constants.

Coefficient systems are the basic universal property; `lift`, the coaction and the twisted case
(`G = ⊕ L^{-m}`) are all instances of it, and the comparison lemmas are proved here once.

References: as for `CoeffSystem` (§2 and §3 of the paper; Vojta, "Jets via Hasse–Schmidt derivations").

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace MiyaokaMori.Jet.TruncatedJetRing

variable {S : Type u} [CommRing S] (r : ℕ)

/-- The totalized coefficient of order `n`: `0` for `n > r`. -/
def coeffTotal (n : ℕ) (x : TruncatedJetRing S r) : S :=
  if h : n ≤ r then coeff r n h x else 0

theorem coeffTotal_of_le {n : ℕ} (hn : n ≤ r) (x : TruncatedJetRing S r) :
    coeffTotal r n x = coeff r n hn x := dif_pos hn

theorem coeffTotal_mk {n : ℕ} (hn : n ≤ r) (p : S[X]) :
    coeffTotal r n (MiyaokaMori.Jet.jetProjection S r p) = p.coeff n := by
  rw [coeffTotal_of_le r hn, coeff_mk]

theorem coeffTotal_add {n : ℕ} (hn : n ≤ r) (x y : TruncatedJetRing S r) :
    coeffTotal r n (x + y) = coeffTotal r n x + coeffTotal r n y := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  obtain ⟨q, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ y
  rw [← map_add]
  show coeffTotal r n (MiyaokaMori.Jet.jetProjection S r (p + q)) =
    coeffTotal r n (MiyaokaMori.Jet.jetProjection S r p) + coeffTotal r n (MiyaokaMori.Jet.jetProjection S r q)
  rw [coeffTotal_mk r hn, coeffTotal_mk r hn, coeffTotal_mk r hn, Polynomial.coeff_add]

/-- The Cauchy product formula in the truncated ring. -/
theorem coeffTotal_mul {n : ℕ} (hn : n ≤ r) (x y : TruncatedJetRing S r) :
    coeffTotal r n (x * y) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
        coeffTotal r ij.1 x * coeffTotal r ij.2 y := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  obtain ⟨q, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ y
  rw [← map_mul]
  show coeffTotal r n (MiyaokaMori.Jet.jetProjection S r (p * q)) =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
      coeffTotal r ij.1 (MiyaokaMori.Jet.jetProjection S r p) *
        coeffTotal r ij.2 (MiyaokaMori.Jet.jetProjection S r q)
  rw [coeffTotal_mk r hn, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [coeffTotal_mk r (show ij.1 ≤ r by omega), coeffTotal_mk r (show ij.2 ≤ r by omega)]

theorem coeffTotal_eta_mul {n : ℕ} (hn : n ≤ r) (a : S) (x : TruncatedJetRing S r) :
    coeffTotal r n (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a * x) = a * coeffTotal r n x := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ x
  show coeffTotal r n (MiyaokaMori.Jet.jetProjection S r (C a * p)) =
    a * coeffTotal r n (MiyaokaMori.Jet.jetProjection S r p)
  rw [coeffTotal_mk r hn, coeffTotal_mk r hn, Polynomial.coeff_C_mul]

theorem coeffTotal_one {n : ℕ} (hn0 : 0 < n) (hn : n ≤ r) :
    coeffTotal r n (1 : TruncatedJetRing S r) = 0 := by
  show coeffTotal r n (MiyaokaMori.Jet.jetProjection S r (1 : S[X])) = 0
  rw [coeffTotal_mk r hn, Polynomial.coeff_one, if_neg (by omega)]

theorem coeffTotal_zero_eq_epsilon (x : TruncatedJetRing S r) :
    coeffTotal r 0 x = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r x := by
  rw [coeffTotal_of_le r (Nat.zero_le r), epsilon_eq_coeff_zero]

end MiyaokaMori.Jet.TruncatedJetRing

namespace BasedJetAlgebra.CoeffSystem

open MiyaokaMori.Jet.TruncatedJetRing

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (r : ℕ)

section OfTruncated

variable {S : Type u} [CommRing S] (ρ : R →+* S) (ψ : B →+* MiyaokaMori.Jet.TruncatedJetRing S r)
  (hψ : ∀ (a : R) (b : B), ψ (a • b) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (ρ a) * ψ b)
  (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (ψ b) = ρ (ε b))

/-- The coefficient system of an untwisted truncated jet: `c_n b =` the coefficient of order `n` of `ψ(b)`. -/
def ofTruncated : CoeffSystem ε r ρ where
  coeff n b := coeffTotal r n (ψ b)
  coeff_zero b := by rw [coeffTotal_zero_eq_epsilon, hε]
  coeff_add n hn b b' := by rw [map_add, coeffTotal_add r hn]
  coeff_smul n hn a b := by rw [hψ, coeffTotal_eta_mul r hn]
  coeff_one n hn0 hn := by rw [map_one, coeffTotal_one r hn0 hn]
  coeff_mul n hn b b' := by rw [map_mul, coeffTotal_mul r hn]

@[simp] theorem ofTruncated_coeff (n : ℕ) (b : B) :
    (ofTruncated ε r ρ ψ hψ hε).coeff n b = coeffTotal r n (ψ b) := rfl

/-- **Comparison**: `BasedJetAlgebra.lift` is the lift of the coefficient system `ofTruncated`. -/
theorem lift_ofTruncated :
    (ofTruncated ε r ρ ψ hψ hε).lift = BasedJetAlgebra.lift ε r ρ ψ hψ hε := by
  refine ((ofTruncated ε r ρ ψ hψ hε).lift_unique _ (fun a => ?_) fun n hn b => ?_).symm
  · show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
    rw [MvPolynomial.eval₂Hom_C]
  · rw [BasedJetAlgebra.lift_coeffClass ε r ρ ψ hψ hε n hn b, ofTruncated_coeff,
      coeffTotal_of_le r hn]

end OfTruncated

/-- The coefficient system of parameter rescaling: `c_n b = D_n b · λ^n ∈ J[λ]` (the weight convention `t ↦ λt` in
coefficient form). -/
def rescaling : CoeffSystem ε r (G := (BasedJetAlgebra ε r)[X])
    ((C : BasedJetAlgebra ε r →+* (BasedJetAlgebra ε r)[X]).comp
      (algebraMap R (BasedJetAlgebra ε r))) where
  coeff n b := C (coeffClass ε r n b) * X ^ n
  coeff_zero b := by rw [coeffClass_zero_order, pow_zero, mul_one]; rfl
  coeff_add n hn b b' := by rw [coeffClass_add ε r n hn, map_add, add_mul]
  coeff_smul n hn a b := by rw [coeffClass_smul ε r n hn, map_mul, mul_assoc]; rfl
  coeff_one n hn0 hn := by
    rw [coeffClass_one ε r n hn, if_neg (by omega), map_zero, zero_mul]
  coeff_mul n hn b b' := by
    rw [coeffClass_mul ε r n hn, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [map_mul, ← h, pow_add]
    ring

/-- **Comparison**: the `𝔸¹`-coaction is the lift of the coefficient system `rescaling`. -/
theorem lift_rescaling : (rescaling ε r).lift = BasedJetAlgebra.coaction ε r := by
  refine ((rescaling ε r).lift_unique _ (fun a => ?_) fun n hn b => ?_).symm
  · exact BasedJetAlgebra.coaction_algebraMap ε r a
  · exact BasedJetAlgebra.coaction_coeffClass ε r n hn b

/-- The coefficient system of the constant jet (the seed section itself): `c_0 = ε`, `c_n = 0` for `n ≥ 1`. It
corresponds to the augmentation `J → R`, i.e. the "zero section" `C → J_r^s` of the jet scheme. -/
def constant : CoeffSystem ε r (RingHom.id R) where
  coeff n b := if n = 0 then ε b else 0
  coeff_zero b := if_pos rfl
  coeff_add n _ b b' := by split_ifs <;> simp
  coeff_smul n _ a b := by split_ifs <;> simp
  coeff_one n hn0 _ := if_neg (by omega)
  coeff_mul n _ b b' := by
    rcases n with _ | n
    · simp
    · rw [if_neg (Nat.succ_ne_zero n)]
      refine (Finset.sum_eq_zero fun ij hij => ?_).symm
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases h1 : ij.1 = 0
      · rw [if_neg (show ij.2 ≠ 0 by omega), mul_zero]
      · rw [if_neg h1, zero_mul]

/-- The augmentation `J_r(B, ε) → R` of the jet algebra (the constant jet); a left inverse of the structure map
`R → J`. -/
def augmentation : BasedJetAlgebra ε r →+* R := (constant ε r).lift

@[simp] theorem augmentation_algebraMap (a : R) :
    augmentation ε r (algebraMap R (BasedJetAlgebra ε r) a) = a :=
  (constant ε r).lift_algebraMap a

/-- The structure map `R → J_r(B, ε)` is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (BasedJetAlgebra ε r)) :=
  Function.LeftInverse.injective (augmentation_algebraMap ε r)

end BasedJetAlgebra.CoeffSystem

end
