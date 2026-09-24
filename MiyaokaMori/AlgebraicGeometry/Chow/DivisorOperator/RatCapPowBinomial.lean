import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpToEnd
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator

/-! # Binomial expansion of powers of ℚ-divisor operators

Binomial expansion and homogeneity of powers of ℚ-divisor operators: if `D` and `H` commute as
operators on the Chow group, then `(D + tH)^n ∩ α = Σ_s C(n,s) t^s D^{n−s} H^s ∩ α`, and
`(c•D)^n = c^n D^n` (Lazarsfeld, Positivity in Algebraic Geometry I, p. 57, "expanding out the
right-hand side"; used for Lemma 2.5 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem rat_cap_of_congr {X : AlgebraicGeometry.Scheme.{u}} {p q : ℕ}
    (h : p = q) (α : AlgebraicGeometry.ChowGroupRat X p) :
    DirectSum.of _ p α =
      DirectSum.of _ q (AlgebraicGeometry.ChowGroupRat.congr X h α) := by
  cases h
  rfl

private theorem rat_toEnd_commute {X : AlgebraicGeometry.Scheme.{u}}
    (D H : AlgebraicGeometry.RatDivisorOp X)
    (hcomm : ∀ d, (D d).comp (H (d + 1)) = (H d).comp (D (d + 1))) :
    Commute (AlgebraicGeometry.RatDivisorOp.toEnd D)
      (AlgebraicGeometry.RatDivisorOp.toEnd H) := by
  rw [Commute]
  apply DirectSum.linearMap_ext ℚ
  intro j
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [DirectSum.lof_eq_of]
  cases j with
  | zero =>
      simp [AlgebraicGeometry.RatDivisorOp.toEnd_of_zero]
  | succ j =>
      cases j with
      | zero =>
          rw [AlgebraicGeometry.RatDivisorOp.toEnd_of]
          rw [AlgebraicGeometry.RatDivisorOp.toEnd_of_zero]
          rw [AlgebraicGeometry.RatDivisorOp.toEnd_of]
          rw [AlgebraicGeometry.RatDivisorOp.toEnd_of_zero]
      | succ j =>
          rw [AlgebraicGeometry.RatDivisorOp.toEnd_of,
            AlgebraicGeometry.RatDivisorOp.toEnd_of,
            AlgebraicGeometry.RatDivisorOp.toEnd_of,
            AlgebraicGeometry.RatDivisorOp.toEnd_of]
          congr 1
          exact LinearMap.congr_fun (hcomm j) x

private theorem rat_end_binom {M : Type u} [AddCommGroup M] [Module ℚ M]
    (A B : Module.End ℚ M) (t : ℚ) (hc : Commute A B) (n : ℕ) (v : M) :
    ((A + t • B) ^ n) v =
      ∑ s : Fin (n + 1), ((n.choose (s : ℕ) : ℚ) * t ^ (s : ℕ)) •
        ((A ^ (n - (s : ℕ)) * B ^ (s : ℕ)) v) := by
  rw [hc.smul_right t |>.add_pow]
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ => ((n.choose s : ℚ) * t ^ s) •
      ((A ^ (n - s) * B ^ s) v)) (n + 1)]
  change (Finset.sum (Finset.range (n + 1)) (fun m =>
      (A ^ m * (t • B) ^ (n - m) * (n.choose m : Module.End ℚ M))) ) v = _
  rw [LinearMap.coe_sum, Finset.sum_apply]
  rw [← Finset.sum_range_reflect
    (fun m : ℕ => ((A ^ m * (t • B) ^ (n - m) *
      (n.choose m : Module.End ℚ M)) v)) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  have hjle : j ≤ n := by omega
  have hidx : n + 1 - 1 - j = n - j := by omega
  have hsub : n - (n - j) = j := by omega
  have hchoose : n.choose (n - j) = n.choose j := Nat.choose_symm hjle
  rw [hidx, hsub, hchoose]
  simp only [smul_pow, Module.End.mul_apply, LinearMap.smul_apply]
  simp [Module.End.natCast_apply, map_smul, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℚ, mul_comm]

theorem AlgebraicGeometry.RatDivisorOp.capPow_add_smul {X : AlgebraicGeometry.Scheme.{u}}
    (D H : AlgebraicGeometry.RatDivisorOp X)
    (hcomm : ∀ d, (D d).comp (H (d + 1)) = (H d).comp (D (d + 1))) (t : ℚ) (n d : ℕ) :
    AlgebraicGeometry.RatDivisorOp.capPow (D + t • H) n d
      = ∑ s : Fin (n + 1), ((n.choose (s : ℕ) : ℚ) * t ^ (s : ℕ)) •
          ((AlgebraicGeometry.RatDivisorOp.capPow D (n - (s : ℕ)) d).comp
            ((AlgebraicGeometry.RatDivisorOp.capPow H (s : ℕ) (d + (n - (s : ℕ)))).comp
              (AlgebraicGeometry.ChowGroupRat.congr X (by have := s.isLt; omega)))) := by
  apply LinearMap.ext
  intro α
  apply DirectSum.of_injective d
  rw [AlgebraicGeometry.RatDivisorOp.capPow_eq_pow_toEnd]
  have hcomm' : Commute (AlgebraicGeometry.RatDivisorOp.toEnd D)
      (AlgebraicGeometry.RatDivisorOp.toEnd H) :=
    rat_toEnd_commute D H hcomm
  have hbin := rat_end_binom
    (AlgebraicGeometry.RatDivisorOp.toEnd D)
    (AlgebraicGeometry.RatDivisorOp.toEnd H) t hcomm'
    n (DirectSum.of _ (d + n) α)
  rw [AlgebraicGeometry.RatDivisorOp.toEnd.map_add,
    AlgebraicGeometry.RatDivisorOp.toEnd.map_smul]
  rw [hbin]
  rw [LinearMap.coe_sum]
  rw [Finset.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  let k : ℕ := (s : ℕ)
  have hklt : k < n + 1 := s.isLt
  have hidx : (d + (n - k)) + k = d + n := by omega
  have hcongr : d + n = d + (n - k) + k := by omega
  have hH := AlgebraicGeometry.RatDivisorOp.capPow_eq_pow_toEnd H k (d + (n - k))
    (AlgebraicGeometry.ChowGroupRat.congr X hcongr α)
  have hH' :
      (AlgebraicGeometry.RatDivisorOp.toEnd H ^ k)
          (DirectSum.of _ (d + n) α) =
        DirectSum.of _ (d + (n - k))
          (AlgebraicGeometry.RatDivisorOp.capPow H k (d + (n - k))
            (AlgebraicGeometry.ChowGroupRat.congr X hcongr α)) := by
    rw [rat_cap_of_congr hcongr α]
    exact hH.symm
  have hD := AlgebraicGeometry.RatDivisorOp.capPow_eq_pow_toEnd D (n - k) d
    (AlgebraicGeometry.RatDivisorOp.capPow H k (d + (n - k))
      (AlgebraicGeometry.ChowGroupRat.congr X hcongr α))
  have hcomp :
      (AlgebraicGeometry.RatDivisorOp.toEnd D ^ (n - k) *
          AlgebraicGeometry.RatDivisorOp.toEnd H ^ k)
          (DirectSum.of _ (d + n) α) =
        DirectSum.of _ d
          (AlgebraicGeometry.RatDivisorOp.capPow D (n - k) d
            (AlgebraicGeometry.RatDivisorOp.capPow H k (d + (n - k))
              (AlgebraicGeometry.ChowGroupRat.congr X hcongr α))) := by
    rw [Module.End.mul_apply, hH', ← hD]
  rw [hcomp]
  rw [← DirectSum.of_smul]
  congr 1

theorem AlgebraicGeometry.RatDivisorOp.capPow_smul {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) (c : ℚ) (n d : ℕ) :
    AlgebraicGeometry.RatDivisorOp.capPow (c • D) n d
      = c ^ n • AlgebraicGeometry.RatDivisorOp.capPow D n d := by
  induction n with
  | zero =>
      simp [AlgebraicGeometry.RatDivisorOp.capPow]
  | succ n ih =>
      simp only [AlgebraicGeometry.RatDivisorOp.capPow]
      rw [ih]
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply]
      rw [pow_succ]
      simp [smul_smul]

end
