import MiyaokaMori.Prelude
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Relative dimension of a standard smooth algebra is bounded by its Krull dimension

A nonzero standard smooth algebra of relative dimension `n` over a field with Krull dimension `≤ 1`
has `n ≤ 1`. This is used because a smooth projective curve is defined as "smooth structure
morphism + topological dimension `1`" rather than via `SmoothOfRelativeDimension 1`; to know,
**without assuming integrality**, that every standard smooth chart has relative dimension `≤ 1`,
this excludes `n ≥ 2`.

Proof: for `n = m + 2`, `K[X_0..X_{m+1}] ≃ B[X]` with `B = K[X_0..X_m]` a Noetherian Jacobson
domain which is not a field. Take a maximal ideal `Q` of `S`; `𝔪 = Q ∩ B[X]` is maximal
(Jacobson + finite type), `𝔭 = 𝔪 ∩ B` is maximal and nonzero, and `ht 𝔪 = ht 𝔭 + 1 ≥ 2` (Mathlib
`Polynomial.height_eq_height_add_one`); étale ⇒ flat ⇒ going-down ⇒ `ht Q ≥ ht 𝔪`.

References: Stacks 00ON (height formula under going-down), Stacks 00OP.
-/

set_option autoImplicit false

universe u v

open Polynomial

/-- Over a Noetherian Jacobson domain `B` which is not a field, a nonzero étale algebra over `B[X]` has
Krull dimension at least `2`. -/
theorem Algebra.Etale.two_le_ringKrullDim_of_polynomial
    (B : Type u) (S : Type v) [CommRing B] [CommRing S] [IsDomain B] [IsNoetherianRing B]
    [IsJacobsonRing B] (hB : ¬ IsField B) [Nontrivial S] [Algebra B[X] S] [Algebra.Etale B[X] S] :
    2 ≤ ringKrullDim S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing B[X] S
  have : Module.Flat B[X] S := Algebra.Smooth.flat B[X] S
  have : Algebra.HasGoingDown B[X] S := Algebra.HasGoingDown.of_flat
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal S
  have : Q.IsMaximal := hQ
  let _ : Field (S ⧸ Q) := Ideal.Quotient.field Q
  have : Algebra.FiniteType B[X] (S ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B[X] Q)
      (Ideal.Quotient.mkₐ_surjective B[X] Q)
  have : Module.Finite B[X] (S ⧸ Q) := finite_of_finite_type_of_isJacobsonRing B[X] (S ⧸ Q)
  have : Algebra.IsIntegral B[X] (S ⧸ Q) := Algebra.IsIntegral.of_finite B[X] (S ⧸ Q)
  have hcomap : (⊥ : Ideal (S ⧸ Q)).under B[X] = Q.under B[X] := by
    ext a
    change Ideal.Quotient.mk Q (algebraMap B[X] S a) = 0 ↔ algebraMap B[X] S a ∈ Q
    exact Ideal.Quotient.eq_zero_iff_mem
  have hmmax : (Q.under B[X]).IsMaximal := by
    rw [← hcomap]
    exact Ideal.IsMaximal.under B[X] (⊥ : Ideal (S ⧸ Q))
  have : Q.LiesOver (Q.under B[X]) := ⟨rfl⟩
  set m : Ideal B[X] := Q.under B[X] with hm
  have hpmax : (m.comap (C : B →+* B[X])).IsMaximal :=
    Polynomial.isMaximal_comap_C_of_isJacobsonRing m
  set p : Ideal B := m.comap (C : B →+* B[X]) with hp
  have : m.LiesOver p := ⟨rfl⟩
  have hpbot : (⊥ : Ideal B) < p := Ideal.bot_lt_of_maximal p hB
  have hp1 : 1 ≤ p.height := by
    have h := Ideal.height_strict_mono_of_isPrime hpbot
    exact Order.one_le_iff_pos.mpr (lt_of_le_of_lt bot_le h)
  have hm2 : 2 ≤ m.height := by
    rw [Polynomial.height_eq_height_add_one p m]
    calc (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ p.height + 1 := by gcongr
  have hQ2 : 2 ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m Q]
    exact hm2.trans le_self_add
  calc (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ (Q.height : WithBot ℕ∞) := by exact_mod_cast hQ2
    _ ≤ ringKrullDim S := Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- A nonzero standard smooth algebra of relative dimension `n` over a field with Krull dimension `≤ 1`
has `n ≤ 1`. -/
theorem RingHom.IsStandardSmoothOfRelativeDimension.le_one_of_ringKrullDim_le_one
    {K S : Type u} [Field K] [CommRing S] [Nontrivial S] {n : ℕ}
    {f : K →+* S} (hf : f.IsStandardSmoothOfRelativeDimension n)
    (hS : ringKrullDim S ≤ 1) : n ≤ 1 := by
  by_contra hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨g, -, hg⟩ := hf.exists_etale_mvPolynomial
  let e := MvPolynomial.finSuccEquiv K (m + 1)
  let g' : (MvPolynomial (Fin (m + 1)) K)[X] →+* S := g.comp e.symm.toRingEquiv.toRingHom
  have hg' : g'.Etale :=
    RingHom.Etale.stableUnderComposition (e.symm.toRingEquiv.toRingHom) g
      (RingHom.Etale.of_bijective e.symm.toRingEquiv.bijective) hg
  let _ : Algebra (MvPolynomial (Fin (m + 1)) K)[X] S := g'.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin (m + 1)) K)[X] S := hg'.toAlgebra
  have hB : ¬ IsField (MvPolynomial (Fin (m + 1)) K) := by
    intro h
    have h0 := ringKrullDim_eq_zero_of_isField h
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h0
    simp at h0
    exact absurd h0 (by exact_mod_cast Nat.succ_ne_zero m)
  have h2 := Algebra.Etale.two_le_ringKrullDim_of_polynomial (MvPolynomial (Fin (m + 1)) K) S hB
  exact absurd (h2.trans hS) (by decide)
