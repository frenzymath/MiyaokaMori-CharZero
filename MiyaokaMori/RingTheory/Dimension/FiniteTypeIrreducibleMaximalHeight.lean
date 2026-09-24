import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.Stacks00os

/-! # Maximal ideals of a finite type algebra with irreducible spectrum have height `dim A`

Let `k` be a field and `A` a finite type `k`-algebra whose nilradical `N` is prime (i.e. `Spec A`
is irreducible; `A` need not be reduced). Then every maximal ideal `𝔪` of `A` satisfies
`height 𝔪 = dim A`.

Proof:
1. `B = A/N` is a finite type `k`-domain. Every prime contains `N`, so `Spec B → Spec A`
   (`q ↦` preimage of `q`) is an order isomorphism (Mathlib
   `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`, with `V(N)` the whole space).
2. Order isomorphisms preserve Krull dimension (`Order.krullDim_eq_of_orderIso`) and heights
   (`Order.height_orderIso`): `dim B = dim A`, `height(𝔪/N) = height 𝔪`
   (`PrimeSpectrum.height_eq_orderHeight`).
3. `𝔪/N` is a maximal ideal of `B`; by Stacks 00OS (module `Stacks00os`) and
   `IsLocalization.AtPrime.ringKrullDim_eq_height`: `height(𝔪/N) = dim B_{𝔪/N} = dim B`.
4. Combining: `height 𝔪 = height(𝔪/N) = dim B = dim A`.

Reference: the reduction step "pass to the reduction" in the proof of Stacks 0A21(3), together with
Stacks 00OS.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

theorem Ideal.height_eq_ringKrullDim_of_isMaximal_of_isPrime_nilradical {k : Type u} [Field k]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hN : (nilradical A).IsPrime) (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  let N := nilradical A
  let B := A ⧸ N
  have : IsDomain B := Ideal.Quotient.isDomain N
  have : Algebra.FiniteType k B := Algebra.FiniteType.quotient k N
  have hz : PrimeSpectrum.zeroLocus (R := A) N = Set.univ :=
    Set.eq_univ_of_forall fun p => (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (nilradical_le_prime p.asIdeal)
  let e : PrimeSpectrum B ≃o PrimeSpectrum A :=
    N.primeSpectrumQuotientOrderIsoZeroLocus.trans
      ((OrderIso.setCongr _ _ hz).trans OrderIso.Set.univ)
  have hNm : N ≤ m := nilradical_le_prime m
  have hm' : (m.map (Ideal.Quotient.mk N)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hNm)
  have he : e ⟨m.map (Ideal.Quotient.mk N), hm'.isPrime⟩ = ⟨m, hm.isPrime⟩ := by
    apply PrimeSpectrum.ext
    change (m.map (Ideal.Quotient.mk N)).comap (Ideal.Quotient.mk N) = m
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hNm
  have hdim : ringKrullDim B = ringKrullDim A := Order.krullDim_eq_of_orderIso e
  have hht : (m.map (Ideal.Quotient.mk N)).height = m.height := by
    have h1 := PrimeSpectrum.height_eq_orderHeight
      (⟨m.map (Ideal.Quotient.mk N), hm'.isPrime⟩ : PrimeSpectrum B)
    have h2 : m.height =
        Order.height (e ⟨m.map (Ideal.Quotient.mk N), hm'.isPrime⟩) := by
      rw [he]
      exact PrimeSpectrum.height_eq_orderHeight (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
    rw [Order.height_orderIso] at h2
    exact h1.trans h2.symm
  rw [← hht, ← hdim, ← stacks_00OS (k := k) B (m.map (Ideal.Quotient.mk N)),
    IsLocalization.AtPrime.ringKrullDim_eq_height (m.map (Ideal.Quotient.mk N))]

end
