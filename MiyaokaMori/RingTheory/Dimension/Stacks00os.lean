import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.Stacks00op
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainSaturatedChain
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainDimension

/-! # Stacks 00OS: local dimension of a finite type domain at a maximal ideal

Stacks 00OS: let `k` be a field and `S` a finite type `k`-algebra which is a domain. Then for every
maximal ideal `m` of `S`, `dim S_m = dim S`; equivalently, every maximal chain of primes in `S`
(starting at `(0)`, ending at a maximal ideal, with no prime strictly between consecutive terms) has
length `dim S`. Pure commutative algebra, not passing through Stacks 0A21.

Reference: Stacks 00OS (algebra-lemma-dimension-spell-it-out).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem stacks_00OS {k : Type u} [Field k] (S : Type u) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (m : Ideal S) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim S := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m]
  refine le_antisymm Ideal.height_le_ringKrullDim_of_isPrime ?_
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k S
  let R := MvPolynomial (Fin n) k
  let _ : Algebra R S := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hdimS : ringKrullDim S = (n : WithBot ℕ∞) := by
    rw [MiyaokaMori.RingTheory.ringKrullDim_eq_of_integral_injective R S,
      MvPolynomial.ringKrullDim_of_isNoetherianRing]; simp
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (m.under R) m
  rw [MvPolynomial.height_eq_of_isMaximal n (m.under R)] at h
  rw [hdimS, h]
  exact_mod_cast le_self_add

theorem stacks_00OS_maximal_chain {k : Type u} [Field k] (S : Type u) [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.FiniteType k S] (l : LTSeries (PrimeSpectrum S))
    (hhead : IsMin l.head) (hlast : IsMax l.last)
    (hcov : ∀ i : Fin l.length, l.toFun i.castSucc ⋖ l.toFun i.succ) :
    (l.length : WithBot ℕ∞) = ringKrullDim S := by
  have hfin := ringKrullDim_quotient_last_add_length_of_covBy_chain (k := k) S l hhead hcov
  have hmax : l.last.asIdeal.IsMaximal := PrimeSpectrum.isMax_iff.mp hlast
  have hfield : ringKrullDim (S ⧸ l.last.asIdeal) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
  rw [hfield, zero_add] at hfin
  exact hfin

end
