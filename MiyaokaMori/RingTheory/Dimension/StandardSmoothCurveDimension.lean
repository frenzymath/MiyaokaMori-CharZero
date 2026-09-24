import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Krull dimension of nonempty standard smooth affine curves

A nonzero étale algebra over a one-dimensional Jacobson domain has Krull dimension one.
The upper bound comes from incomparability of primes in a quasi-finite algebra. For the
lower bound, the contraction of an actual maximal ideal is maximal by the finite-type
form of Zariski's lemma, and flat going-down lifts a strict chain below that ideal.

Standard smooth algebras of relative dimension one over a field factor through an étale
map from a polynomial ring in one variable, so the first theorem applies to their actual
coordinate rings. This supplies the algebraic part of the source-curve dimension bridge
for the main theorem of the paper; passing from affine charts to the scheme is separate.

Sources: Stacks, Algebra, `definition-standard-smooth`, `lemma-standard-smooth`, and
`lemma-flat-going-down`; Morphisms, `definition-smooth-relative-dimension`.
-/

noncomputable section

namespace MiyaokaMori.RingTheory

universe u v

/-- A nonzero étale algebra over a one-dimensional Jacobson domain has dimension one. -/
theorem ringKrullDim_eq_one_of_etale
    (A : Type u) (S : Type v) [CommRing A] [CommRing S]
    [IsDomain A] [IsJacobsonRing A] [Nontrivial S]
    [Algebra A S] [Algebra.Etale A S]
    (hA : ringKrullDim A = 1) :
    ringKrullDim S = 1 := by
  have : Algebra.FiniteType A S := inferInstance
  have : Algebra.FormallyUnramified A S := inferInstance
  have : Algebra.QuasiFinite A S := inferInstance
  have : Module.Flat A S := Algebra.Smooth.flat A S
  have : Algebra.HasGoingDown A S := Algebra.HasGoingDown.of_flat
  have hupper : ringKrullDim S ≤ ringKrullDim A := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S))
    intro P Q hPQ
    have hPle : P.asIdeal ≤ Q.asIdeal := hPQ.le
    have : P.asIdeal.IsPrime := P.isPrime
    have : Q.asIdeal.IsPrime := Q.isPrime
    refine lt_of_le_of_ne ?_ ?_
    · change Ideal.comap (algebraMap A S) P.asIdeal ≤
        Ideal.comap (algebraMap A S) Q.asIdeal
      exact Ideal.comap_mono hPle
    · intro h
      have hunder : P.asIdeal.under A = Q.asIdeal.under A :=
        congrArg PrimeSpectrum.asIdeal h
      exact hPQ.ne (PrimeSpectrum.ext
        (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A)
          P.asIdeal Q.asIdeal hPle hunder))
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal S
  have : Q.IsMaximal := hQ
  have : Q.IsPrime := hQ.isPrime
  letI : Field (S ⧸ Q) := Ideal.Quotient.field Q
  have : Algebra.FiniteType A (S ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A Q)
      (Ideal.Quotient.mkₐ_surjective A Q)
  have : Module.Finite A (S ⧸ Q) :=
    finite_of_finite_type_of_isJacobsonRing A (S ⧸ Q)
  have : Algebra.IsIntegral A (S ⧸ Q) := Algebra.IsIntegral.of_finite A (S ⧸ Q)
  have hcomap : (⊥ : Ideal (S ⧸ Q)).under A = Q.under A := by
    ext a
    change Ideal.Quotient.mk Q (algebraMap A S a) = 0 ↔ algebraMap A S a ∈ Q
    exact Ideal.Quotient.eq_zero_iff_mem
  have : (Q.under A).IsMaximal := by
    rw [← hcomap]
    exact Ideal.IsMaximal.under A (⊥ : Ideal (S ⧸ Q))
  have : (Q.under A).IsPrime := Ideal.IsPrime.under A Q
  have : Q.LiesOver (Q.under A) := ⟨rfl⟩
  have hnotfield : ¬ IsField A := by
    intro hfield
    exact one_ne_zero (hA.symm.trans (ringKrullDim_eq_zero_of_isField hfield))
  obtain ⟨P, hPQ, hP, _⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (p := (⊥ : Ideal A)) (q := Q.under A) Q
      (Ideal.bot_lt_of_maximal (Q.under A) hnotfield)
  have hlower : 1 ≤ ringKrullDim S := by
    apply Order.one_le_krullDim_iff.mpr
    refine ⟨⟨P, hP⟩, ⟨Q, hQ.isPrime⟩, ?_⟩
    change P < Q
    exact hPQ
  exact le_antisymm (hupper.trans_eq hA) hlower

/-- A nonzero standard smooth algebra of relative dimension one over a field has dimension one. -/
theorem ringKrullDim_eq_one_of_standardSmooth
    (K : Type u) (S : Type v) [Field K] [CommRing S] [Nontrivial S]
    (f : K →+* S) (hf : f.IsStandardSmoothOfRelativeDimension 1) :
    ringKrullDim S = 1 := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin 1) K) S := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) K) S := hg.toAlgebra
  apply ringKrullDim_eq_one_of_etale (MvPolynomial (Fin 1) K) S
  simp

end MiyaokaMori.RingTheory
