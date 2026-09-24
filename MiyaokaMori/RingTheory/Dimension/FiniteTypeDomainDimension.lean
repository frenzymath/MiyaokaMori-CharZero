import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Dimension and transcendence degree of finite type domains

An injective integral algebra extension preserves actual Krull dimension. Incomparability
makes contraction strict on prime chains, while lying-over and going-up lift every finite
prime chain. Noether normalization then identifies the dimension of a finite type domain
over a field with the transcendence degree of its actual algebra structure.

For a prime quotient, the actual residue field is a fraction field of that quotient, so
its transcendence degree is the same. The result uses `Cardinal.toENat`, retaining infinity
without a default finite value. These are the affine algebraic steps needed for the point
closure dimension bridge; no scheme-level residue-field comparison is asserted.

Sources: Stacks, Algebra, `lemma-Noether-normalization` (00OW); Varieties,
`lemma-dimension-locally-algebraic`, item `item-dimension-irreducible-trdeg` (0A21).
-/

noncomputable section

open scoped nonZeroDivisors

namespace MiyaokaMori.RingTheory

universe u

/-- An integral algebra whose structure map is injective preserves Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  have : Algebra.HasGoingUp R S := Algebra.HasGoingUp.of_isIntegral
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    have : p.asIdeal.IsPrime := p.isPrime
    have hpq' : p.asIdeal < q.asIdeal := hpq
    change p.asIdeal.comap (algebraMap R S) < q.asIdeal.comap (algebraMap R S)
    exact Ideal.IsIntegral.comap_lt_comap (R := R) hpq'
  · change (⨆ l : LTSeries (PrimeSpectrum R), (l.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun l ↦ ?_
    obtain ⟨P, hP⟩ := (Algebra.IsIntegral.comap_surjective R S) l.head
    have : P.asIdeal.IsPrime := P.isPrime
    have : P.asIdeal.LiesOver l.head.asIdeal :=
      ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L

/-- The Krull dimension of a finite type domain over a field is its transcendence degree. -/
theorem finiteTypeDomain_ringKrullDim_eq_trdeg
    (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  letI : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : IsScalarTower k P A := IsScalarTower.of_algHom g
  have htr0 : Algebra.trdeg P A = 0 := trdeg_eq_zero
  have hpoly : Algebra.trdeg k P = (n : Cardinal.{u}) := by simp [P]
  have htr : Algebra.trdeg k A = (n : Cardinal.{u}) := by
    simpa only [htr0, hpoly, add_zero] using (trdeg_add_eq k P (A := A)).symm
  rw [ringKrullDim_eq_of_integral_injective P A, htr]
  simp [P, Cardinal.toENat_nat]

/-- A prime quotient has dimension equal to the transcendence degree of its actual residue field. -/
theorem quotient_ringKrullDim_eq_residue_trdeg
    (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) =
      (Cardinal.toENat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := by
  have : Algebra.FiniteType k (A ⧸ p) := Algebra.FiniteType.quotient k p
  have : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
    IsLocalization.isAlgebraic p.ResidueField (nonZeroDivisors (A ⧸ p))
  have : FaithfulSMul (A ⧸ p) p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ p) p.ResidueField).mpr
      p.injective_algebraMap_quotient_residueField
  have : IsScalarTower k (A ⧸ p) p.ResidueField := inferInstance
  have htr : Algebra.trdeg k (A ⧸ p) = Algebra.trdeg k p.ResidueField := by
    simpa only [trdeg_eq_zero, add_zero] using
      trdeg_add_eq k (A ⧸ p) (A := p.ResidueField)
  rw [finiteTypeDomain_ringKrullDim_eq_trdeg k (A ⧸ p), htr]

end MiyaokaMori.RingTheory
