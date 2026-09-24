import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.KrullDimension

/-!+# Dimension of the closure of a prime point

The closure of a point of an affine spectrum is the zero locus of its prime
ideal. The order of primes in that zero locus is the dual of the order of its
irreducible closed subsets, and it is the spectrum order of the actual quotient
ring. Thus the topological dimension of the point closure is the Krull dimension
of that quotient. No finite type or reducedness hypothesis is needed here.

This is the topological input to MAIN C2's affine residue transcendence-degree
formula. Sources: Stacks Project, `varieties.tex`, dimension-locally-algebraic
(0A21), and the spectrum/quotient correspondence.
-/

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual closure of a prime point has the Krull dimension of its prime quotient. -/
theorem primeClosureDimension_eq_quotient
    (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    topologicalKrullDim (closure ({p} : Set (PrimeSpectrum A))) =
      ringKrullDim (A ⧸ p.asIdeal) := by
  rw [PrimeSpectrum.closure_singleton, topologicalKrullDim]
  calc
    Order.krullDim (IrreducibleCloseds (PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) =
        Order.krullDim (IrreducibleCloseds
          (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)))ᵒᵈ :=
      Order.krullDim_orderDual.symm
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) :=
      (Order.krullDim_eq_of_orderIso
        (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (p.asIdeal : Set A))).symm
    _ = ringKrullDim (A ⧸ p.asIdeal) := (ringKrullDim_quotient p.asIdeal).symm

end AlgebraicGeometry.Scheme
