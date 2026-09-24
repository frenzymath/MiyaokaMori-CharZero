import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PrimeClosureDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Point-closure dimension on an affine scheme over a field

Local finite type of the actual map `Spec A ⟶ Spec k` gives finite type of
the algebra defined by its `Spec.preimage`. The closure of a prime point has
the dimension of the actual prime quotient. Noether normalization compares
that dimension with the transcendence degree of its ideal residue field.
The existing affine residue-field algebra equivalence identifies this with
the scheme residue field over exactly the specified `pointBaseMap`.

This proves the affine formula used in MAIN C2. Passing to a general scheme
and connecting its actual reduced point closures remain separate steps.
Sources: Stacks Project, `varieties.tex`, dimension-locally-algebraic (0A21),
and `chow.tex`, equal-dimension (02R1).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Intersection

/-- On an affine scheme locally of finite type over a field, the actual point closure has
dimension equal to the transcendence degree of the specified scheme residue field. -/
theorem spec_pointClosureDimension_eq_trdeg {k : Type u} [Field k]
    (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (p : Spec A) :
    letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
    pointClosureDimension (Spec A) p =
      (Cardinal.toENat (Algebra.trdeg k ((Spec A).residueField p)) : WithBot ℕ∞) := by
  letI : Algebra k A := (Spec.preimage f).hom.toAlgebra
  letI : Algebra k ((Spec A).residueField p) := (pointBaseMap f p).hom.toAlgebra
  have hft : (Spec.preimage f).hom.FiniteType :=
    HasRingHomProperty.Spec_iff.mp (show LocallyOfFiniteType (Spec.map (Spec.preimage f)) by
      simpa only [Spec.map_preimage] using (inferInstance : LocallyOfFiniteType f))
  have : Algebra.FiniteType k A := hft
  have : p.asIdeal.IsPrime := p.isPrime
  calc
    pointClosureDimension (Spec A) p = ringKrullDim (A ⧸ p.asIdeal) :=
      (pointClosureDimension_eq_topologicalKrullDim_closure (Spec A) p).trans
        (AlgebraicGeometry.Scheme.primeClosureDimension_eq_quotient A p)
    _ = (Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : WithBot ℕ∞) :=
      MiyaokaMori.RingTheory.quotient_ringKrullDim_eq_residue_trdeg k A p.asIdeal
    _ = (Cardinal.toENat (Algebra.trdeg k ((Spec A).residueField p)) : WithBot ℕ∞) :=
      congrArg (fun c : Cardinal.{u} ↦ (Cardinal.toENat c : WithBot ℕ∞))
        (specResidueField_trdeg_eq A f p).symm

end AlgebraicGeometry.Intersection
