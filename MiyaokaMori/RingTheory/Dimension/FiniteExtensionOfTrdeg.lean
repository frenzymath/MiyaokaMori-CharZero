import Mathlib.FieldTheory.FinTrdeg
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Finite field extensions from equal finite transcendence degrees

For a compatible field tower `k → K → L`, equality of the two finite
transcendence degrees over `k` forces `L/K` to be algebraic. Essential finite
type then makes `L/K` finite. Essential finite type over `k` supplies both
the finite transcendence degree and essential finite type over `K`.

Sources: Stacks Tags 02R1 and 02NX. These are the field-algebra steps of the
dimension comparison; the comparison with scheme point-closure dimensions is separate.
-/

universe u v

namespace AlgebraicGeometry.Intersection

/-- Equal finite transcendence degrees make an essentially finite type
extension in the same field tower finite. -/
theorem finite_of_trdeg_eq
    (k : Type v) (K L : Type u)
    [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L]
    [FinTrdeg k K] [Algebra.EssFiniteType K L]
    (h : Algebra.trdeg k K = Algebra.trdeg k L) :
    Module.Finite K L := by
  have hsum :
      Algebra.trdeg k K + Algebra.trdeg K L =
        Algebra.trdeg k K :=
    (trdeg_add_eq k K (A := L)).trans h.symm
  have hzero : Algebra.trdeg K L = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hlarge | hzero
    · exact False.elim
        ((not_le_of_gt (trdeg_lt_aleph0 k K))
          ((le_max_left _ _).trans hlarge))
    · exact hzero
  have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp hzero
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- Essential finite type over the original base supplies both finite
transcendence degree and essential finite type over the intermediate field. -/
theorem finite_of_essFiniteType_of_trdeg_eq
    (k : Type v) (K L : Type u)
    [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L]
    [Algebra.EssFiniteType k L]
    (h : Algebra.trdeg k K = Algebra.trdeg k L) :
    Module.Finite K L := by
  have : FinTrdeg k K :=
    FinTrdeg.of_trdeg (h.trans_lt (trdeg_lt_aleph0 k L))
  have : Algebra.EssFiniteType K L :=
    Algebra.EssFiniteType.of_comp k K L
  exact finite_of_trdeg_eq k K L h

end AlgebraicGeometry.Intersection
