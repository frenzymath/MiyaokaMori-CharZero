import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Preorder.Finite

/-!
# Coordinates of the top exterior power in a specified finite basis

For an actual basis indexed by `Fin n`, Mathlib's exterior-power basis has one
index, the whole finite index set. Its ordered enumeration is the identity.
Consequently the basis coordinate at that index gives an explicit linear
equivalence from the existing top exterior power to the coefficient ring.

The ordered basis wedge maps to one, the inverse sends a coefficient to its
scalar multiple of that same wedge, and arbitrary wedges map to the determinant
of their coordinate matrix. The matrix uses vectors as columns; the transposed
matrix in Mathlib's exterior-pairing formula has the same determinant.

No nontriviality or positive-rank hypothesis is used. In degree zero the ordered
wedge is empty and its coordinate is the coefficient unit, also over the zero ring.
These module-level helpers underlie the frames of top exterior powers (determinants) of
locally free sheaves; they do not construct any sheaf restriction comparison.

Sources: Stacks Project, `algebra.tex`, the ordered exterior basis preceding
`lemma-free-tensor-algebra`; `modules.tex`, Rank and determinant; the paper, main theorem
(the determinant of the tangent bundle).
-/

noncomputable section

namespace MiyaokaMori.Algebra.TopExteriorBasis

/-- The full finite index set as the unique index of a top exterior-power basis. -/
def topIndex (n : ℕ) : Set.powersetCard (Fin n) n :=
  ⟨Finset.univ, by simp⟩

/-- A subset of `Fin n` with cardinality `n` is the whole index set. -/
theorem eq_topIndex {n : ℕ} (s : Set.powersetCard (Fin n) n) : s = topIndex n := by
  apply Subtype.ext
  exact Finset.eq_univ_of_card s.val (by simpa using s.prop)

/-- The increasing enumeration of the full index set keeps the original order. -/
@[simp]
theorem topIndex_enumeration (n : ℕ) (i : Fin n) :
    Set.powersetCard.ofFinEmbEquiv.symm (topIndex n) i = i :=
  (Set.powersetCard.ofFinEmbEquiv.symm (topIndex n)).strictMono.apply_eq

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
  (b : Module.Basis (Fin n) R M)

/-- Mathlib's top exterior basis vector is the ordered wedge of the supplied basis. -/
theorem topExteriorBasisVector :
    b.exteriorPower n (topIndex n) = exteriorPower.ιMulti R n b := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  congr 1
  funext i
  exact congrArg b (topIndex_enumeration n i)

/-- The actual top exterior power is linearly equivalent to the coefficient ring in this basis. -/
def topExteriorEquiv : (⋀[R]^n M) ≃ₗ[R] R := by
  letI : Unique (Set.powersetCard (Fin n) n) :=
    { default := topIndex n
      uniq := eq_topIndex }
  exact (b.exteriorPower n).equivFun.trans
    (LinearEquiv.funUnique (Set.powersetCard (Fin n) n) R R)

/-- The equivalence evaluates the existing exterior basis representation at the full index. -/
@[simp]
theorem topExteriorEquiv_apply (x : ⋀[R]^n M) :
    topExteriorEquiv b x = (b.exteriorPower n).repr x (topIndex n) := rfl

/-- The ordered wedge of the given basis has coordinate one, including the empty wedge. -/
@[simp]
theorem topExteriorEquiv_basis_wedge :
    topExteriorEquiv b (exteriorPower.ιMulti R n b) = 1 := by
  rw [topExteriorEquiv_apply, ← topExteriorBasisVector b]
  simp

/-- The inverse equivalence multiplies the same ordered basis wedge by the coefficient. -/
@[simp]
theorem topExteriorEquiv_symm_apply (r : R) :
    (topExteriorEquiv b).symm r = r • exteriorPower.ιMulti R n b := by
  apply (topExteriorEquiv b).injective
  simp only [LinearEquiv.apply_symm_apply, map_smul, topExteriorEquiv_basis_wedge,
    smul_eq_mul, mul_one]

/-- Wedge coordinates are determinants of the matrix whose columns are the vector coordinates. -/
theorem topExteriorEquiv_wedge_coords (v : Fin n → M) :
    topExteriorEquiv b (exteriorPower.ιMulti R n v) =
      (Matrix.of fun i j : Fin n ↦ b.repr (v j) i).det := by
  rw [topExteriorEquiv_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [topIndex_enumeration, Module.Basis.coord_apply]
  exact Matrix.det_transpose (Matrix.of fun i j : Fin n ↦ b.repr (v j) i)

/-- The same wedge-coordinate formula expressed by the determinant of the specified basis. -/
theorem topExteriorEquiv_wedge_det (v : Fin n → M) :
    topExteriorEquiv b (exteriorPower.ιMulti R n v) = b.det v := by
  rw [topExteriorEquiv_wedge_coords, Module.Basis.det_apply]
  rfl

end MiyaokaMori.Algebra.TopExteriorBasis
