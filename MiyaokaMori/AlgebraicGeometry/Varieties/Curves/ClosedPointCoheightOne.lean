import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-!
# Closed points of integral one-dimensional schemes

A closed point of an integral scheme of topological Krull dimension one has
coheight one in the scheme's specialization order. This supplies the dimension
part of the prerequisite for local parameters on a curve. For a smooth projective
curve, its dimension is supplied separately by the smooth-chart dimension
construction.

The proof uses the order isomorphism between points and irreducible closed
subsets. The generic point is the greatest point; a closed point has height zero
and cannot also be greatest in a space of dimension one. No regularity, rational
point, local Noetherian, or discrete-valuation hypothesis is needed.

Sources: Stacks, Topology, `definition-Krull`; Varieties,
`lemma-dimension-locally-algebraic`, especially the closed-point dimension clause.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A closed point of an integral scheme of dimension one has coheight one. -/
theorem closedPoint_coheight_eq_one_of_dimension_one
    (X : Scheme.{u}) [IsIntegral X] (hX : topologicalKrullDim X = 1)
    (z : X) (hz : IsClosed ({z} : Set X)) : Order.coheight z = 1 := by
  have hdim : Order.krullDim X = 1 := by
    calc
      Order.krullDim X = topologicalKrullDim X :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm
      _ = 1 := hX
  have hu : Order.coheight z ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim z).trans_eq hdim
  have hn : Order.coheight z ≠ 0 := by
    intro hzero
    have hm : IsMax z := Order.coheight_eq_zero.mp hzero
    have hheight : Order.height (⊤ : X) ≤ 0 := by
      rw [← Scheme.height_of_isClosed hz]
      exact Order.height_mono (hm le_top)
    have hheight' : (Order.height (⊤ : X) : WithBot ℕ∞) ≤ 0 := by
      exact_mod_cast hheight
    rw [Order.height_top_eq_krullDim, hdim] at hheight'
    exact (not_le_of_gt (zero_lt_one : (0 : WithBot ℕ∞) < 1)) hheight'
  exact le_antisymm hu (Order.one_le_iff_ne_zero.mpr hn)

end AlgebraicGeometry.Scheme
