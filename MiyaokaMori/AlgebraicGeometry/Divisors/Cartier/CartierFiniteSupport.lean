import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdFiniteOnNoetherianOpen
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalData
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree

/-!
# Finite Cartier support and the associated zero cycle on a curve

For the existing `CartierLocalData`, compactness of a Noetherian scheme supplies a finite
subcover. Unit transitions identify its coefficient with the order of each local equation,
so `finite_support_ord` proves that the same coefficient function has finite support.

On a scheme of dimension at most one, a codimension-one point is closed. Thus the existing
`FiniteCartierDivisor.zeroCycle` applies to the same coefficients without a separate support
hypothesis. Neither smoothness, DVR stalks, nor properness is needed here. No degree is defined.

Sources: Stacks Project, Tags 02SG and 02SJ; Theorem 1.1 of the paper and the
coordinate-divisor calculation in the proof of Proposition 2.4.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace Order
open scoped Classical

namespace AlgebraicGeometry.Intersection

universe u

/-- A codimension-one point of a scheme of dimension at most one is closed. -/
theorem isClosed_singleton_of_coheight_eq_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : coheight x = 1) :
    IsClosed ({x} : Set X) := by
  have hdim' : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hcoheight (y : X) : coheight y ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim y).trans hdim')
  apply closure_eq_iff_isClosed.mp
  apply Set.Subset.antisymm
  · intro y hy
    have hyx : y ≤ x :=
      Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
    have hxy : x ≤ y := by
      by_contra h
      have hlt : coheight x < coheight y :=
        Order.coheight_strictAnti (lt_of_le_not_ge hyx h) (by simp [hx])
      rw [hx] at hlt
      exact (not_lt_of_ge (hcoheight y)) hlt
    exact ((Scheme.le_iff_specializes.mp hxy).antisymm
      (Scheme.le_iff_specializes.mp hyx)).eq
  · exact subset_closure

/-- Codimension-one points have zero-dimensional closures on a scheme of dimension at most one. -/
theorem pointClosureDimension_eq_zero_of_coheight_eq_one {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : coheight x = 1) :
    pointClosureDimension X x = 0 :=
  pointClosureDimension_eq_zero_of_isClosed x
    (isClosed_singleton_of_coheight_eq_one hdim x hx)

namespace CartierLocalData

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Every chart containing a point computes the existing Cartier coefficient by its own equation. -/
theorem coefficient_eq_ord_of_mem (D : CartierLocalData X) (x : X) (i : D.index)
    (hxi : x ∈ D.opens i) : D.coefficient x = X.ord (D.equation i) x := by
  by_cases hx : coheight x = 1
  · rw [D.coefficient_eq_ord x hx]
    exact D.coefficient_eq_of_mem x hx (D.indexAt x) i (D.indexAt_mem x) hxi
  · rw [D.coefficient_eq_zero_of_coheight_ne_one x hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Compactness and the finite support of each local equation prove finite Cartier support. -/
theorem coefficient_finite_support [IsNoetherian X] (D : CartierLocalData X) :
    (Function.support D.coefficient).Finite := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ (D.opens i : Set X)) (fun i ↦ (D.opens i).isOpen) D.cover.ge
  have hfin : (⋃ i ∈ s, Function.support (X.ord (D.equation i))).Finite :=
    s.finite_toSet.biUnion fun i _ ↦ AlgebraicGeometry.Divisors.finite_support_ord X (D.equation i) (D.equation_ne_zero i)
  apply hfin.subset
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  change X.ord (D.equation i) x ≠ 0
  change D.coefficient x ≠ 0 at hx
  rwa [D.coefficient_eq_ord_of_mem x i hxi] at hx

/-- The original Cartier datum with its proved, rather than assumed, finite-support witness. -/
def toFiniteCartierDivisor [IsNoetherian X] (D : CartierLocalData X) :
    FiniteCartierDivisor X where
  toCartierLocalData := D
  finite_support := D.coefficient_finite_support

@[simp]
theorem toFiniteCartierDivisor_toCartierLocalData [IsNoetherian X]
    (D : CartierLocalData X) : D.toFiniteCartierDivisor.toCartierLocalData = D := rfl

/-- The same nonzero coefficients are supported in dimension zero on a curve. -/
theorem coefficient_pointClosureDimension_zero (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : D.coefficient x ≠ 0) :
    pointClosureDimension X x = 0 := by
  apply pointClosureDimension_eq_zero_of_coheight_eq_one hdim x
  by_contra h
  exact hx (D.coefficient_eq_zero_of_coheight_ne_one x h)

/-- The proved dimension condition for the original finite Cartier divisor. -/
theorem zeroDimensionalSupport [IsNoetherian X] (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) : D.toFiniteCartierDivisor.ZeroDimensionalSupport := by
  constructor
  intro x hx
  exact D.coefficient_pointClosureDimension_zero hdim x hx

/-- The existing zero-cycle construction, supplied only with the proved support witnesses. -/
def zeroCycle [IsNoetherian X] (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) : DimensionCycle X 0 :=
  D.toFiniteCartierDivisor.zeroCycle (D.zeroDimensionalSupport hdim)

@[simp]
theorem zeroCycle_apply [IsNoetherian X] (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    (D.zeroCycle hdim).1 x = D.coefficient x := rfl

/-- The resulting zero cycle retains the finite support of the original Cartier coefficients. -/
theorem zeroCycle_support_finite [IsNoetherian X] (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) : (Function.support (D.zeroCycle hdim).1).Finite :=
  D.toFiniteCartierDivisor.zeroCycle_support_finite (D.zeroDimensionalSupport hdim)

end CartierLocalData

end AlgebraicGeometry.Intersection
