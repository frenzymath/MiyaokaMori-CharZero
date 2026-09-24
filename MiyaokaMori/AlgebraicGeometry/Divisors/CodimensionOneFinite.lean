import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finitely many codimension-one points outside a nonempty open

A proper closed subset of an integral Noetherian scheme is a finite union of irreducible
closed subsets. Each codimension-one point in that subset must be the generic point of one
of those finitely many subsets. The order used here is Mathlib's scheme order:
`x ≤ y` means that `y` specializes to `x`, so coheight is codimension.

This is the topological support step for the rational coordinate divisors of §3 of the paper
(the weighted order (3.3)). The scheme and its points are Mathlib's actual
objects. The subsequent finite-support theorem applies to the same function field as the
curve-stalk valuations used in the positive-jet construction.
-/

noncomputable section

open Set TopologicalSpace AlgebraicGeometry Order

universe u

namespace AlgebraicGeometry.Divisors

/-- Only finitely many codimension-one points lie outside a nonempty open of an integral
Noetherian scheme. -/
theorem finite_codimensionOneOutside (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : X | x ∉ U ∧ Order.coheight x = 1}.Finite := by
  let Z : Set X := (U : Set X)ᶜ
  have hZclosed : IsClosed Z := isClosed_compl_iff.mpr U.isOpen
  obtain ⟨S, hSfin, hSclosed, hSirred, hSsup⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZclosed
  have : Finite S := hSfin
  let p : S → X := fun t ↦ (hSirred t.1 t.2).genericPoint
  apply (Set.finite_range p).subset
  intro x hx
  have hxZ : x ∈ Z := hx.1
  obtain ⟨t, ht, hxt⟩ := mem_sUnion.mp (hSsup ▸ hxZ)
  refine ⟨⟨t, ht⟩, ?_⟩
  let η : X := (hSirred t ht).genericPoint
  have hηgeneric : IsGenericPoint η t :=
    (hSirred t ht).isGenericPoint_genericPoint (hSclosed t ht)
  have ht_sub : t ⊆ Z := by
    intro y hy
    rw [hSsup]
    exact subset_sUnion_of_mem ht hy
  have hηZ : η ∈ Z := ht_sub hηgeneric.mem
  have hηnotTop : ¬(⊤ : X) ≤ η := by
    intro hη
    obtain ⟨u, hu⟩ := (inferInstance : Nonempty U)
    have htopU : (⊤ : X) ∈ U :=
      (genericPoint_specializes u).mem_open U.isOpen hu
    exact hηZ ((Scheme.le_iff_specializes.mp hη).mem_open U.isOpen htopU)
  have hηpos : 0 < Order.coheight η :=
    Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top hηnotTop)
  have hle : x ≤ η := Scheme.le_iff_specializes.mpr (hηgeneric.specializes hxt)
  have hηle : Order.coheight η ≤ 1 := by
    rw [← hx.2]
    exact Order.coheight_anti hle
  by_cases hback : η ≤ x
  · exact ((Scheme.le_iff_specializes.mp hle).antisymm
      (Scheme.le_iff_specializes.mp hback)).eq
  have hlt : x < η := lt_of_le_not_ge hle hback
  have hηlt : Order.coheight η < Order.coheight x :=
    Order.coheight_strictAnti hlt (hηle.trans_lt (by simp))
  have hηzero : Order.coheight η = 0 := by
    rw [hx.2] at hηlt
    exact Order.lt_one_iff.mp hηlt
  exact (ne_of_gt hηpos hηzero).elim

end AlgebraicGeometry.Divisors
