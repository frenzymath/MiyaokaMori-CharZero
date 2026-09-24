import MiyaokaMori.AlgebraicGeometry.Divisors.CodimensionOneFinite
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A unit neighbourhood away from one point

For a nonzero section on an open subset of an integral Noetherian scheme of
dimension at most one, the complement of its actual basic open is a finite set
of closed points.  Removing all of those points except a specified point gives
an open neighbourhood on which the original section has a unit germ everywhere
else.  The section remains the original section; this result does not construct
a Cartier divisor or replace its zero locus by a singleton.
-/

noncomputable section

open AlgebraicGeometry Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme
open AlgebraicGeometry.Divisors

/-- Shrink an open around `z` so that a nonzero section is a unit away from `z`. -/
theorem exists_open_isUnit_germ_off_point
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (U : X.Opens) (s : Γ(X, U)) (hs : s ≠ 0)
    (z : X) (hzU : z ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), z ∈ V ∧
      ∀ (y : X) (hyV : y ∈ V), y ≠ z →
        IsUnit (X.presheaf.germ U y (hVU hyV) s) := by
  letI : Nonempty U := ⟨⟨z, hzU⟩⟩
  let W : X.Opens := X.basicOpen s
  have hsη : X.germToFunctionField U s ≠ 0 := by
    intro hsη
    apply hs
    apply X.germToFunctionField_injective U
    simpa using hsη
  have hηU : genericPoint X ∈ U := by
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  have hηW : genericPoint X ∈ W := by
    rw [show W = X.basicOpen s from rfl, Scheme.mem_basicOpen X s (genericPoint X) hηU]
    exact (isUnit_iff_ne_zero.mpr hsη)
  letI : Nonempty W := ⟨⟨genericPoint X, hηW⟩⟩
  have hdim' : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hbad_coheight (y : X) (hy : y ∉ W) : Order.coheight y = 1 := by
    have hyTop : ¬(⊤ : X) ≤ y := by
      intro hty
      obtain ⟨w, hw⟩ := (inferInstance : Nonempty W)
      have htopW : (⊤ : X) ∈ W :=
        (genericPoint_specializes w).mem_open W.isOpen hw
      exact hy ((Scheme.le_iff_specializes.mp hty).mem_open W.isOpen htopW)
    have hpos : 0 < Order.coheight y :=
      Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top hyTop)
    have hle : Order.coheight y ≤ 1 :=
      WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim y).trans hdim')
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr (ne_of_gt hpos))
  have hbad_finite : {y : X | y ∉ W}.Finite := by
    apply (finite_codimensionOneOutside X W).subset
    intro y hy
    exact ⟨hy, hbad_coheight y hy⟩
  let B : Set X := {y : X | y ∉ W ∧ y ≠ z}
  have hB_finite : B.Finite := by
    apply hbad_finite.subset
    intro y hy
    exact hy.1
  have hB_closed : IsClosed B := by
    have hsingle : ∀ y ∈ B, IsClosed ({y} : Set X) := by
      intro y hy
      exact Intersection.isClosed_singleton_of_coheight_eq_one hdim y
        (hbad_coheight y hy.1)
    have hUnion : (⋃ y ∈ B, ({y} : Set X)) = B := by
      ext y
      simp [B]
    rw [← hUnion]
    exact hB_finite.isClosed_biUnion hsingle
  let Vbad : X.Opens := ⟨Bᶜ, isOpen_compl_iff.mpr hB_closed⟩
  let V : X.Opens := U ⊓ Vbad
  have hVU : V ≤ U := inf_le_left
  refine ⟨V, hVU, ?_, ?_⟩
  · exact ⟨hzU, by
      intro hzB
      exact hzB.2 rfl⟩
  · intro y hyV hyz
    have hyW : y ∈ W := by
      by_contra hyW
      exact hyV.2 ⟨hyW, hyz⟩
    exact (Scheme.mem_basicOpen X s y hyV.1).mp hyW

end AlgebraicGeometry.Scheme
