import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField

/-!
# Dominant pullback of Cartier local equations

For the same dominant morphism of integral schemes, local equations are mapped by the
canonical function-field map and the original covering opens are pulled back. The unit
on an entire overlap pulls back by the actual map on structure-sheaf sections. This
constructs `CartierLocalData` without choosing a new divisor or changing its index set.

This is the local-equation input to the projection comparison in the proof of the main theorem:
after factoring the source through its integral image curve, compatible sections have compatible
Cartier equations. The section and line-module pullback comparison, as well as the weighted
proper-pushforward formula, remain separate constructions.

Sources: Theorem 1.1 of the paper; Stacks Project, `divisors.tex`,
`lemma-pullback-meromorphic-sections-defined`, and `chow.tex`, `lemma-equal-c1-as-cycles`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Intersection

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Mapping a section's generic germ agrees with pulling back the actual section. -/
theorem dominantFunctionFieldMap_germToFunctionField
    (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (a : Γ(Y, U)) :
    AlgebraicGeometry.Scheme.dominantFunctionFieldMap f (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) := by
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty (f ⁻¹ᵁ U)›
  rw [← Y.algebraMap_germ_eq_germToFunctionField (x := f x) hx a,
    AlgebraicGeometry.Scheme.dominantFunctionFieldMap_algebraMap f x,
    f.germ_stalkMap_apply U x hx a,
    X.algebraMap_germ_eq_germToFunctionField hx (f.app U a)]

/-- A unit ratio on an open set pulls back to a unit ratio on its full inverse image. -/
theorem isUnitRatioOn_pullback_dominant
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens)
    (a b : Y.functionField) (h : IsUnitRatioOn U a b) :
    IsUnitRatioOn (f ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f a)
      (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f b) := by
  intro hV
  have : Nonempty (f ⁻¹ᵁ U) := hV
  have hU : Nonempty U := by
    obtain ⟨⟨x, hx⟩⟩ := hV
    exact ⟨⟨f x, hx⟩⟩
  obtain ⟨s, hs, hratio⟩ := h hU
  refine ⟨f.app U s, hs.map (f.app U).hom, ?_⟩
  rw [← dominantFunctionFieldMap_germToFunctionField f U s, hratio]
  exact map_div₀ (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom a b

namespace CartierLocalData

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Pull back the original Cartier cover, equations and overlap units along a dominant map. -/
noncomputable def pullbackDominant
    (D : CartierLocalData Y) (f : X ⟶ Y) [IsDominant f] :
    CartierLocalData X where
  index := D.index
  opens i := f ⁻¹ᵁ D.opens i
  cover := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨D.indexAt (f x), D.indexAt_mem (f x)⟩
  locallyFinite := D.locallyFinite.preimage_continuous f.continuous
  equation i := AlgebraicGeometry.Scheme.dominantFunctionFieldMap f (D.equation i)
  equation_ne_zero i := fun h ↦ D.equation_ne_zero i
    ((AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom.injective (by simpa using h))
  ratio_unit i j := by
    change IsUnitRatioOn (f ⁻¹ᵁ (D.opens i ⊓ D.opens j)) _ _
    exact isUnitRatioOn_pullback_dominant f _ _ _ (D.ratio_unit i j)

/-- Every pulled-back chart computes the coefficient using the mapped original equation. -/
theorem pullbackDominant_coefficient_eq_ord
    (D : CartierLocalData Y) (f : X ⟶ Y) [IsDominant f]
    (x : X) (i : D.index) (hxi : f x ∈ D.opens i) :
    (D.pullbackDominant f).coefficient x =
      X.ord (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f (D.equation i)) x := by
  exact (D.pullbackDominant f).coefficient_eq_ord_of_mem x i hxi

end CartierLocalData

end AlgebraicGeometry.Intersection
