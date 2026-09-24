import MiyaokaMori.AlgebraicGeometry.Morphisms.TotalSpaceAgreesTotLine

/-! # The fiber of the total space maps into the fiber of the ruled surface

The fiber of `Tot(L) → C̃` over `y` maps into the fiber of the ruling `π_W : W = P(O ⊕ L) → C̃` over
`y`, by base change of the open immersion `Tot(L) ⊆ W`; the map is an open immersion compatible with
the fiber embeddings.

Source: §2 of the paper (`W = P(O ⊕ L)`, `Tot(L) = W ∖ σ_L`) and the proof of Theorem 4.2.
Mathlib: `Scheme.pullback_map_isOpenImmersion`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The fiber of `Tot(L) → C̃` over `y` maps into the fiber of the ruling `π_W : W → C̃` over `y`,
induced by the open immersion `Tot(L) ⊆ W` (`pullback.map` along `ruledSurface.totalSpaceIncl L`,
identity on `Spec κ(y)` and `C̃`). -/
noncomputable def totalSpaceFiberToRuledFiber {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (y : C.toScheme) :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ⟶ (ruledSurface.π L).fiber y :=
  pullback.map (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
    (C.toScheme.fromSpecResidueField y) (ruledSurface.π L) (C.toScheme.fromSpecResidueField y)
    (ruledSurface.totalSpaceIncl L) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ruledSurface.totalSpaceIncl_comp_π]) (by simp)

/-- Compatibility with the fiber embeddings: `Tot(L)_y → W_y → W` equals `Tot(L)_y → Tot(L) → W`. -/
theorem totalSpaceFiberToRuledFiber_comp_fiberι {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (y : C.toScheme) :
    totalSpaceFiberToRuledFiber L y ≫ (ruledSurface.π L).fiberι y =
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y ≫ ruledSurface.totalSpaceIncl L := by
  unfold totalSpaceFiberToRuledFiber AlgebraicGeometry.Scheme.Hom.fiberι
  exact pullback.lift_fst _ _ _

/-- The fiber inclusion `Tot(L)_y ⟶ W_y` is an open immersion (base change of the open immersion
`Tot(L) ⊆ W`; Mathlib `Scheme.pullback_map_isOpenImmersion`). Not registered as a global instance. -/
theorem totalSpaceFiberToRuledFiber_isOpenImmersion {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (y : C.toScheme) :
    AlgebraicGeometry.IsOpenImmersion (totalSpaceFiberToRuledFiber L y) := by
  have := ruledSurface.totalSpaceIncl_isOpenImmersion L
  unfold totalSpaceFiberToRuledFiber
  exact AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _

end
