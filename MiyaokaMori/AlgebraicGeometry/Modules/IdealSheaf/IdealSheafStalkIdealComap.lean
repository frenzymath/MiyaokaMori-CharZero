import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap

/-! # Stalk ideals of inverse image ideal sheaves

The stalk of the inverse image ideal sheaf: `(f⁻¹I·O_X)_x = I_{f(x)}·O_{X,x}`.

References: Stacks 01HQ; Hartshorne II p.163 (definition of `f⁻¹I·O_X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `(I.comap f)_x` is the extension of `I_{f x}` along the stalk map `O_{Y,f x} → O_{X,x}`.

Proof sketch: choose an affine open `U ⊆ Y` containing `f x` and an affine open `V ⊆ f⁻¹U`
containing `x`. By `stalkIdeal_eq_map_germ` (on both sides) and `comap_ideal_eq_map_appLE`, the
left side is `I(U).map (f.appLE ≫ germ_x)` and the right side is
`I(U).map (germ_{f x} ≫ f.stalkMap x)`; these agree by `Scheme.Hom.germ_stalkMap` and the
definition of `Scheme.Hom.appLE`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_comap
    {X Y : AlgebraicGeometry.Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    (I.comap f).stalkIdeal x = (I.stalkIdeal (f x)).map (f.stalkMap x).hom := by
  obtain ⟨U, hU, hfxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (Set.mem_univ (f x))
  obtain ⟨V, hV, hxV, hVU⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ U) hfxU
  have e : V ≤ f ⁻¹ᵁ U := hVU
  rw [I.stalkIdeal_eq_map_germ (f x) ⟨U, hU⟩ hfxU,
    (I.comap f).stalkIdeal_eq_map_germ x ⟨V, hV⟩ hxV,
    I.comap_ideal_eq_map_appLE f ⟨U, hU⟩ ⟨V, hV⟩ e, Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 2
  rw [AlgebraicGeometry.Scheme.Hom.germ_stalkMap, AlgebraicGeometry.Scheme.Hom.appLE,
    Category.assoc, X.presheaf.germ_res]

end
