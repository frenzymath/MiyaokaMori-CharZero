import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal

/-! # The stalk ideal computed on any affine open

The stalk ideal can be computed on any affine open `U` containing `x`: `I_x = I(U)·O_{X,x}`.

References: Stacks 01QZ; Hartshorne II Prop 5.2(b) (a quasi-coherent sheaf on an affine open is
the localization of its global sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `I_x = I(U)·O_{X,x}` for any affine open `U` containing `x`.

Proof sketch: `≥` is `le_iSup₂`. For `≤`, given another affine open `V ∋ x`, choose an affine
open `W ∋ x` inside `U ⊓ V`; by `I.map_ideal'` the ideals `I(U)` and `I(V)` both restrict to
`I(W)`, and germs commute with restriction (`germ_res`), so `I(V)·O_x = I(W)·O_x = I(U)·O_x`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hx : x ∈ U.1) :
    I.stalkIdeal x = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  apply le_antisymm
  · refine iSup₂_le fun V hxV => ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (U.1 ⊓ V.1 : X.Opens) from ⟨hx, hxV⟩) (U.1 ⊓ V.1).isOpen
    have hWU : W ≤ U.1 := fun y hy => (hWle hy).1
    have hWV : W ≤ V.1 := fun y hy => (hWle hy).2
    have e1 := I.map_ideal' (U := ⟨W, hW⟩) (V := U) (homOfLE hWU).op
    have e2 := I.map_ideal' (U := ⟨W, hW⟩) (V := V) (homOfLE hWV).op
    have r1 : X.presheaf.map (homOfLE hWU).op ≫ X.presheaf.germ W x hxW =
        X.presheaf.germ U.1 x hx := X.presheaf.germ_res (homOfLE hWU) x hxW
    have r2 : X.presheaf.map (homOfLE hWV).op ≫ X.presheaf.germ W x hxW =
        X.presheaf.germ V.1 x hxV := X.presheaf.germ_res (homOfLE hWV) x hxW
    refine le_of_eq ?_
    calc (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom
        = ((I.ideal V).map (X.presheaf.map (homOfLE hWV).op).hom).map
            (X.presheaf.germ W x hxW).hom := by
          rw [Ideal.map_map, ← CommRingCat.hom_comp, r2]
      _ = (I.ideal ⟨W, hW⟩).map (X.presheaf.germ W x hxW).hom := by rw [e2]
      _ = ((I.ideal U).map (X.presheaf.map (homOfLE hWU).op).hom).map
            (X.presheaf.germ W x hxW).hom := by rw [e1]
      _ = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
          rw [Ideal.map_map, ← CommRingCat.hom_comp, r1]
  · exact le_iSup₂ (f := fun (V : X.affineOpens) (hxV : x ∈ V.1) =>
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom) U hx

end
