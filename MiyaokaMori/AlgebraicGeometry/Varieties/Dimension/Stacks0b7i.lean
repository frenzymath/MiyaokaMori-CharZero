import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension

/-! # Dimension is the supremum of the local dimensions (Stacks 0B7I)

Stacks 0B7I: the dimension of a topological space is the supremum of the local dimensions at its
points, `dim X = sup_x dim_x X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0B7I: `dim X = ⨆ x, dim_x X`. -/
theorem topologicalKrullDim_eq_iSup_localDimension (X : AlgebraicGeometry.Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ⨅ (U : X.Opens) (_ : x ∈ U), topologicalKrullDim U := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    have hlocal : ∀ (U : X.Opens), x ∈ U →
        (Order.coheight Z : WithBot ℕ∞) ≤ topologicalKrullDim U := by
      intro U hxU
      let fU : ↥(U : Set X) → X := fun y => y.1
      have hne : (fU ⁻¹' (Z : Set X)).Nonempty :=
        ⟨⟨x, hxU⟩, hx⟩
      let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
        fU U.2.isOpenEmbedding_subtypeVal
      let zU : IrreducibleCloseds ↥(U : Set X) := e.symm ⟨Z, hne⟩
      have hmap : IrreducibleCloseds.map fU U.2.isOpenEmbedding_subtypeVal.continuous zU = Z := by
        change (e zU : IrreducibleCloseds X) = Z
        exact congrArg Subtype.val (e.apply_symm_apply ⟨Z, hne⟩)
      have hco := U.2.isOpenEmbedding_subtypeVal.coheight_map zU
      change Order.coheight (IrreducibleCloseds.map fU U.2.isOpenEmbedding_subtypeVal.continuous zU) =
        Order.coheight zU at hco
      rw [hmap] at hco
      rw [hco]
      exact Order.coheight_le_krullDim _
    have hinf : (Order.coheight Z : WithBot ℕ∞) ≤
        ⨅ (U : X.Opens) (_ : x ∈ U), topologicalKrullDim U :=
      le_iInf fun U => le_iInf fun hxU => hlocal U hxU
    exact hinf.trans (le_iSup (fun x : X => ⨅ (U : X.Opens) (_ : x ∈ U), topologicalKrullDim U) x)
  · refine iSup_le fun x => ?_
    refine (iInf₂_le (⊤ : X.Opens) (show x ∈ (⊤ : X.Opens) from trivial)).trans ?_
    exact Topology.IsInducing.subtypeVal.topologicalKrullDim_le

end
