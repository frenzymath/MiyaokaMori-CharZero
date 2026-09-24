import MiyaokaMori.Prelude

/-! # Dimension is the supremum over an open cover

The topological Krull dimension of a scheme is the supremum of the dimensions of the members of
any open cover.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem topologicalKrullDim_eq_iSup_openCover {X : AlgebraicGeometry.Scheme.{u}} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Z => ?_
    obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
    obtain ⟨y, hy⟩ := 𝒰.covers x
    have hf : Topology.IsOpenEmbedding (𝒰.f (𝒰.idx x)) :=
      (𝒰.f (𝒰.idx x)).isOpenEmbedding
    have hne : ((𝒰.f (𝒰.idx x)) ⁻¹' (Z : Set X)).Nonempty := ⟨y, by simpa [hy] using hx⟩
    have hZ : Z = IrreducibleCloseds.map (𝒰.f (𝒰.idx x)) hf.continuous
        ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hf).symm ⟨Z, hne⟩) :=
      congrArg Subtype.val
        ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hf).apply_symm_apply ⟨Z, hne⟩).symm
    rw [hZ, hf.coheight_map]
    exact (Order.coheight_le_krullDim _).trans
      (le_iSup (fun i => topologicalKrullDim (𝒰.X i)) (𝒰.idx x))
  · exact iSup_le fun i => (𝒰.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le

end
