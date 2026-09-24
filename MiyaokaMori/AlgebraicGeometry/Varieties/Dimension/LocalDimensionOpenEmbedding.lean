import MiyaokaMori.Prelude

/-! # Local dimension along an open embedding

If `f : Y → X` is an open embedding of topological spaces and `y ∈ Y`, then the local dimension
of `Y` at `y` (the infimum of the Krull dimensions of the open neighbourhoods of `y`, in
`WithBot ℕ∞`, untruncated) equals the local dimension of `X` at `f(y)`.

Proof sketch:
1. (`≤`) For an open `U ∋ f(y)` in `X`, `V := f⁻¹(U)` is an open neighbourhood of `y`; the
   restriction `V → U` is inducing (`Topology.IsInducing.of_comp`), so `dim V ≤ dim U`
   (`Topology.IsInducing.topologicalKrullDim_le`).
2. (`≥`) For an open `V ∋ y` in `Y`, `U := f(V)` is an open neighbourhood of `f(y)` (an open
   embedding is an open map); `V ≃ₜ f(V)` (`Topology.IsEmbedding.homeomorphImage`) and
   homeomorphisms preserve Krull dimension (`IsHomeomorph.topologicalKrullDim_eq`), so
   `dim U = dim V`.
3. The two inequalities give equality of the infima.

This is the step "the local dimension depends only on an open neighbourhood, so one may pass to
an affine open" in the proofs of Stacks 0A21 / 02FX and Debarre 6.11.
-/

set_option autoImplicit false

open TopologicalSpace

theorem Topology.IsOpenEmbedding.iInf_topologicalKrullDim_opens_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    (y : Y) :
    (⨅ V ∈ {V : Opens Y | y ∈ V}, topologicalKrullDim V) =
      ⨅ U ∈ {U : Opens X | f y ∈ U}, topologicalKrullDim U := by
  apply le_antisymm
  · refine le_iInf₂ fun U hU => ?_
    let V : Opens Y := ⟨f ⁻¹' (U : Set X), U.2.preimage hf.continuous⟩
    refine (iInf₂_le V (show y ∈ V from hU)).trans ?_
    let g : V → U := fun v => ⟨f v.1, v.2⟩
    have hg : Continuous g := (hf.continuous.comp continuous_subtype_val).subtype_mk _
    have hcomp : Topology.IsInducing ((Subtype.val : U → X) ∘ g) :=
      hf.isInducing.comp Topology.IsInducing.subtypeVal
    exact (Topology.IsInducing.of_comp hg continuous_subtype_val hcomp).topologicalKrullDim_le
  · refine le_iInf₂ fun V hV => ?_
    let U : Opens X := ⟨f '' (V : Set Y), hf.isOpenMap _ V.2⟩
    refine (iInf₂_le U (show f y ∈ U from ⟨y, hV, rfl⟩)).trans ?_
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (hf.isEmbedding.homeomorphImage (V : Set Y)).isHomeomorph).ge
