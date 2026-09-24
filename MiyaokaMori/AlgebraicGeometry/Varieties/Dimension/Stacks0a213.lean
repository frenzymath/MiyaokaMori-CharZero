import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.AffineOpenDimEqClosedPointStalkDim

/-! # Nonempty opens of an irreducible locally algebraic scheme have full dimension (Stacks 0A21 (3))

Stacks 0A21 (3): if `X` is an irreducible scheme locally of finite type over a field `k` (not
necessarily separated or reduced), every nonempty open subset of `X` has dimension `dim X`, and
the local dimension (infimum of the dimensions of the open neighbourhoods) at every point is
`dim X`. The version for varieties is `Variety.localDimension_eq_dim`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every nonempty open of an irreducible scheme locally of finite type over a field has the
dimension of the whole scheme. -/
theorem AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IrreducibleSpace X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    topologicalKrullDim U = topologicalKrullDim X := by
  have hJ : JacobsonSpace X :=
    LocallyOfFiniteType.jacobsonSpace (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- any two nonempty affine opens have the same dimension
  have hsame : ∀ V W : X.affineOpens, (V.1 : Set X).Nonempty → (W.1 : Set X).Nonempty →
      topologicalKrullDim V.1 = topologicalKrullDim W.1 := by
    intro V W hVne hWne
    have hne : ((V.1 : Set X) ∩ (W.1 : Set X)).Nonempty :=
      nonempty_preirreducible_inter V.1.2 W.1.2 hVne hWne
    obtain ⟨z, ⟨hzV, hzW⟩, hz⟩ :=
      nonempty_inter_closedPoints hne (V.1.2.inter W.1.2).isLocallyClosed
    rw [AlgebraicGeometry.topologicalKrullDim_affineOpen_eq_ringKrullDim_stalk_of_isClosed
        (k := k) X V.1 V.2 z hzV hz,
      AlgebraicGeometry.topologicalKrullDim_affineOpen_eq_ringKrullDim_stalk_of_isClosed
        (k := k) X W.1 W.2 z hzW hz]
  -- `U` contains a nonempty affine open `V₀`
  obtain ⟨x, hxU⟩ := hU
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hle1 : topologicalKrullDim V₀ ≤ topologicalKrullDim U :=
    (Topology.IsEmbedding.inclusion hV₀U).isInducing.topologicalKrullDim_le
  have hle2 : topologicalKrullDim U ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X U
  have hcov : topologicalKrullDim X = ⨆ V : X.affineOpens, topologicalKrullDim V.1 :=
    topologicalKrullDim_eq_iSup_openCover
      (X.openCoverOfIsOpenCover (fun V : X.affineOpens => V.1) (AlgebraicGeometry.iSup_affineOpens_eq_top X))
  have hle3 : topologicalKrullDim X ≤ topologicalKrullDim V₀ := by
    rw [hcov]
    refine iSup_le fun V => ?_
    by_cases hV : (V.1 : Set X).Nonempty
    · exact (hsame V ⟨V₀, hV₀⟩ hV ⟨x, hxV₀⟩).le
    · have : IsEmpty V.1 := by
        rw [Set.not_nonempty_iff_eq_empty] at hV
        exact Set.isEmpty_coe_sort.mpr hV
      have : IsEmpty (IrreducibleCloseds V.1) :=
        ⟨fun s => this.elim s.isIrreducible'.nonempty.some⟩
      rw [topologicalKrullDim, Order.krullDim_eq_bot]
      exact bot_le
  exact le_antisymm hle2 (hle3.trans hle1)

/-- The (untruncated) local dimension at any point of an irreducible scheme locally of finite type
over a field equals the dimension of the whole scheme. -/
theorem AlgebraicGeometry.iInf_topologicalKrullDim_opens_eq_of_irreducible {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IrreducibleSpace X] (x : X) :
    (⨅ U ∈ {U : X.Opens | x ∈ U}, topologicalKrullDim U) = topologicalKrullDim X := by
  refine le_antisymm (iInf₂_le ⊤ trivial |>.trans_eq ?_) (le_iInf₂ fun U hU => ?_)
  · exact AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X ⊤ ⟨x, trivial⟩
  · exact (AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X U ⟨x, hU⟩).ge

end
