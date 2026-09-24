import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qt

/-! # The fundamental cycle of a scheme

The `d`-dimensional fundamental cycle `[X]_d = Σ_Z length(O_{X,ξ_Z})·[Z]` of a locally Noetherian scheme
`X`, the sum running over the `d`-dimensional irreducible components `Z` of `X` with generic points `ξ_Z`
(Stacks 02QR); for `d = dim X` this is the fundamental cycle `[X]`. `X` need not be integral or reduced —
fibers and non-reduced closed subschemes occur; for `X` integral, `[X]` is the generic point with
multiplicity `1`. Its Chow class is `X.fundamentalChowClass d ∈ A_d(X)`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `d`-dimensional fundamental cycle `[X]_d = Σ_Z length(O_{X,ξ_Z})·[Z]`, `Z` running over the
`d`-dimensional irreducible components of `X` (Stacks 02QR); for `d = dim X` this is `[X]`. The
coefficients are `AlgebraicGeometry.Intersection.integralFundamentalMultiplicity` (the integer lift of
`length(O_{X,ξ})` at the generic point of a component, finite for `X` locally Noetherian), and the
dimension filter is `pointClosureDimension`. The underlying function is that of
`dimensionFundamentalCycle X d`, which requires `[IsNoetherian X]` (to prove finiteness of the support);
here only local Noetherianity is assumed and local finiteness is proved. -/
noncomputable def AlgebraicGeometry.Scheme.fundamentalCycle (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (d : ℕ) : AlgebraicGeometry.AlgebraicCycle X ℤ where
  toFun x := by
    classical
    exact if AlgebraicGeometry.Intersection.pointClosureDimension X x = d
      then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x else 0
  supportWithinDomain' := by simp
  -- local finiteness: the support is contained in `genericPoints X`; take an affine open neighbourhood `U`
  -- of `z` (locally Noetherian ⇒ `Γ(X,U)` Noetherian ⇒ `U` is a Noetherian space); `U` has finitely many
  -- irreducible components, and the generic points of components of `X` lying in `U` are generic points
  -- of components of `U` (an open immersion pulls back components)
  supportLocallyFiniteWithinDomain' z _ := by
    classical
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    have hopen : IsOpen (U : Set X) := U.2
    refine ⟨(U : Set X), hopen.mem_nhds hzU, ?_⟩
    have : IsNoetherianRing Γ(X, U) :=
      AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : TopologicalSpace.NoetherianSpace ↥(U : Set X) :=
      AlgebraicGeometry.noetherianSpace_of_isAffineOpen U hU
    have hfin : (genericPoints ↥(U : Set X)).Finite :=
      genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    refine (hfin.image (Subtype.val : ↥(U : Set X) → X)).subset ?_
    rintro y ⟨(hyU : y ∈ (U : Set X)), hy⟩
    rw [Function.mem_support] at hy
    have hgen : closure ({y} : Set X) ∈ irreducibleComponents X := by
      by_contra hcl
      exact hy (by
        simp [AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_of_not_generic X y hcl])
    have he : Topology.IsOpenEmbedding (Subtype.val : ↥(U : Set X) → X) :=
      hopen.isOpenEmbedding_subtypeVal
    refine ⟨(⟨y, hyU⟩ : ↥(U : Set X)), ?_, rfl⟩
    show closure ({(⟨y, hyU⟩ : ↥(U : Set X))} : Set ↥(U : Set X)) ∈
      irreducibleComponents ↥(U : Set X)
    rw [he.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hgen he
      ⟨y, subset_closure rfl, ⟨(⟨y, hyU⟩ : ↥(U : Set X)), rfl⟩⟩

/-- The Chow class `[X]_d ∈ A_d(X)` of the fundamental cycle. -/
noncomputable def AlgebraicGeometry.Scheme.fundamentalChowClass (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (d : ℕ) : AlgebraicGeometry.ChowGroup X d :=
  -- membership in `Z_d` follows from the dimension filter in the definition
  AlgebraicGeometry.ChowGroup.mk ⟨X.fundamentalCycle d,
    (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension _).mpr fun x hx => by
      by_contra h
      exact hx (if_neg h)⟩

open Classical in

/-- For `X` integral, locally Noetherian and **finite-dimensional**, `[X]_{dim X}` is the generic point with
multiplicity `1`.

The hypothesis `hdim : topologicalKrullDim X ≠ ⊤` cannot be dropped: for `A` Nagata's Noetherian domain
of infinite Krull dimension and `X = Spec A`, `X.dimension` falls back to `0` at `⊤`, while the generic
point `η` has `pointClosureDimension X η = ⊤ ≠ (0 : ℕ)`, so the left side is `0` at `η` and the right side
is `1`. Quasi-compact schemes locally of finite type over a field (in particular proper or projective
schemes over a field) satisfy the hypothesis. -/
theorem AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]
    (hdim : topologicalKrullDim X ≠ ⊤) :
    ⇑(X.fundamentalCycle X.dimension) = fun x => if x = genericPoint X then 1 else 0 := by
  funext x
  show (if AlgebraicGeometry.Intersection.pointClosureDimension X x = (X.dimension : ℕ)
      then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x else 0) = _
  have hgen : genericPoints X = {genericPoint X} := genericPoints_eq_singleton
  by_cases hx : x = genericPoint X
  · subst hx
    rw [if_pos rfl]
    -- dimension: `closure{η} = univ`, so `dim closure{η} = dim X = X.dimension`
    have hcl : closure ({genericPoint X} : Set X) = Set.univ :=
      genericPoint_spec X
    have hne : topologicalKrullDim X ≠ ⊥ := by
      unfold topologicalKrullDim
      have : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨Set.univ, (IrreducibleSpace.isIrreducible_univ X), isClosed_univ⟩⟩
      exact Order.krullDim_ne_bot_iff.mpr inferInstance
    have hd : AlgebraicGeometry.Intersection.pointClosureDimension X (genericPoint X)
        = (X.dimension : WithBot ℕ∞) := by
      rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure,
        hcl, ← X.dimension_spec hne hdim]
      exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
    rw [if_pos hd]
    -- multiplicity: the stalk at the generic point is a field, of length `1`
    have hmem : genericPoint X ∈ genericPoints X := by rw [hgen]; rfl
    have hlen : AlgebraicGeometry.Intersection.fundamentalMultiplicity X (genericPoint X) = 1 := by
      rw [AlgebraicGeometry.Intersection.fundamentalMultiplicity_of_generic X _ hmem]
      unfold AlgebraicGeometry.Intersection.stalkLength
      let _ : Field (X.presheaf.stalk (genericPoint X)) :=
        inferInstanceAs (Field X.functionField)
      exact Module.length_eq_one _ _
    unfold AlgebraicGeometry.Intersection.integralFundamentalMultiplicity
    simp [hlen]
  · rw [if_neg hx]
    have hnot : x ∉ genericPoints X := by rw [hgen]; exact hx
    rw [AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_of_not_generic X x hnot]
    simp

open Classical in

/-- Convenient form: an integral scheme separated and of finite type over a field `k` (in particular an
integral scheme proper or projective over `k`) is automatically finite-dimensional, so no `hdim` is
needed. -/
theorem AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral_of_isOfFiniteType {k : Type u}
    [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsSeparated (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsLocallyNoetherian X] :
    ⇑(X.fundamentalCycle X.dimension) = fun x => if x = genericPoint X then 1 else 0 :=
  X.fundamentalCycle_of_isIntegral
    (Variety.topologicalKrullDim_eq_trdeg (k := k) { carrier := X }).2

end
