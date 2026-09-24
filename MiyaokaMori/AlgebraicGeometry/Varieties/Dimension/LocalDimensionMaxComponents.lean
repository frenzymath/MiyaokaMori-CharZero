import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimensionOpenEmbedding
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.LocalDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00ot
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # Local dimension is the maximum over irreducible components

Stacks 0A21 (5): for a locally algebraic `k`-scheme, the local dimension at a point `x` is the
maximum of the dimensions of the irreducible components through `x`; in particular if
`dim_x Z ≥ 2` there is an irreducible component through `x` of dimension `≥ 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0A21 (3) applied to an irreducible closed subset `W` (with its reduced induced
structure): the dimension of `W` is at most the dimension of any open set meeting `W`. -/
private theorem topologicalKrullDim_irreducibleClosed_le_opens {k : Type u} [Field k]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (W : Set Z) (hWirr : IsIrreducible W) (hWcl : IsClosed W) (x : Z) (hxW : x ∈ W)
    (U : Z.Opens) (hxU : x ∈ U) :
    topologicalKrullDim W ≤ topologicalKrullDim U := by
  let I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (X := Z) ⟨W, hWcl⟩
  let Y : AlgebraicGeometry.Scheme.{u} := I.subscheme
  let ι : Y ⟶ Z := I.subschemeι
  have hrange : Set.range ι = W := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hemb : Topology.IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  let e : Y ≃ₜ W := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace W := Subtype.irreducibleSpace hWirr
  have : IrreducibleSpace Y := e.irreducibleSpace_iff.mpr inferInstance
  let _ : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨ι ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change AlgebraicGeometry.LocallyOfFiniteType
      (ι ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    infer_instance
  obtain ⟨y, hy⟩ : ∃ y : Y, ι y = x := by
    have : x ∈ Set.range ι := hrange ▸ hxW
    exact this
  let V : Y.Opens := ι ⁻¹ᵁ U
  have hyV : y ∈ V := by
    change ι y ∈ U
    rw [hy]
    exact hxU
  have h1 : topologicalKrullDim W = topologicalKrullDim Y :=
    (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm
  have h2 : topologicalKrullDim V = topologicalKrullDim Y :=
    AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) Y V ⟨y, hyV⟩
  have h3 : topologicalKrullDim V ≤ topologicalKrullDim U := by
    let g : V → U := fun v => ⟨ι v.1, v.2⟩
    have hg : Continuous g := (ι.continuous.comp continuous_subtype_val).subtype_mk _
    have hcomp : Topology.IsInducing ((Subtype.val : U → Z) ∘ g) :=
      hemb.isInducing.comp Topology.IsInducing.subtypeVal
    exact (Topology.IsInducing.of_comp hg continuous_subtype_val hcomp).topologicalKrullDim_le
  rw [h1, ← h2]
  exact h3

/-- Discreteness in `WithBot ℕ∞`: `(n : ℕ) < d ≤ n + 1` implies `d = n + 1`. -/
private theorem withBot_enat_eq_of_lt_of_le {d : WithBot ℕ∞} {n : ℕ}
    (h1 : ((n : ℕ∞) : WithBot ℕ∞) < d) (h2 : d ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    d = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  cases d with
  | bot => simp at h1
  | coe a =>
    have h1' : (n : ℕ∞) < a := WithBot.coe_lt_coe.mp h1
    have h2' : a ≤ ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h2
    congr 1
    refine le_antisymm h2' ?_
    have := Order.add_one_le_of_lt h1'
    simpa using this

/-- Stacks 0A21 (5): the local dimension at `x` is the maximum of the dimensions of the irreducible
components through `x`. -/
theorem localDimension_eq_max_components {k : Type u} [Field k]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] (x : Z) :
    ∃ W ∈ irreducibleComponents Z, x ∈ W ∧
      topologicalKrullDim W = (localDimension Z x : WithBot ℕ∞) ∧
      ∀ W' ∈ irreducibleComponents Z, x ∈ W' → topologicalKrullDim W' ≤ topologicalKrullDim W := by
  -- take an affine open neighbourhood `V = Spec A` of `x`, with `A` a finitely generated `k`-algebra
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV : AlgebraicGeometry.IsAffineOpen V := hV0
  let f := Z ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let φ : k →+* Γ(Z, V) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ V le_top).hom.FiniteType :=
      f.finiteType_appLE (AlgebraicGeometry.isAffineOpen_top _) hV _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(Z, V) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Z, V) := hφ
  have hopen : AlgebraicGeometry.IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let y : PrimeSpectrum Γ(Z, V) := hV.primeIdealOf ⟨x, hxV⟩
  have hy : hV.fromSpec y = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hinf := hV.fromSpec.isOpenEmbedding.iInf_topologicalKrullDim_opens_eq y
  rw [hy] at hinf
  obtain ⟨hOT1, hOT2⟩ := stacks_00OT (k := k) Γ(Z, V) y
  set I : WithBot ℕ∞ := ⨅ U ∈ {U : Z.Opens | x ∈ U}, topologicalKrullDim U with hI
  have hIeq : I = ⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum Γ(Z, V)) | y ∈ U},
      topologicalKrullDim U := hinf.symm
  -- (a) every component through `x` has dimension `≤ I`
  have ha : ∀ W ∈ irreducibleComponents Z, x ∈ W → topologicalKrullDim W ≤ I := by
    intro W hW hxW
    refine le_iInf₂ fun U hU => ?_
    exact topologicalKrullDim_irreducibleClosed_le_opens (k := k) Z W hW.1
      (isClosed_of_mem_irreducibleComponents W hW) x hxW U hU
  -- (b) `I ≤` the supremum of the dimensions of the components through `x`
  have hb : I ≤ ⨆ W ∈ {W ∈ irreducibleComponents Z | x ∈ W}, topologicalKrullDim W := by
    rw [hIeq, hOT1]
    refine iSup₂_le fun T hT => ?_
    obtain ⟨hTc, hyT⟩ := hT
    have himg : IsIrreducible (hV.fromSpec '' T) := hTc.1.image _ hV.fromSpec.continuous.continuousOn
    obtain ⟨W, hW, hTW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ himg
    have hxW : x ∈ W := hTW ⟨y, hyT, hy⟩
    refine le_trans ?_ (le_iSup₂ (f := fun (W : Set Z)
      (_ : W ∈ {W ∈ irreducibleComponents Z | x ∈ W}) => topologicalKrullDim W) W ⟨hW, hxW⟩)
    let g : T → W := fun t => ⟨hV.fromSpec t.1, hTW ⟨t.1, t.2, rfl⟩⟩
    have hg : Continuous g := (hV.fromSpec.continuous.comp continuous_subtype_val).subtype_mk _
    have hcomp : Topology.IsInducing ((Subtype.val : W → Z) ∘ g) :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    exact (Topology.IsInducing.of_comp hg continuous_subtype_val hcomp).topologicalKrullDim_le
  -- (c) `I` is finite: `I ≤ dim A_m` for a maximal ideal `m ∋ y`, and a Noetherian local ring has finite dimension
  have hNoeth : IsNoetherianRing Γ(Z, V) := Algebra.FiniteType.isNoetherianRing k Γ(Z, V)
  have htop : I ≠ ⊤ := by
    obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.2.ne_top
    have hle : I ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [hIeq, hOT2]
      exact iInf_le_of_le ⟨m, hm.isPrime⟩ (iInf_le_of_le hm (iInf_le_of_le hym le_rfl))
    intro h
    rw [h, top_le_iff] at hle
    exact ringKrullDim_lt_top.ne hle
  have hbot : I ≠ ⊥ := by
    intro h
    obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({x} : Set Z) isIrreducible_singleton
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim W := by
      have : Nonempty (IrreducibleCloseds W) :=
        ⟨⟨closure {⟨x, hxW rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    have := h0.trans (ha W hW (hxW rfl))
    rw [h] at this
    exact absurd this (by simp)
  -- I = localDimension
  have hloc : I = (localDimension Z x : WithBot ℕ∞) := by
    unfold localDimension
    rw [← hI]
    generalize I = J at hbot htop
    cases J with
    | bot => exact (hbot rfl).elim
    | coe a =>
      have ha' : a ≠ ⊤ := by
        rintro rfl
        exact htop rfl
      rw [WithBot.unbotD_coe]
      exact congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) (ENat.natCast_toNat ha').symm
  -- (d) the supremum is attained by some component
  obtain ⟨W, hW, hxW, hdim⟩ : ∃ W ∈ irreducibleComponents Z, x ∈ W ∧ topologicalKrullDim W = I := by
    rw [hloc] at hb ha ⊢
    generalize localDimension Z x = n at hb ha
    cases n with
    | zero =>
      obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        ({x} : Set Z) isIrreducible_singleton
      refine ⟨W, hW, hxW rfl, le_antisymm (ha W hW (hxW rfl)) ?_⟩
      have : Nonempty (IrreducibleCloseds W) :=
        ⟨⟨closure {⟨x, hxW rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    | succ n =>
      have hlt : (((n : ℕ) : ℕ∞) : WithBot ℕ∞) <
          ⨆ W ∈ {W ∈ irreducibleComponents Z | x ∈ W}, topologicalKrullDim W := by
        refine lt_of_lt_of_le ?_ hb
        exact_mod_cast Nat.lt_succ_self n
      obtain ⟨W, hlt'⟩ := lt_iSup_iff.mp hlt
      obtain ⟨hWmem, hlt''⟩ := lt_iSup_iff.mp hlt'
      exact ⟨W, hWmem.1, hWmem.2,
        withBot_enat_eq_of_lt_of_le hlt'' (ha W hWmem.1 hWmem.2)⟩
  refine ⟨W, hW, hxW, hdim.trans hloc, fun W' hW' hxW' => ?_⟩
  rw [hdim]
  exact ha W' hW' hxW'

end
