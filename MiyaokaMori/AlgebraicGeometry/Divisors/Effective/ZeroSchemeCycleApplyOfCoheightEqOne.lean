import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.SubschemeStalkKer
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleApply
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.SectionGermGeneratorOffZeroLocus
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero
import MiyaokaMori.AlgebraicGeometry.Modules.SectionSupportComplNonvanishingLocus

/-! # The zero-scheme cycle at a point of coheight one

At a point `z` of coheight `1`, the coefficient of the zero-scheme cycle `[Z(σ)]_d` of a nonzero
section `σ` of a line bundle equals `ord_z(σ)`. Sources: the proof of Stacks 02SQ; Stacks 02QU, 02RV.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- A point of a scheme that is maximal for the specialization order (`Order.coheight = 0`) is the
generic point of an irreducible component.
Proof: `irreducibleComponent z′` is an irreducible closed set; take its generic point `w′`
(quasi-sobriety); `z′ ∈ closure {w′}` means `w′ ⤳ z′`, maximality gives `z′ ⤳ w′`, and `T₀` gives
`w′ = z′`, so `closure {z′} = irreducibleComponent z′` is an irreducible component. -/
theorem mem_genericPoints_of_isMax (Z : AlgebraicGeometry.Scheme.{u}) {z' : Z} (h : IsMax z') :
    z' ∈ genericPoints Z := by
  show closure ({z'} : Set Z) ∈ irreducibleComponents Z
  obtain ⟨w', hw'⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z'))
    isClosed_irreducibleComponent
  have hmem : z' ∈ closure ({w'} : Set Z) := by
    rw [hw'.def]; exact mem_irreducibleComponent
  have hle : z' ≤ w' := AlgebraicGeometry.Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr hmem)
  have heq : w' = z' :=
    ((AlgebraicGeometry.Scheme.le_iff_specializes.mp (h hle)).antisymm
      (AlgebraicGeometry.Scheme.le_iff_specializes.mp hle)).eq.symm
  rw [← heq, hw'.def]
  exact irreducibleComponent_mem_irreducibleComponents z'

/-- Let `X` be integral, `ι : Z → X` a closed immersion, `z′ ∈ Z` with `coheight(ι z′) = 1`, and assume
the generic point `η ∉ ι(Z)`. Then `z′` is maximal in `Z`.
Proof: if `z′ < w′` then `ι z′ < ι w′` and `coheight(ι w′) + 1 ≤ coheight(ι z′) = 1`, so `ι w′` is
maximal; `η ⤳ ι w′` means `ι w′ ≤ η`, and maximality gives `ι w′ = η ∈ ι(Z)`, a contradiction. -/
theorem isMax_of_coheight_eq_one_of_notMem_range {Z X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (ι : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι] {z' : Z}
    (hz : Order.coheight (ι.base z') = 1) (hη : genericPoint X ∉ Set.range ι.base) : IsMax z' := by
  intro w' hw'
  by_contra hne
  have hlt : z' < w' := lt_of_le_not_ge hw' hne
  have hlt' : ι.base z' < ι.base w' := (ι.lt_iff_of_isClosedImmersion _ _).mpr hlt
  have h1 := Order.coheight_add_one_le hlt'
  rw [hz] at h1
  have h0 : Order.coheight (ι.base w') = 0 := by
    have hnt : Order.coheight (ι.base w') ≠ ⊤ := by
      intro ht
      rw [ht, top_add] at h1
      simp at h1
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnt
    rw [← hm] at h1 ⊢
    norm_cast at h1 ⊢
    omega
  have hmax : IsMax (ι.base w') := Order.coheight_eq_zero.mp h0
  have hle : ι.base w' ≤ genericPoint X :=
    AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes _)
  exact hη ⟨w', ((AlgebraicGeometry.Scheme.le_iff_specializes.mp (hmax hle)).antisymm
    (AlgebraicGeometry.Scheme.le_iff_specializes.mp hle)).eq⟩

/-- If the germ of `σ` at the generic point is nonzero then `η ∉ supp Z(σ)` (the stalk at `η` is a field,
`𝔪_η = 0`). -/
theorem genericPoint_notMem_idealSheafOfSection_support {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] (L : X.Modules) [L.IsLineBundle]
    (σ : (L.val.obj (Opposite.op ⊤) : Type u))
    (hση : L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ) ≠ 0) :
    genericPoint X ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection L σ).support := by
  rw [mem_idealSheafOfSection_support_iff]
  intro hmem
  let _ : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  rw [IsLocalRing.maximalIdeal_eq_bot, Submodule.bot_smul] at hmem
  exact hση ((Submodule.mem_bot _).mp hmem)

/-- The `Ring.ord` of an element `f` of the local ring (`= length(A/fA)`) agrees with the `Scheme.ord` of
its image in the function field (Stacks 02QU, 02RV). -/
theorem ord_algebraMap_eq_of_ord_eq {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    [AlgebraicGeometry.IsLocallyNoetherian W] (z : W) (hz : Order.coheight z = 1)
    {f : W.presheaf.stalk z} (hf : f ≠ 0) {n : ℕ} (hn : Ring.ord (W.presheaf.stalk z) f = n) :
    W.ord (algebraMap (W.presheaf.stalk z) W.functionField f) z = n := by
  have : Ring.KrullDimLE 1 (W.presheaf.stalk z) := AlgebraicGeometry.krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (W.presheaf.stalk z) W.functionField f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hf
  apply (AlgebraicGeometry.Scheme.ord_eq_iff hz hne).2
  change Ring.ordFrac (W.presheaf.stalk z) _ = _
  rw [Ring.ordFrac_eq_ord _ hf]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hf) hn

end AlgebraicGeometry.Scheme

/-- At a point `z` of coheight `1`, the coefficient of `[Z(σ)]_d` equals `ord_z(σ)`.

Sources: the proof of Stacks 02SQ (Stacks 02OQ: the ideal of `Z(σ)` at `z` is `(f)`); Stacks 02QU, 02RV
(the definition `ord_A(f) = length_A(A/fA)`).
Proof: let `A := O_{X,z}`. Take an affine open `W` near `z` with a frame `e`, `σ|_W = c·e`,
`f := germ_z c`, so `σ_z = f·e_z` and `f ≠ 0` (otherwise `σ_η = 0`).
Right side: `rationalSectionOrd_eq_ord_of_generator` gives `ord_z(σ_η) = X.ord (image of f) z
= Ring.ord_A(f) = length(A/fA)` (`ord_algebraMap_eq_of_ord_eq`).
Left side: if `z ∉ Z` both sides are `0` (`IdealSheafData.cycle_apply_of_notMem_support`,
`rationalSectionOrd_germ_eq_zero_of_notMem_support`); otherwise `z = ι z′` and the coefficient of `[Z]_d`
at `z` is the coefficient of `[Z]_d^Z` at `z′` (`IdealSheafData.cycle_apply_subschemeι`). Dimension
filter: `pointClosureDimension Z z′ = height z′ = height z = d` (`Scheme.height_eq_of_coheight_eq_one`).
`z′` is the generic point of a component of `Z` (`isMax_of_coheight_eq_one_of_notMem_range`,
`mem_genericPoints_of_isMax`, using `η ∉ Z(σ)`), and the multiplicity is
`length_{O_{Z,z′}} O_{Z,z′} = length_A O_{Z,z′}` (`closedSubschemeStalkLength_eq`) `= length_A(A/I_z)`
(`closedSubschemeStalkLength_subschemeι_eq`), with `I_z = I(W)·A = (f)`
(`idealSheafOfSection_ideal_eq_span_coord`). -/
theorem AlgebraicGeometry.Scheme.idealSheafOfSection_cycle_apply_of_coheight_eq_one
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (Opposite.op ⊤) : Type u)) (hσ : σ ≠ 0)
    (d : ℕ) (hX : X.dimension = d + 1) (z : X) (hz : Order.coheight z = 1) :
    (AlgebraicGeometry.Scheme.idealSheafOfSection L σ).cycle d z =
      L.rationalSectionOrd
        (L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ)) z := by
  classical
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection L σ with hI
  have hση : L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ) ≠ 0 :=
    AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero L σ hσ
  by_cases hzZ : z ∈ I.support
  swap
  · rw [I.cycle_apply_of_notMem_support d hzZ,
      AlgebraicGeometry.Scheme.rationalSectionOrd_germ_eq_zero_of_notMem_support L σ hzZ]
  have hzZ' : z ∈ Set.range I.subschemeι.base := by
    rw [I.range_subschemeι]; exact hzZ
  obtain ⟨z', rfl⟩ := hzZ'
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  rw [I.cycle_apply_subschemeι d z']
  -- frame and local equation
  obtain ⟨W, hW, -, hzW, e, hf⟩ := AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L
    (U := ⊤) (p := I.subschemeι.base z') trivial
  set σW : Γ(L, W) := L.res (le_top : W ≤ ⊤) (show Γ(L, ⊤) from σ) with hσW
  set c := hf.coord le_rfl σW with hcdef
  have hc : c • L.res le_rfl e = σW := hf.coord_smul_frame le_rfl σW
  have hIW : I.ideal ⟨W, hW⟩ = Ideal.span {c} :=
    AlgebraicGeometry.Scheme.idealSheafOfSection_ideal_eq_span_coord L σ hW hf
  set f := X.presheaf.germ W (I.subschemeι.base z') hzW c with hfdef
  set ez := L.presheaf.germ W (I.subschemeι.base z') hzW e with hezdef
  have hez := hf.span_germ_eq_top hzW
  have hgerm : L.presheaf.germ ⊤ (I.subschemeι.base z') trivial (show Γ(L, ⊤) from σ) = f • ez := by
    have h1 : L.presheaf.germ ⊤ (I.subschemeι.base z') trivial (show Γ(L, ⊤) from σ) =
        L.presheaf.germ W (I.subschemeι.base z') hzW σW :=
      (TopCat.Presheaf.germ_res_apply L.presheaf (CategoryTheory.homOfLE (le_top : W ≤ ⊤)) _ hzW
        _).symm
    rw [h1, ← hc, AlgebraicGeometry.Scheme.Modules.germ_smul',
      AlgebraicGeometry.Scheme.Modules.res_self]
  have hj := AlgebraicGeometry.Scheme.moduleStalkToGenericFiber_germ_top L σ (I.subschemeι.base z')
  have hf0 : f ≠ 0 := by
    intro h0
    apply hση
    rw [← hj, hgerm, h0, zero_smul, map_zero]
  -- right side
  have hRHS : L.rationalSectionOrd (L.presheaf.germ ⊤ (genericPoint X) trivial (show Γ(L, ⊤) from σ))
      (I.subschemeι.base z') =
      X.ord (algebraMap (X.presheaf.stalk (I.subschemeι.base z')) X.functionField f)
        (I.subschemeι.base z') := by
    refine AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_ord_of_generator L _ ez hez _ _
      hση ?_
    rw [← hj, hgerm, map_smulₛₗ]
  rw [hRHS]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (I.subschemeι.base z')) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hz.le
  have hord_ne : Ring.ord (X.presheaf.stalk (I.subschemeι.base z')) f ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hf0)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Ring.ord (X.presheaf.stalk (I.subschemeι.base z')) f = n :=
    ⟨_, (ENat.natCast_toNat_eq_self.mpr hord_ne).symm⟩
  rw [AlgebraicGeometry.Scheme.ord_algebraMap_eq_of_ord_eq _ hz hf0 hn]
  -- left side: dimension filter
  have hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    have hne : topologicalKrullDim X ≠ ⊥ := by
      unfold topologicalKrullDim
      have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
        ⟨⟨Set.univ, (IrreducibleSpace.isIrreducible_univ X), isClosed_univ⟩⟩
      exact Order.krullDim_ne_bot_iff.mpr inferInstance
    have hnt : topologicalKrullDim X ≠ ⊤ := by
      intro h
      unfold AlgebraicGeometry.Scheme.dimension at hX
      rw [h] at hX
      have : (WithBot.unbotD 0 (⊤ : WithBot ℕ∞)).toNat = 0 := by
        show (⊤ : ℕ∞).toNat = 0
        exact ENat.toNat_top
      omega
    rw [X.dimension_spec hne hnt, hX]
  have hht : Order.height (I.subschemeι.base z') = (d : ℕ∞) :=
    AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) hdim hz
  have hpcd : AlgebraicGeometry.Intersection.pointClosureDimension I.subscheme z' = (d : WithBot ℕ∞) := by
    rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height,
      ← I.subschemeι.height_of_isClosedImmersion z', hht]
    rfl
  -- z′ is the generic point of a component
  have hη : genericPoint X ∉ Set.range I.subschemeι.base := by
    rw [I.range_subschemeι]
    exact AlgebraicGeometry.Scheme.genericPoint_notMem_idealSheafOfSection_support L σ hση
  have hgen : z' ∈ genericPoints I.subscheme :=
    AlgebraicGeometry.Scheme.mem_genericPoints_of_isMax _
      (AlgebraicGeometry.Scheme.isMax_of_coheight_eq_one_of_notMem_range I.subschemeι hz hη)
  -- multiplicity
  have hmult : AlgebraicGeometry.Intersection.fundamentalMultiplicity I.subscheme z' = (n : ℕ∞) := by
    rw [AlgebraicGeometry.Intersection.fundamentalMultiplicity_of_generic _ _ hgen,
      ← AlgebraicGeometry.Intersection.closedSubschemeStalkLength_eq I.subschemeι z',
      I.closedSubschemeStalkLength_subschemeι_eq ⟨W, hW⟩ z' hzW, hIW, Ideal.map_span,
      Set.image_singleton]
    exact hn
  show (if AlgebraicGeometry.Intersection.pointClosureDimension I.subscheme z' = (d : WithBot ℕ∞)
    then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity I.subscheme z' else 0) = (n : ℤ)
  rw [if_pos hpcd]
  have h1 := AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_toNat I.subscheme z'
  rw [hmult] at h1
  have h2 : (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity I.subscheme z').toNat = n :=
    Nat.cast_injective h1
  rw [← h2, Int.toNat_of_nonneg (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_nonneg _ _)]

end
