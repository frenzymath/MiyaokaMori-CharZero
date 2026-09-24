import MiyaokaMori.Prelude

/-! # Flat pullback of cycles

The flat pullback `f^* : Z(Y) → Z(X)` at the level of cycles (Stacks 02RB): the coefficient at `x` is the
multiplicity `length(O_{X,x}/m_{f x}O_{X,x})` of `[f⁻¹(closure{f x})]` at `closure{x}` times `α(f x)`, taking
only the points with `height x = height f(x) + r` (relative dimension `r`). The statements of 02RG, 0EPJ and
02RH use this `flatPullbackCycle`.

Source: Stacks 02RB, 02R9 (with 02R5/02RM/02RH/02RT/02S2). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Relative dimension `r` (Stacks 02NJ): every irreducible component of every fiber (the points of coheight
`0` in the fiber) has dimension `r`; no condition for empty fibers. -/
def AlgebraicGeometry.Scheme.Hom.HasRelativeDimension {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) (r : ℕ) : Prop :=
  ∀ (x : X) (z : π.fiber x), Order.coheight z = 0 → Order.height z = (r : ℕ∞)

/-- The coefficient function of the pullback of cycles (Stacks 02RB): when `y` is the generic point of an
irreducible component of its fiber `Y_{π y}` (`π.asFiber y` has coheight `0`) and
`height y = height (π y) + r`, the value is `α(π y)·length O_{Y_{π y}, y}`, otherwise `0`. -/
noncomputable def AlgebraicGeometry.flatPullbackCoeff {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) (r : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (y : Y) : ℤ := by
  classical
  exact if Order.coheight (π.asFiber y) = 0 ∧ Order.height y = Order.height (π.base y) + r then
      α (π.base y) * ((Module.length ((π.fiber (π.base y)).presheaf.stalk (π.asFiber y))
        ((π.fiber (π.base y)).presheaf.stalk (π.asFiber y))).toNat : ℤ)
    else 0

/-- The flat pullback of cycles (Stacks 02RB): the cycle with coefficient function `flatPullbackCoeff` when
its support is locally finite; the junk value `0` otherwise (which does not happen for `π` locally of finite
type and `X` locally Noetherian, Stacks 02R9). -/
noncomputable def AlgebraicGeometry.flatPullbackCycle {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) (r : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle Y ℤ := by
  classical
  exact if h : ∀ z ∈ (Set.univ : Set Y), ∃ t ∈ nhds z,
      (t ∩ Function.support (AlgebraicGeometry.flatPullbackCoeff π r α)).Finite then
    { toFun := AlgebraicGeometry.flatPullbackCoeff π r α
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := h }
  else 0

/-- Topological lemma (the core of step 3 of the argument of Stacks 02R9): let `α` be a T0 quasi-sober space
and `K ⊆ α` an open set which is a Noetherian space as a subspace. Then `K` has only finitely many points that
are maximal for specialization (`∀ z', z' ⤳ z → z ⤳ z'`, i.e. no proper generization).

Proof: such a `z` is still maximal in the subspace `K` (specialization in the subspace is specialization in
the whole space, `IsInducing.subtypeVal`). Take the irreducible component `C` containing `z`
(`irreducibleComponent`); its generic point `g` (`K` is quasi-sober, as an open subset) satisfies `g ⤳ z`;
maximality gives `z ⤳ g`, T0 gives `z = g`, so `closure{z} = C` is an irreducible component and
`z ∈ genericPoints K`. A Noetherian space has finitely many irreducible components
(`NoetherianSpace.finite_irreducibleComponents`), and under T0 generic points correspond bijectively to
components (`genericPoints.finite`). -/
theorem finite_specializationMax_of_isOpen_noetherianSpace {α : Type*} [TopologicalSpace α]
    [T0Space α] [QuasiSober α] {K : Set α} (hK : IsOpen K) [NoetherianSpace K] :
    {z : α | z ∈ K ∧ ∀ z', z' ⤳ z → z ⤳ z'}.Finite := by
  have : QuasiSober K := hK.isOpenEmbedding_subtypeVal.quasiSober
  have hfin : (genericPoints K).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  refine (hfin.image Subtype.val).subset ?_
  rintro z ⟨hzK, hz⟩
  refine ⟨⟨z, hzK⟩, ?_, rfl⟩
  set w : K := ⟨z, hzK⟩
  have hC := irreducibleComponent_mem_irreducibleComponents w
  have hg := (isIrreducible_irreducibleComponent (x := w)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  set g := (isIrreducible_irreducibleComponent (x := w)).genericPoint
  have h1 : g ⤳ w := hg.specializes mem_irreducibleComponent
  have h2 : w ⤳ g :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (hz g.1 (h1.map continuous_subtype_val))
  have hwg : w = g := (h2.antisymm h1).eq
  show closure {w} ∈ irreducibleComponents K
  rw [hwg, show closure {g} = irreducibleComponent w from hg]
  exact hC

/-- A quasi-compact open subset of a locally Noetherian scheme is a Noetherian subspace (standard, cf.
Stacks 01OX).

Proof: a quasi-compact open is a finite union of affine opens
(`isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens`); the coordinate ring of each affine open is
Noetherian (`IsLocallyNoetherian.component_noetherian`), so its underlying space is Noetherian
(`noetherianSpace_of_isAffineOpen`); by `noetherianSpace_set_iff`, any subset `t` of `K` is the finite union
of the `t ∩ Uᵢ`, each quasi-compact. -/
theorem AlgebraicGeometry.noetherianSpace_of_isCompact_of_isOpen {F : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian F] {K : Set F} (hK : IsCompact K) (hKo : IsOpen K) :
    NoetherianSpace K := by
  obtain ⟨s, hs, rfl⟩ :=
    AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hK, hKo⟩
  rw [noetherianSpace_set_iff]
  intro t ht
  rw [← Set.inter_eq_left.mpr ht, Set.inter_iUnion₂]
  refine hs.isCompact_biUnion fun i _ => ?_
  have := AlgebraicGeometry.IsLocallyNoetherian.component_noetherian i
  exact (noetherianSpace_set_iff _).mp (AlgebraicGeometry.noetherianSpace_of_isAffineOpen i.1 i.2) _
    Set.inter_subset_right

/-- `Spec κ(x) → X` is quasi-compact: the source is a one-point space, so every subset is quasi-compact. -/
theorem AlgebraicGeometry.quasiCompact_fromSpecResidueField (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    AlgebraicGeometry.QuasiCompact (X.fromSpecResidueField x) := by
  refine ⟨fun U _ _ => ?_⟩
  have : Subsingleton (AlgebraicGeometry.Spec (X.residueField x)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x)))
  exact Set.subsingleton_of_subsingleton.isCompact

set_option backward.isDefEq.respectTransparency.types false in
/-- The fiber embedding `π.fiberι x : π.fiber x ⟶ Y` is quasi-compact: it is the base change of
`Spec κ(x) → X`, and quasi-compactness is stable under base change. -/
theorem AlgebraicGeometry.quasiCompact_fiberι {X Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X) (x : X) :
    AlgebraicGeometry.QuasiCompact (π.fiberι x) :=
  MorphismProperty.pullback_fst _ _ (AlgebraicGeometry.quasiCompact_fromSpecResidueField X x)

/-- Step 3 of the argument of Stacks 02R9: `π` locally of finite type, `X` locally Noetherian, `V ⊆ Y`
quasi-compact open, `x ∈ X`. Then only finitely many points of `V` lie in the fiber `π⁻¹(x)` and are maximal
in the fiber `π.fiber x` (`IsMax (π.asFiber y)`, i.e. generic points of irreducible components of the fiber).

Proof: the fiber `F = π.fiber x` is locally Noetherian (base change of `π` locally of finite type, and
`Spec κ(x)` is Noetherian); `π.fiberι x` is quasi-compact (`quasiCompact_fiberι`), so `K = fiberι⁻¹(V)` is a
quasi-compact open of `F`, hence a Noetherian subspace (`noetherianSpace_of_isCompact_of_isOpen`). The set in
question is the image of the specialization-maximal points of `K` (`range_fiberι`, `fiberι_asFiber` and the
injectivity of `fiberι` match `y` with `π.asFiber y`), which is finite
(`finite_specializationMax_of_isOpen_noetherianSpace`). -/
theorem AlgebraicGeometry.finite_isMax_asFiber_of_isCompact {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) [AlgebraicGeometry.LocallyOfFiniteType π] [AlgebraicGeometry.IsLocallyNoetherian X]
    (x : X) {V : Set Y} (hV : IsCompact V) (hVo : IsOpen V) :
    {y : Y | y ∈ V ∧ π.base y = x ∧ IsMax (π.asFiber y)}.Finite := by
  have : AlgebraicGeometry.IsLocallyNoetherian (π.fiber x) := by
    unfold AlgebraicGeometry.Scheme.Hom.fiber; infer_instance
  have : AlgebraicGeometry.QuasiCompact (π.fiberι x) := AlgebraicGeometry.quasiCompact_fiberι π x
  have hKo : IsOpen ((π.fiberι x).base ⁻¹' V) := hVo.preimage (π.fiberι x).continuous
  have hKc : IsCompact ((π.fiberι x).base ⁻¹' V) :=
    AlgebraicGeometry.QuasiCompact.isCompact_preimage V hVo hV
  have : NoetherianSpace ((π.fiberι x).base ⁻¹' V) :=
    AlgebraicGeometry.noetherianSpace_of_isCompact_of_isOpen hKc hKo
  refine ((finite_specializationMax_of_isOpen_noetherianSpace hKo).image (π.fiberι x).base).subset ?_
  rintro y ⟨hyV, rfl, hmax⟩
  obtain ⟨z, hz⟩ : y ∈ Set.range (π.fiberι (π.base y)) := by
    rw [π.range_fiberι]; exact rfl
  have hz' : z = π.asFiber y :=
    (π.fiberι (π.base y)).isEmbedding.injective (by rw [hz, π.fiberι_asFiber])
  subst hz'
  refine ⟨π.asFiber y, ⟨?_, ?_⟩, hz⟩
  · show (π.fiberι _).base (π.asFiber y) ∈ V
    rw [π.fiberι_asFiber]; exact hyV
  · intro z' hz'
    exact AlgebraicGeometry.Scheme.le_iff_specializes.mp
      (hmax (AlgebraicGeometry.Scheme.le_iff_specializes.mpr hz'))

/-- Stacks 02R9: for `π` locally of finite type and `X` locally Noetherian, the support of
`flatPullbackCoeff π r α` is locally finite in `Y` (i.e. the condition of the `dite` in the definition of
`flatPullbackCycle` holds).

Proof: let `y ∈ Y` and take an affine open neighbourhood `V` (`Scheme.isBasis_affineOpens`), which is
quasi-compact. `π(V)` is quasi-compact and the support of `α` is locally finite, so `B = π(V) ∩ supp α` is
finite (Mathlib's `LocallyFiniteSupport.finite_inter_support_of_isCompact`). If `flatPullbackCoeff y′ ≠ 0`
and `y′ ∈ V`, then `α(π y′) ≠ 0` (`π y′ ∈ B`) and `coheight (π.asFiber y′) = 0` (`Order.coheight_eq_zero`: a
maximal point); for each `x ∈ B` there are finitely many such `y′` (`finite_isMax_asFiber_of_isCompact`), and
a finite union of finite sets is finite. -/
theorem AlgebraicGeometry.flatPullbackCoeff_locallyFinite {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) [AlgebraicGeometry.LocallyOfFiniteType π] [AlgebraicGeometry.IsLocallyNoetherian X]
    (r : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    ∀ z ∈ (Set.univ : Set Y), ∃ t ∈ nhds z,
      (t ∩ Function.support (AlgebraicGeometry.flatPullbackCoeff π r α)).Finite := by
  intro y _
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have hVc : IsCompact (V : Set Y) := AlgebraicGeometry.IsAffineOpen.isCompact hV
  refine ⟨V, V.isOpen.mem_nhds hyV, ?_⟩
  have hA : IsCompact (π.base '' (V : Set Y)) := hVc.image π.continuous
  have hB : (π.base '' (V : Set Y) ∩ Function.support α.toFun).Finite :=
    (Function.locallyFinsupp.locallyFiniteSupport α).finite_inter_support_of_isCompact hA
  refine (hB.biUnion fun x _ =>
    AlgebraicGeometry.finite_isMax_asFiber_of_isCompact π x hVc V.isOpen).subset ?_
  rintro y' ⟨hy'V, hy's⟩
  rw [Function.mem_support] at hy's
  unfold AlgebraicGeometry.flatPullbackCoeff at hy's
  split_ifs at hy's with hc
  · refine Set.mem_iUnion₂.mpr ⟨π.base y', ⟨Set.mem_image_of_mem _ hy'V, ?_⟩, hy'V, rfl,
      Order.coheight_eq_zero.mp hc.1⟩
    exact left_ne_zero_of_mul hy's
  · exact absurd rfl hy's


/-- Under the hypotheses, `flatPullbackCycle` is indeed given by `flatPullbackCoeff` (the junk branch of the
`dite` is not taken).

Source: Stacks 02RB (definition of the flat pullback) + 02R9 (local finiteness of the preimage).

**The only content is that the condition of the `dite` holds**: for `π` locally of finite type and `X`
locally Noetherian, `Function.support (flatPullbackCoeff π r α)` is locally finite in `Y`; then `dif_pos`
reduces the body to `flatPullbackCoeff`, both sides agree literally (the `toFun` field of `AlgebraicCycle`),
and `rfl` finishes.

Proof: let `y ∈ Y`.
1. Take a quasi-compact open neighbourhood `V` of `y` (schemes have a basis of quasi-compact opens:
   `Scheme.isBasis_affineOpens`, affine opens are quasi-compact). We show that
   `V ∩ support(flatPullbackCoeff)` is finite.
2. `flatPullbackCoeff π r α y′ ≠ 0` implies `α (π y′) ≠ 0`, i.e. `π y′ ∈ Function.support α`. `α` is an
   `AlgebraicCycle X ℤ`, whose support is locally finite in `X`; `π(V)` is quasi-compact (continuous image),
   so `π(V)` meets only finitely many points of `support α`; call this finite set `{x₁,…,x_s}`.
3. For each `x_j`: `flatPullbackCoeff ≠ 0` also requires `Order.coheight (π.asFiber y′) = 0`, i.e. `y′` is
   the generic point of an irreducible component of the fiber `Y_{x_j}`. `π` locally of finite type and `X`
   locally Noetherian ⟹ the fiber `Y_{x_j}` is locally Noetherian, the quasi-compact open `V ∩ Y_{x_j}` is a
   Noetherian space, and a Noetherian space has finitely many irreducible components, so there are finitely
   many such `y′` in `V`.
4. Altogether `V ∩ support` is a union of `s` finite sets, hence finite.

This is the argument of Stacks 02R9 ("the pullback of a locally finite family is locally finite", using
that `π` maps quasi-compacts to quasi-compacts and that Noetherian fibers have finitely many components).
The finiteness (a) of the intersection of a quasi-compact set with a locally finite support is Mathlib's
`Function.locallyFinsupp.locallyFiniteSupport` + `LocallyFiniteSupport.finite_inter_support_of_isCompact`;
(b) the finiteness of fiber generic points in a quasi-compact open is
`finite_specializationMax_of_isOpen_noetherianSpace`, `noetherianSpace_of_isCompact_of_isOpen`,
`quasiCompact_fiberι`, `finite_isMax_asFiber_of_isCompact`; local finiteness itself is
`flatPullbackCoeff_locallyFinite` (Stacks 02R9). -/
theorem AlgebraicGeometry.flatPullbackCycle_apply {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : Y ⟶ X) [AlgebraicGeometry.LocallyOfFiniteType π] [AlgebraicGeometry.IsLocallyNoetherian X]
    (r : ℕ) (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (y : Y) :
    AlgebraicGeometry.flatPullbackCycle π r α y =
      if Order.coheight (π.asFiber y) = 0 ∧ Order.height y = Order.height (π.base y) + r then
        α (π.base y) * ((Module.length ((π.fiber (π.base y)).presheaf.stalk (π.asFiber y))
          ((π.fiber (π.base y)).presheaf.stalk (π.asFiber y))).toNat : ℤ)
      else 0 := by
  have h := AlgebraicGeometry.flatPullbackCoeff_locallyFinite π r α
  unfold AlgebraicGeometry.flatPullbackCycle
  rw [dif_pos h]
  show AlgebraicGeometry.flatPullbackCoeff π r α y = _
  unfold AlgebraicGeometry.flatPullbackCoeff
  by_cases hc : Order.coheight (π.asFiber y) = 0 ∧ Order.height y = Order.height (π.base y) + r
  · rw [if_pos hc]
  · rw [if_neg hc]

end
