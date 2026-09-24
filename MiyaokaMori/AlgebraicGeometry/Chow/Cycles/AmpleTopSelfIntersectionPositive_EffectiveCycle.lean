import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedInducedSubschemeIntegral
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupTopDimension
import MiyaokaMori.AlgebraicGeometry.Modules.SectionSupportComplNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RestrictionDegreePositiveOfAmple
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleApply
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2Scheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightEqOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightNeOne
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree

/-! # Helpers for the positivity of ample top self-intersections: effective cycles and zero schemes

Cycle-level input for the induction step of Stacks 0BEV (Chow form; used for Lemma 2.5 of the paper):

* `effective_cycle_class_eq_sum_pointClosure` — **an effective `d`-cycle on a field-proper scheme is
  a positive integer combination of the classes of its point closures**: for `c ∈ Z_d(Z)` with
  `c ≥ 0`, `[c] = Σ_{x ∈ supp c} (c x) · ι_{x*}[W_x]` in `A_d(Z)`, where `W_x = Z.pointClosure x`
  (reduced induced structure, integral) and `ι_x` its closed immersion (Ful98 §1.3 / Stacks 02QU);
* `idealSheafData_cycle_nonneg` — `[Z(I)]_d ≥ 0` (its coefficients are lengths);
* `exists_mem_support_coheight_eq_one` — a nonempty zero scheme `Z(s)` of a nonzero section on an
  integral locally Noetherian scheme has a point of coheight `1` (generic point of a component of
  `Z(s)`, Krull's Hauptidealsatz: Stacks 0BCN in the form
  `coheight_subschemeι_eq_one_of_mem_genericPoints`);
* `idealSheafOfSection_cycle_pos_of_coheight_eq_one` — at such a point the coefficient of
  `[Z(s)]_{d-1}` is `ord_x(s) ≥ 1` (Stacks 02QU + 02SE);
* `dimension_eq_zero_of_isAffine`, `isAffine_of_forall_mem_nonvanishingLocus` — the "X is not
  affine" step of 0BEV: an affine scheme proper over a field is finite over it, hence
  zero-dimensional.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.AmpleTopSelfIntersection

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

/-! ## Point-closure classes -/

open Classical in
/-- `ι_{x*}[W_x] = [x]` in `A_d(Z)` for `height x = d`: the pushforward of the fundamental class of
the reduced point closure `W_x` along its closed immersion is the class of the one-point cycle
`single x 1`.

Proof: `W_x` is integral of dimension `d` (`dimension_pointClosure`), so `[W_x]_d = single η 1` with
`η` its generic point (`fundamentalCycle_of_isIntegral`); the pushforward along a closed immersion of
a one-point cycle is the one-point cycle at the image (`properPushforward_single_of_isClosedImmersion`)
and `ι_x η = x` (`pointClosureι_genericPoint`). `chowPushforward` is the descended cycle pushforward
because pushforward respects rational equivalence over a field
(`properPushforward_rationallyEquivalent`, Stacks 02S2). -/
theorem chowPushforward_pointClosure_fundamentalChowClass {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ : IsProperOver K Z) [AlgebraicGeometry.IsLocallyNoetherian Z]
    (d : ℕ) (x : Z) (hx : Order.height x = (d : ℕ∞)) :
    AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
        ((Z.pointClosure x).fundamentalChowClass d) =
      AlgebraicGeometry.ChowGroup.mk ⟨Function.locallyFinsuppWithin.single x (1 : ℤ),
        ChowGroupTopDimension.single_mem_cycleSubgroup hx⟩ := by
  haveI : AlgebraicGeometry.IsProper (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ
  letI : (Z.pointClosure x).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  haveI : (Z.pointClosureι x).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  haveI : AlgebraicGeometry.IsProper
      ((Z.pointClosure x) ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    inferInstanceAs (AlgebraicGeometry.IsProper
      (Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))))
  have hdesc : AlgebraicGeometry.PushforwardDescends (Z.pointClosureι x) d :=
    AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent (k := K) _ d
  have hdimx : (Z.pointClosure x).dimension = d := AlgebraicGeometry.Scheme.dimension_pointClosure x hx
  have hfin : topologicalKrullDim (Z.pointClosure x) ≠ ⊤ := by
    rw [AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure x hx]
    intro h
    exact ENat.natCast_ne_top d (WithBot.coe_injective h)
  have hfund : (Z.pointClosure x).fundamentalCycle d =
      Function.locallyFinsuppWithin.single (genericPoint (Z.pointClosure x)) (1 : ℤ) := by
    have h := (Z.pointClosure x).fundamentalCycle_of_isIntegral hfin
    rw [hdimx] at h
    ext y
    rw [h, Function.locallyFinsuppWithin.single_apply]
  show AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
      (AlgebraicGeometry.ChowGroup.mk ⟨(Z.pointClosure x).fundamentalCycle d, _⟩) = _
  rw [AlgebraicGeometry.chowPushforward_mk _ d hdesc]
  congr 1
  apply Subtype.ext
  show AlgebraicGeometry.AlgebraicCycle.properPushforward (Z.pointClosureι x) ((Z.pointClosure x).fundamentalCycle d) = _
  rw [hfund, MiyaokaMori.Stacks02suCycle.properPushforward_single_of_isClosedImmersion,
    AlgebraicGeometry.Scheme.pointClosureι_genericPoint]

open Classical in
/-- A cycle with finite support and nonnegative coefficients is the sum of its one-point cycles:
`c = Σ_{x ∈ supp c} (c x) · single x 1`. -/
theorem cycle_eq_sum_single {X : AlgebraicGeometry.Scheme.{u}} (c : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (hfin : (Function.support c).Finite) (heff : ∀ x, 0 ≤ c x) :
    c = ∑ x ∈ hfin.toFinset, (c x).toNat • Function.locallyFinsuppWithin.single x (1 : ℤ) := by
  ext y
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply, smul_ite, smul_zero, nsmul_eq_mul, mul_one]
  by_cases hy : c y = 0
  · rw [hy, Finset.sum_eq_zero]
    intro x _
    split_ifs with h
    · subst h; simp [hy]
    · rfl
  · rw [Finset.sum_eq_single y]
    · rw [if_pos rfl, Int.toNat_of_nonneg (heff y)]
    · intro x _ hxy
      rw [if_neg (Ne.symm hxy)]
    · intro hy'
      exact absurd (hfin.mem_toFinset.mpr hy) hy'

open Classical in
/-- **An effective `d`-cycle on a field-proper scheme is a positive combination of point-closure
classes** (Ful98 §1.3 / Stacks 02QU): for `c ∈ Z_d(Z)` with all coefficients `≥ 0`, its support `S`
is finite, every `x ∈ S` has `height x = d`, and in `A_d(Z)`
`[c] = Σ_{x ∈ S} (c x) · ι_{x*}[W_x]`, `W_x := Z.pointClosure x`, `ι_x := Z.pointClosureι x`.

Proof: `Z` proper over `K` ⇒ compact ⇒ finite support (`properCycle_finiteSupport`);
`c ∈ Z_d(Z)` means coefficients are supported in height `d`; `c = Σ (c x) • single x 1` as cycles
(`cycle_eq_sum_single`), each term lies in `Z_d(Z)`, and `ChowGroup.mk` is additive; finally
`ι_{x*}[W_x] = [single x 1]` (`chowPushforward_pointClosure_fundamentalChowClass`). -/
theorem effective_cycle_class_eq_sum_pointClosure {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ : IsProperOver K Z) [AlgebraicGeometry.IsLocallyNoetherian Z] (d : ℕ)
    (c : AlgebraicGeometry.AlgebraicCycle Z ℤ) (h : c ∈ AlgebraicGeometry.cycleSubgroup Z d)
    (heff : ∀ x, 0 ≤ c x) :
    ∃ S : Finset Z, (∀ x, x ∈ S ↔ c x ≠ 0) ∧ (∀ x ∈ S, Order.height x = (d : ℕ∞)) ∧
      AlgebraicGeometry.ChowGroup.mk ⟨c, h⟩ =
        ∑ x ∈ S, (c x).toNat • AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
          ((Z.pointClosure x).fundamentalChowClass d) := by
  haveI : AlgebraicGeometry.IsProper (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ
  have hfin : (Function.support c).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) c
  have hht : ∀ x, c x ≠ 0 → Order.height x = (d : ℕ∞) := fun x hx => h x hx
  refine ⟨hfin.toFinset, fun x => hfin.mem_toFinset, fun x hx => hht x (hfin.mem_toFinset.mp hx), ?_⟩
  have hmem : ∀ x, (c x).toNat • Function.locallyFinsuppWithin.single x (1 : ℤ) ∈
      AlgebraicGeometry.cycleSubgroup Z d := by
    intro x
    by_cases hx : c x = 0
    · rw [hx, Int.toNat_zero, zero_smul]
      exact zero_mem _
    · exact nsmul_mem (ChowGroupTopDimension.single_mem_cycleSubgroup (hht x hx)) _
  have hsub : (⟨c, h⟩ : ↥(AlgebraicGeometry.cycleSubgroup Z d)) =
      ∑ x ∈ hfin.toFinset, (⟨_, hmem x⟩ : ↥(AlgebraicGeometry.cycleSubgroup Z d)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact cycle_eq_sum_single c hfin heff
  rw [hsub, map_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [chowPushforward_pointClosure_fundamentalChowClass Z hZ d x (hht x (hfin.mem_toFinset.mp hx)),
    ← map_nsmul]
  rfl

/-! ## Zero schemes of sections -/

/-- The coefficients of `[Z(I)]_d` are nonnegative (they are lengths of local rings at generic
points of components of `Z(I)`, or `0`): Stacks 02QU, `cycle_apply_subschemeι`. -/
theorem idealSheafData_cycle_nonneg {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Z] (I : Z.IdealSheafData) (d : ℕ) (x : Z) :
    0 ≤ I.cycle d x := by
  classical
  haveI : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  by_cases hx : x ∈ I.support
  · have hx' : x ∈ Set.range I.subschemeι.base := by rw [I.range_subschemeι]; exact hx
    obtain ⟨z', rfl⟩ := hx'
    rw [I.cycle_apply_subschemeι d z']
    show 0 ≤ (if AlgebraicGeometry.Intersection.pointClosureDimension I.subscheme z' = (d : ℕ)
      then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity I.subscheme z' else 0)
    split_ifs
    · exact AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_nonneg _ _
    · exact le_rfl
  · rw [I.cycle_apply_of_notMem_support d hx]

/-- **A nonempty zero scheme has a coheight-one point** (Stacks 0BCN): `W`
integral and locally Noetherian, `s ≠ 0` a global section of a line bundle `M`, `w ∈ Z(s)`. Then
some `x ∈ Z(s)` has `coheight x = 1` in `W`.

Proof: `w = ι z'` for a point `z'` of the closed subscheme `Z(s)`; the irreducible component of
`Z(s)` through `z'` has a generic point `z''` (schemes are sober), which lies in
`genericPoints Z(s)`; by Krull's Hauptidealsatz (`coheight_subschemeι_eq_one_of_mem_genericPoints`,
which uses that `s` is locally a nonzerodivisor because `W` is integral and `s ≠ 0`) `x := ι z''`
has coheight `1`. -/
theorem exists_mem_support_coheight_eq_one {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (M : W.Modules) [M.IsLineBundle] (s : (M.val.obj (Opposite.op ⊤) : Type u)) (hs : s ≠ 0)
    {w : W} (hw : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection M s).support) :
    ∃ x ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection M s).support, Order.coheight x = 1 := by
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection M s with hI
  have hw' : w ∈ Set.range I.subschemeι.base := by rw [I.range_subschemeι]; exact hw
  obtain ⟨z', rfl⟩ := hw'
  obtain ⟨z'', hz''⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z'))
    isClosed_irreducibleComponent
  have hgen : z'' ∈ genericPoints I.subscheme := by
    show closure ({z''} : Set I.subscheme) ∈ irreducibleComponents I.subscheme
    rw [hz''.def]
    exact irreducibleComponent_mem_irreducibleComponents z'
  refine ⟨I.subschemeι.base z'', ?_,
    AlgebraicGeometry.Scheme.coheight_subschemeι_eq_one_of_mem_genericPoints M s hs z'' hgen⟩
  have hmem : I.subschemeι.base z'' ∈ Set.range I.subschemeι.base := ⟨z'', rfl⟩
  rw [I.range_subschemeι] at hmem
  exact hmem

/-- **Positive multiplicity at a coheight-one point of the zero scheme**: `W` integral, locally
Noetherian, locally of finite type over a field, `dim W = e + 1`, `s ≠ 0` a global section of a
line bundle `M`, `x ∈ Z(s)` with `coheight x = 1`. Then the coefficient of `[Z(s)]_e` at `x` is
positive.

Proof: at a coheight-one point the coefficient of `[Z(s)]_e` is the order of vanishing
`ord_x(s_η)` (`idealSheafOfSection_cycle_apply_of_coheight_eq_one`, Stacks 02QU/02SE), and since
`s` vanishes at `x` (`x ∈ Z(s)` ⇔ `s_x ∈ 𝔪_x M_x`) this order is `≥ 1`
(`rationalSectionOrd_pos_of_isZeroAt`: write `s_x = a • e` with `e` a generator, `a ∈ 𝔪_x`,
`ord(a) = length(𝒪_x/(a)) ≥ 1`). -/
theorem idealSheafOfSection_cycle_pos_of_coheight_eq_one {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}} [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (M : W.Modules) [M.IsLineBundle] (s : (M.val.obj (Opposite.op ⊤) : Type u)) (hs : s ≠ 0)
    (e : ℕ) (hdim : W.dimension = e + 1) {x : W}
    (hx : x ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection M s).support)
    (hx1 : Order.coheight x = 1) :
    0 < (AlgebraicGeometry.Scheme.idealSheafOfSection M s).cycle e x := by
  rw [AlgebraicGeometry.Scheme.idealSheafOfSection_cycle_apply_of_coheight_eq_one (k := k)
    M s hs e hdim x hx1]
  refine AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_pos_of_isZeroAt M s hx1 ?_
    (AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero M s hs)
  exact (AlgebraicGeometry.Scheme.mem_idealSheafOfSection_support_iff M s x).mp hx

/-- **The `d`-cycle class of a closed subscheme is a positive combination of its `d`-dimensional
component classes**: `Z` proper over `K`, locally Noetherian, `I` an ideal sheaf with `[Z(I)]_d ∈ Z_d(Z)`; then
there are a finite set `s ⊆ Z` and positive integers `m_x` (`x ∈ s`) with `height x = d` and
`[Z(I)]_d = Σ_{x ∈ s} m_x · ι_{x*}[W_x]` in `A_d(Z)`.

Proof: `[Z(I)]_d` is effective (`idealSheafData_cycle_nonneg`), so
`effective_cycle_class_eq_sum_pointClosure` applies with `s := supp [Z(I)]_d` and
`m_x := ([Z(I)]_d)(x) > 0`. -/
theorem idealSheafData_cycle_class_eq_sum_pointClosure {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ : IsProperOver K Z) [AlgebraicGeometry.IsLocallyNoetherian Z]
    (I : Z.IdealSheafData) (d : ℕ) (h : I.cycle d ∈ AlgebraicGeometry.cycleSubgroup Z d) :
    ∃ (s : Finset Z) (m : Z → ℕ), (∀ x ∈ s, 0 < m x) ∧ (∀ x ∈ s, Order.height x = (d : ℕ∞)) ∧
      AlgebraicGeometry.ChowGroup.mk ⟨I.cycle d, h⟩ =
        ∑ x ∈ s, m x • AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
          ((Z.pointClosure x).fundamentalChowClass d) := by
  obtain ⟨S, hS, hht, hsum⟩ := effective_cycle_class_eq_sum_pointClosure Z hZ d (I.cycle d) h
    (idealSheafData_cycle_nonneg I d)
  refine ⟨S, fun x => (I.cycle d x).toNat, fun x hx => ?_, hht, hsum⟩
  exact Int.lt_toNat.mpr (by
    simpa using lt_of_le_of_ne (idealSheafData_cycle_nonneg I d x) (Ne.symm ((hS x).mp hx)))

/-! ## "X is not affine" (Stacks 0BEV) -/

/-- An affine scheme proper over a field is zero-dimensional: proper + affine ⇒ finite
(`IsFinite.iff_isProper_and_isAffineHom`) ⇒ `Γ(W, 𝒪)` is a finite `k`-algebra ⇒ Artinian ⇒ `W`
is discrete ⇒ `topologicalKrullDim W = 0`. (Same argument as `IntegralCurve.not_isAffine`.) -/
theorem dimension_eq_zero_of_isAffine {k : Type u} [Field k]
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hW : IsProperOver k W) [AlgebraicGeometry.IsAffine W] : W.dimension = 0 := by
  haveI : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hW
  set p := W ↘ AlgebraicGeometry.Spec (CommRingCat.of k) with hp
  have : AlgebraicGeometry.IsFinite p :=
    AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hfin : p.appTop.hom.Finite := p.finite_appTop
  let : Algebra Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(W, ⊤) := p.appTop.hom.toAlgebra
  have : Module.Finite Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(W, ⊤) := hfin
  have : IsArtinianRing Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  have : IsArtinianRing Γ(W, ⊤) :=
    IsArtinianRing.of_finite Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(W, ⊤)
  have : AlgebraicGeometry.IsLocallyArtinian (AlgebraicGeometry.Spec Γ(W, ⊤)) :=
    AlgebraicGeometry.Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : AlgebraicGeometry.IsLocallyArtinian W :=
    AlgebraicGeometry.IsLocallyArtinian.of_isImmersion W.isoSpec.hom
  have h0 := topologicalKrullDim_zero_of_discreteTopology W
  unfold AlgebraicGeometry.Scheme.dimension
  cases hd : topologicalKrullDim W with
  | bot => rfl
  | coe t =>
    rw [hd] at h0
    have ht : t ≤ 0 := by exact_mod_cast h0
    rw [nonpos_iff_eq_zero.mp ht]
    rfl

/-- If the nonvanishing locus `X_s` of a section is affine and is all of `X`, then `X` is affine. -/
theorem isAffine_of_forall_mem_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤))
    (haff : AlgebraicGeometry.IsAffineOpen (L.nonvanishingLocus s))
    (htop : ∀ x : X, x ∈ L.nonvanishingLocus s) : AlgebraicGeometry.IsAffine X := by
  have heq : L.nonvanishingLocus s = ⊤ := top_le_iff.mp (fun x _ => htop x)
  rw [heq] at haff
  exact (AlgebraicGeometry.IsAffine.iff_of_isIso X.topIso.hom).mp haff

end MiyaokaMori.AmpleTopSelfIntersection

end
