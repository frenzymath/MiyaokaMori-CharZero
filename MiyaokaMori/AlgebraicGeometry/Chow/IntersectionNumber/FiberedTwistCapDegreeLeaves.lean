import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CapDegreeExpansion
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.PullbackTrivialOnFiber
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Bridge
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusOn
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.AmpleTopSelfIntersectionPositive
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveToCurveSurjectiveOrConstant
import MiyaokaMori.AlgebraicGeometry.Morphisms.CurveInFiberFactors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ZeroSchemeOfCurveSectionDiscrete
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k_IsAmplePullbackIso
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.WeightedProjTopDegree

/-! # Intersection numbers on a fibered variety: positivity and arithmetic

The intersection-number computation for the negative curve on a fibered variety (Lemma 2.5 of the paper) splits into:

* **Arithmetic** (this file): `exists_ab` — from `(M^r) = eB^{r}T + r·eB^{r−1}·eF·w < 0`, `w ≥ 0`, `w' > 0`
  one finds `a, b > 0` with `(L^r) = b^r T + r b^{r−1} a w' > 0` and
  `(M^{r−1}·L) = eB^{r−1}(bT + a w') + (r−1)eB^{r−2}eF·b·w < 0` (`r = d + 2`, `T = (β^r)`,
  `w = (β^{r−1}·φ)`, `w' = (β^{r−1}·φ')`).
* **Empty zero scheme ⇒ trivial line bundle** (this file): `nonempty_iso_unit_of_support_eq_empty`.
* **Positivity** (this file): `capDeg_pullback_section_nonneg` / `capDeg_pullback_section_pos` — `w ≥ 0`,
  `w' > 0`, both from the core decomposition `capDeg_pullback_section_eq_sum` (`w = Σ_{x∈S} f x`, `f > 0`,
  `supp Z(s) ≠ ∅ ⇒ S ≠ ∅`); auxiliary lemmas: `mem_support_pullback_section_iff` (the zero locus of a
  pulled-back section is the preimage), `surjective_of_not_range_singleton`, `sectionPullbackAlong_ne_zero`,
  `isClosed_singleton_and_range_subset_of_mem_support`, `topSelfIntersection_pullback_pos_of_range_subset`.
* **Expansion**: `CapDegreeExpansion.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FiberedTwistCapDegreeLeaves

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori.CapDegreeExpansion

/-! ## Arithmetic -/

/-- The explicit choice in integer form: `b := 2(d+2)·w'·eB`, `a := (d+3)·eB·(−T) − (d+1)(d+2)·eF·w`. -/
theorem ab_int (d eB eF : ℕ) (T w w' : ℤ) (heB : 0 < eB) (hw : 0 ≤ w) (hw' : 0 < w')
    (hneg : (eB : ℤ) ^ (d + 2) * T + ((d : ℤ) + 2) * (eB : ℤ) ^ (d + 1) * (eF : ℤ) * w < 0) :
    0 < ((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w ∧
    0 < 2 * ((d : ℤ) + 2) * w' * (eB : ℤ) ∧
    0 < (2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) ^ (d + 2) * T +
        ((d : ℤ) + 2) * (2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) ^ (d + 1) *
          (((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w) * w' ∧
    (eB : ℤ) ^ (d + 1) * ((2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) * T +
        (((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w) * w') +
      ((d : ℤ) + 1) * (eB : ℤ) ^ d * (eF : ℤ) * ((2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) * w) < 0 := by
  have heB' : (0 : ℤ) < eB := by exact_mod_cast heB
  have heF' : (0 : ℤ) ≤ eF := by exact_mod_cast Nat.zero_le eF
  have hd' : (0 : ℤ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hpow : (0 : ℤ) < (eB : ℤ) ^ (d + 1) := pow_pos heB' _
  -- the key inequality `(d+2)·eF·w < eB·(−T)`
  have hkey : ((d : ℤ) + 2) * (eF : ℤ) * w < (eB : ℤ) * (-T) := by
    have h1 : (eB : ℤ) ^ (d + 1) * ((eB : ℤ) * T + ((d : ℤ) + 2) * (eF : ℤ) * w) < 0 := by
      calc (eB : ℤ) ^ (d + 1) * ((eB : ℤ) * T + ((d : ℤ) + 2) * (eF : ℤ) * w)
          = (eB : ℤ) ^ (d + 2) * T + ((d : ℤ) + 2) * (eB : ℤ) ^ (d + 1) * (eF : ℤ) * w := by ring
        _ < 0 := hneg
    have h2 : (eB : ℤ) * T + ((d : ℤ) + 2) * (eF : ℤ) * w < 0 := by
      by_contra h
      push Not at h
      exact absurd (mul_nonneg hpow.le h) (not_le.mpr h1)
    linarith
  have hPw : (0 : ℤ) ≤ (eF : ℤ) * w := mul_nonneg heF' hw
  have hgap : 0 < (eB : ℤ) * (-T) - ((d : ℤ) + 2) * (eF : ℤ) * w := by linarith
  have ha : 0 < ((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w := by
    have h1 : ((d : ℤ) + 1) * (((d : ℤ) + 2) * (eF : ℤ) * w) ≤
        ((d : ℤ) + 3) * (((d : ℤ) + 2) * (eF : ℤ) * w) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : ((d : ℤ) + 3) * (((d : ℤ) + 2) * (eF : ℤ) * w) < ((d : ℤ) + 3) * ((eB : ℤ) * (-T)) :=
      mul_lt_mul_of_pos_left hkey (by positivity)
    nlinarith [h1, h2]
  have hb : 0 < 2 * ((d : ℤ) + 2) * w' * (eB : ℤ) := by positivity
  refine ⟨ha, hb, ?_, ?_⟩
  · have hid : (2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) ^ (d + 2) * T +
        ((d : ℤ) + 2) * (2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) ^ (d + 1) *
          (((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w) * w' =
        (2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) ^ (d + 1) *
          ((((d : ℤ) + 2) * ((d : ℤ) + 1) * w') *
            ((eB : ℤ) * (-T) - ((d : ℤ) + 2) * (eF : ℤ) * w)) := by ring
    rw [hid]
    exact mul_pos (pow_pos hb _) (mul_pos (by positivity) hgap)
  · have hid : (eB : ℤ) ^ (d + 1) * ((2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) * T +
        (((d : ℤ) + 3) * (eB : ℤ) * (-T) - ((d : ℤ) + 1) * ((d : ℤ) + 2) * (eF : ℤ) * w) * w') +
      ((d : ℤ) + 1) * (eB : ℤ) ^ d * (eF : ℤ) * ((2 * ((d : ℤ) + 2) * w' * (eB : ℤ)) * w) =
        -((eB : ℤ) ^ (d + 1) * (((d : ℤ) + 1) * w') *
          ((eB : ℤ) * (-T) - ((d : ℤ) + 2) * (eF : ℤ) * w)) := by ring
    rw [hid, neg_lt_zero]
    exact mul_pos (mul_pos hpow (by positivity)) hgap

/-- **The choice of `a`, `b` (natural-number form)**: `T = (β^{d+2})`, `w = (β^{d+1}·φ) ≥ 0`,
`w' = (β^{d+1}·φ') > 0`, `(M^{d+2}) = eB^{d+2}T + (d+2)eB^{d+1}eF·w < 0` ⇒ there are `a, b > 0` with
`(L^{d+2}) = b^{d+2}T + (d+2)b^{d+1}a·w' > 0` and `eB^{d+1}(bT + a w') + (d+1)eB^d eF (b w) < 0`. -/
theorem exists_ab (d eB eF : ℕ) (T w w' : ℤ) (heB : 0 < eB) (hw : 0 ≤ w) (hw' : 0 < w')
    (hneg : (eB : ℤ) ^ (d + 2) * T + ((d : ℤ) + 2) * (eB : ℤ) ^ (d + 1) * (eF : ℤ) * w < 0) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      0 < (b : ℤ) ^ (d + 2) * T + ((d : ℤ) + 2) * (b : ℤ) ^ (d + 1) * (a : ℤ) * w' ∧
      (eB : ℤ) ^ (d + 1) * ((b : ℤ) * T + (a : ℤ) * w') +
        ((d : ℤ) + 1) * (eB : ℤ) ^ d * (eF : ℤ) * ((b : ℤ) * w) < 0 := by
  obtain ⟨ha, hb, h1, h2⟩ := ab_int d eB eF T w w' heB hw hw' hneg
  obtain ⟨a, ha'⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨w'n, hw'n⟩ := Int.eq_ofNat_of_zero_le hw'.le
  refine ⟨a, 2 * (d + 2) * w'n * eB, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℤ) < a := by rw [← ha']; exact ha
    exact_mod_cast this
  · have hw'n' : 0 < w'n := by
      have : (0 : ℤ) < w'n := by rw [← hw'n]; exact hw'
      exact_mod_cast this
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hw'n') heB
  · have hb' : ((2 * (d + 2) * w'n * eB : ℕ) : ℤ) = 2 * ((d : ℤ) + 2) * w' * (eB : ℤ) := by
      push_cast; rw [hw'n]
    rw [hb', ← ha']
    exact h1
  · have hb' : ((2 * (d + 2) * w'n * eB : ℕ) : ℤ) = 2 * ((d : ℤ) + 2) * w' * (eB : ℤ) := by
      push_cast; rw [hw'n]
    rw [hb', ← ha']
    exact h2

/-! ## Empty zero scheme ⇒ trivial line bundle -/

/-- **A nowhere vanishing section trivializes the line bundle**: `supp Z(s) = ∅` ⇒ `s` is a global frame ⇒
`L ≅ O_X` (Stacks 01CY: `L|_{X_s} ≅ O` when `X_s = X`). -/
theorem nonempty_iso_unit_of_support_eq_empty {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤))
    (h : (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support) = (∅ : Set X)) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  have h1 : ((nonvanishingLocus L s : X.Opens) : Set X) = Set.univ := by
    have h0 := AlgebraicGeometry.Scheme.idealSheafOfSection_support_compl_eq_nonvanishingLocus L s
    rw [h, Set.compl_empty] at h0
    exact h0.symm
  have h2 : frameLocus L s = ⊤ := by
    rw [MiyaokaMori.Found.CartierBridge.frameLocus_eq_nonvanishingLocus L s]
    exact Opens.ext h1
  have h3 : IsFrame L (frameLocus L s) (L.res le_top s) := by
    refine IsFrame.of_sSup {W : X.Opens | IsFrame L W (L.res le_top s)}
      (fun W hW => le_sSup hW) le_rfl (fun W hW => ?_)
    have hW' : IsFrame L W (L.res le_top s) := hW
    convert hW' using 2
    exact L.res_res _ _ _
  rw [h2] at h3
  have h4 : IsFrame L ⊤ s := by
    have : L.res (le_top : (⊤ : X.Opens) ≤ ⊤) s = s := L.res_self s
    rw [this] at h3
    exact h3
  exact iso_unit_of_trivialization_top L h4.trivialization rfl

/-! ## Positivity -/

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

section Positivity

variable {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}}
    (π : V ⟶ C.toScheme)
    (W : AlgebraicGeometry.Scheme.{u})
    (ι : W ⟶ V)
    (N : C.toScheme.Modules) [N.IsLineBundle] (s : (N.val.obj (Opposite.op ⊤) : Type u))

/-- **The zero locus of a pulled-back section is the preimage of the zero locus** (pointwise):
`w ∈ supp Z(ι^*π^*s) ↔ (ι ≫ π)(w) ∈ supp Z(s)`. Replace both sides by non-vanishing loci
(`idealSheafOfSection_support_compl_eq_nonvanishingLocus`) and apply
`mem_nonvanishingLocus_sectionPullbackAlong` twice. -/
theorem mem_support_pullback_section_iff (w : W) :
    w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N))
        (sectionPullbackAlong ι (sectionPullbackAlong π s))).support ↔
      (ι ≫ π).base w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support := by
  have h1 := AlgebraicGeometry.Scheme.idealSheafOfSection_support_compl_eq_nonvanishingLocus
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N))
    (sectionPullbackAlong ι (sectionPullbackAlong π s))
  have h2 := AlgebraicGeometry.Scheme.idealSheafOfSection_support_compl_eq_nonvanishingLocus N s
  have e1 : w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N))
      (sectionPullbackAlong ι (sectionPullbackAlong π s))).support ↔
      ¬ w ∈ ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)).nonvanishingLocus
          (sectionPullbackAlong ι (sectionPullbackAlong π s)) := by
    rw [← SetLike.mem_coe, ← not_not (a := w ∈ _), ← Set.mem_compl_iff, h1]
    rfl
  have e2 : (ι ≫ π).base w ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support ↔
      ¬ (ι ≫ π).base w ∈ N.nonvanishingLocus s := by
    rw [← SetLike.mem_coe, ← not_not (a := (ι ≫ π).base w ∈ _), ← Set.mem_compl_iff, h2]
    rfl
  rw [e1, e2, AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionPullbackAlong,
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionPullbackAlong,
    AlgebraicGeometry.Scheme.Hom.comp_apply]

/-- `ρ := ι ≫ π` nonconstant ⇒ surjective (`range_closedPoint_or_surjective`: a morphism to a curve is
constant or surjective). -/
theorem surjective_of_not_range_singleton
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsIntegral W]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c}) :
    Function.Surjective (ι ≫ π).base := by
  rcases range_closedPoint_or_surjective W hW (ι ≫ π) with ⟨c, _, hc⟩ | h
  · exact absurd ⟨c, hc⟩ hns
  · exact h

/-- **The pulled-back section is nonzero**: `ρ` is surjective, so take `w` with `ρ(w) = η_C`;
`η_C ∉ supp Z(s)` (as `s ≠ 0`), hence `w ∉ supp Z(ρ^*s)`, so the germ of `ρ^*s` at `η_W` is nonzero
(`germ_genericPoint_ne_zero_of_notMem_support`); in particular `ρ^*s ≠ 0`. -/
theorem sectionPullbackAlong_ne_zero [AlgebraicGeometry.IsIntegral W] (hs : s ≠ 0)
    (hsurj : Function.Surjective (ι ≫ π).base) :
    sectionPullbackAlong ι (sectionPullbackAlong π s) ≠ 0 := by
  obtain ⟨w, hw⟩ := hsurj (genericPoint C.toScheme)
  have hη : genericPoint C.toScheme ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support :=
    AlgebraicGeometry.Scheme.genericPoint_notMem_idealSheafOfSection_support N s
      (AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero N s hs)
  have hw' : w ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N))
      (sectionPullbackAlong ι (sectionPullbackAlong π s))).support := by
    rw [mem_support_pullback_section_iff, hw]
    exact hη
  have hne := AlgebraicGeometry.Scheme.germ_genericPoint_ne_zero_of_notMem_support _ _ hw'
  intro h0
  apply hne
  rw [h0]
  exact map_zero _

/-- **Closed points and constancy on the closure**: `c ∈ supp Z(s)` (`s ≠ 0`) is a closed point of `C`; if
`x ∈ W` satisfies `ρ(x) = c`, then every point of `W_x := closure {x}` maps to `c`
(`x ⤳ y ⇒ c = ρ(x) ⤳ ρ(y)`, and `c` is minimal). -/
theorem isClosed_singleton_and_range_subset_of_mem_support (hs : s ≠ 0) {x : W}
    (hx : (ι ≫ π).base x ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support) :
    IsClosed ({(ι ≫ π).base x} : Set C.toScheme) ∧
      Set.range ((W.pointClosureι x ≫ ι) ≫ π).base ⊆ {(ι ≫ π).base x} := by
  have hη : genericPoint C.toScheme ∉ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support :=
    AlgebraicGeometry.Scheme.genericPoint_notMem_idealSheafOfSection_support N s
      (AlgebraicGeometry.Scheme.Modules.germ_genericPoint_ne_zero N s hs)
  have hne : (ι ≫ π).base x ≠ genericPoint C.toScheme := fun h => hη (h ▸ hx)
  have hmin : IsMin ((ι ≫ π).base x) :=
    MiyaokaMori.ZeroSchemeOfCurveSectionDiscrete.isMin_of_ne_genericPoint C hne
  have key : ∀ y : C.toScheme, (ι ≫ π).base x ⤳ y → y = (ι ≫ π).base x := by
    intro y hy
    have h1 : y ≤ (ι ≫ π).base x := AlgebraicGeometry.Scheme.le_iff_specializes.mpr hy
    have h2 : y ⤳ (ι ≫ π).base x := AlgebraicGeometry.Scheme.le_iff_specializes.mp (hmin h1)
    exact (h2.antisymm hy).eq
  refine ⟨?_, ?_⟩
  · apply isClosed_of_closure_subset
    intro y hy
    exact key y (specializes_iff_mem_closure.mpr hy)
  · rintro _ ⟨v, rfl⟩
    have h1 : x ⤳ (W.pointClosureι x).base v :=
      specializes_iff_mem_closure.mpr
        (MiyaokaMori.ClosedImmersionPushforward.pointClosureι_mem_closure x v)
    have h2 : (ι ≫ π).base x ⤳ (ι ≫ π).base ((W.pointClosureι x).base v) :=
      h1.map (ι ≫ π).continuous
    have h3 : (ι ≫ π).base x ⤳ ((W.pointClosureι x ≫ ι) ≫ π).base v := by
      simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using h2
    exact Set.mem_singleton_iff.mpr (key _ h3)

end Positivity

/-- **The top self-intersection of `ι^*B` on an integral closed subscheme inside a fiber is positive**:
`Γ ⊂ W` integral, proper over `K`, of positive dimension, `j : Γ → W` a closed immersion, and the image of
`(j ≫ ι ≫ π)` contained in the closed point `{c}`. Then `((j^*ι^*B)^{dim Γ}) > 0`.

Proof: `j^*ι^*π^*A ≅ O_Γ` (`exists_closedImmersion_to_fiber_of_range_subset` +
`pullback_fiberι_pullback_iso_unit`: the curve factors through the fiber, on which the pullback from the
base is trivial), so `j^*ι^*B ≅ (j ≫ ι)^*(B ⊗ π^*A)`, the pullback of an ample bundle along a closed
immersion, whose top self-intersection is positive (`topSelfIntersection_pos_of_isAmple`);
`topSelfIntersection_congr` transports along the isomorphism. -/
theorem topSelfIntersection_pullback_pos_of_range_subset {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {V : AlgebraicGeometry.Scheme.{u}} (π : V ⟶ C.toScheme)
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1)))
    (W : AlgebraicGeometry.Scheme.{u}) (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    (Γ : AlgebraicGeometry.Scheme.{u}) [Γ.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Γ] (j : Γ ⟶ W) [AlgebraicGeometry.IsClosedImmersion j]
    (hΓ : IsProperOver K Γ) (hpos : 0 < Γ.dimension) (c : C.toScheme)
    (hc : IsClosed ({c} : Set C.toScheme)) (hrange : Set.range ((j ≫ ι) ≫ π).base ⊆ {c}) :
    0 < AlgebraicGeometry.topSelfIntersection Γ hΓ
      ((AlgebraicGeometry.Scheme.Modules.pullback j).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B)) := by
  -- (j ≫ ι)^*π^*A ≅ O_Γ
  obtain ⟨f, hf, hfι⟩ :=
    AlgebraicGeometry.exists_closedImmersion_to_fiber_of_range_subset (j ≫ ι) π c hc hrange
  obtain ⟨e⟩ := AlgebraicGeometry.pullback_fiberι_pullback_iso_unit π A c
  let tA : (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) ≅
      SheafOfModules.unit Γ.ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hfι.symm).app _ ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f (π.fiberι c)).app _).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f
  -- j^*ι^*B ≅ (j ≫ ι)^*(B ⊗ π^*A)
  let eB : (AlgebraicGeometry.Scheme.Modules.pullback j).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj B :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j ι).app B
  let eH : (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj
      (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj B :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (j ≫ ι) _ _ ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso (j ≫ ι) B 1 ≪≫
        (AlgebraicGeometry.Scheme.Modules.unitTensorIso _ :
          AlgebraicGeometry.Scheme.Modules.tensor
            (AlgebraicGeometry.Scheme.Modules.tensorPow
              ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj B) 0)
            ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ ι)).obj B) ≅ _)) _ ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso (j ≫ ι) _ 1 ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMapIso tA 1 ≪≫
        AlgebraicGeometry.Scheme.Modules.unitTensorPowIso Γ 1) ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorUnitIso _
  rw [AlgebraicGeometry.topSelfIntersection_congr Γ hΓ _ _ (eB ≪≫ eH.symm)]
  exact AlgebraicGeometry.topSelfIntersection_pos_of_isAmple V _ hA Γ (j ≫ ι) hΓ hpos

section Core

variable {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1)))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)

include hA in
/-- **Core decomposition** (steps 1–6 shared by the two positivity statements): write `ρ := ι ≫ π`,
`σ := ρ^*s`, `w := deg(c₁(ι^*B)^{d+1} ∩ c₁(ι^*π^*N) ∩ [W])`. There are a finite set `S ⊂ W` and
`f : W → ℤ` with `f > 0` on `S`, `w = Σ_{x∈S} f x`, and `supp Z(s) ≠ ∅ ⇒ S ≠ ∅`.

**Source**: Fulton, Intersection Theory, §2.3–2.5; Stacks 02SJ/02SK
(`firstChernClass_cap_fundamentalClass_of_regular_section`),
Stacks 02QU (`effective_cycle_class_eq_sum_pointClosure`), Stacks 0BCN (`exists_mem_support_coheight_eq_one`), 
Stacks 02SE (`idealSheafOfSection_cycle_pos_of_coheight_eq_one`).

**Proof**:
1. `ρ` is surjective (`surjective_of_not_range_singleton`); `σ ≠ 0` (`sectionPullbackAlong_ne_zero`).
2. `c₁(ι^*π^*N) ∩ [W] = [Z(σ)]_{d+1}` (02SK; `W` integral, locally Noetherian, proper ⇒ locally of finite type).
3. `[Z(σ)]_{d+1} = Σ_{x∈S} m_x · ι_{x*}[W_x]`, `S = supp [Z(σ)]_{d+1}`, `m_x > 0`, `height x = d+1`.
4. `capDeg` is additive and `deg(c₁(ι^*B)^{d+1} ∩ ι_{x*}[W_x]) = ((ι_x^*ι^*B)^{d+1})`
 (`capDegree_chowPushforward_fundamentalChowClass`: projection formula for closed immersions + invariance
   of the degree under pushforward).
5. `x ∈ S ⇒ x ∈ supp Z(σ) ⇒ c := ρ(x) ∈ supp Z(s)` is a closed point with `ρ(W_x) = {c}`
 (`isClosed_singleton_and_range_subset_of_mem_support`), so `((ι_x^*ι^*B)^{d+1}) > 0`
 (`topSelfIntersection_pullback_pos_of_range_subset`). Take `f x := m_x · ((ι_x^*ι^*B)^{d+1})`.
6. If `supp Z(s) ≠ ∅`: take `c`; surjectivity of `ρ` gives `w` with `ρ(w) = c`, so `w ∈ supp Z(σ)`; 0BCN
   gives `x ∈ supp Z(σ)` of coheight `1`, and 02SE gives `[Z(σ)]_{d+1}(x) > 0`, i.e. `x ∈ S`. -/
theorem capDeg_pullback_section_eq_sum (d : ℕ) (hdim : W.dimension = d + 2)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (N : C.toScheme.Modules) [N.IsLineBundle] (s : Γ(N, ⊤)) (hs : s ≠ 0) :
    ∃ (S : Finset W) (f : W → ℤ), (∀ x ∈ S, 0 < f x) ∧
      capDeg W hW ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) (d + 1)
        (AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (d + 2)
          (W.fundamentalChowClass (d + 2))) = ∑ x ∈ S, f x ∧
      ((SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support).Nonempty →
        S.Nonempty) := by
  have hprop : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  -- structures on the point closures
  let _ : ∀ x : W, (W.pointClosure x).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    fun x => ⟨W.pointClosureι x ≫ (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  have _ : ∀ x : W, (W.pointClosureι x).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    fun x => ⟨rfl⟩
  have hWx : ∀ x : W, IsProperOver K (W.pointClosure x) := fun x =>
    inferInstanceAs (AlgebraicGeometry.IsProper
      (W.pointClosureι x ≫ (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K))))
  set L : W.Modules := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) with hL
  set σ : (L.val.obj (Opposite.op ⊤) : Type u) := sectionPullbackAlong ι (sectionPullbackAlong π s)
    with hσdef
  -- 1. `ρ` surjective, `σ ≠ 0`
  have hsurj : Function.Surjective (ι ≫ π).base := surjective_of_not_range_singleton π W ι hW hns
  have hσ : σ ≠ 0 := sectionPullbackAlong_ne_zero π W ι N s hs hsurj
  -- 2. c₁(L) ∩ [W] = [Z(σ)]_{d+1}
  obtain ⟨hmem, hcap⟩ :=
    AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section (k := K) L σ hσ (d + 1) hdim
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection L σ with hI
  -- 3. [Z(σ)]_{d+1} = Σ m_x ι_{x*}[W_x]
  obtain ⟨S, hS, hht, hsum⟩ :=
    MiyaokaMori.AmpleTopSelfIntersection.effective_cycle_class_eq_sum_pointClosure W hW (d + 1)
      (I.cycle (d + 1)) hmem
      (MiyaokaMori.AmpleTopSelfIntersection.idealSheafData_cycle_nonneg I (d + 1))
  -- 5. every term is positive
  have hterm : ∀ x ∈ S, 0 < AlgebraicGeometry.topSelfIntersection (W.pointClosure x) (hWx x)
      ((AlgebraicGeometry.Scheme.Modules.pullback (W.pointClosureι x)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B)) := by
    intro x hx
    have hxI : x ∈ I.support := by
      by_contra hxI
      exact (hS x).mp hx (I.cycle_apply_of_notMem_support (d + 1) hxI)
    have hxs : (ι ≫ π).base x ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support :=
      (mem_support_pullback_section_iff π W ι N s x).mp hxI
    obtain ⟨hc, hrange⟩ := isClosed_singleton_and_range_subset_of_mem_support π W ι N s hs hxs
    have hpos : 0 < (W.pointClosure x).dimension := by
      rw [AlgebraicGeometry.Scheme.dimension_pointClosure x (hht x hx)]
      exact Nat.succ_pos d
    exact topSelfIntersection_pullback_pos_of_range_subset π B A hA W ι (W.pointClosure x)
      (W.pointClosureι x) (hWx x) hpos _ hc hrange
  refine ⟨S, fun x => ((I.cycle (d + 1) x).toNat : ℤ) *
    AlgebraicGeometry.topSelfIntersection (W.pointClosure x) (hWx x)
      ((AlgebraicGeometry.Scheme.Modules.pullback (W.pointClosureι x)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B)), ?_, ?_, ?_⟩
  · intro x hx
    have h0 : 0 < I.cycle (d + 1) x :=
      lt_of_le_of_ne (MiyaokaMori.AmpleTopSelfIntersection.idealSheafData_cycle_nonneg I (d + 1) x)
        (Ne.symm ((hS x).mp hx))
    exact mul_pos (by exact_mod_cast Int.lt_toNat.mpr (by simpa using h0)) (hterm x hx)
  -- 4. expansion
  · show MiyaokaMori.AmpleTopSelfIntersection.capDegree W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) (d + 1)
      (AlgebraicGeometry.firstChernClass L (d + 2) (W.fundamentalChowClass (d + 2))) = _
    rw [hcap, hsum, MiyaokaMori.AmpleTopSelfIntersection.capDegree_finset_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [MiyaokaMori.AmpleTopSelfIntersection.capDegree_nsmul,
      MiyaokaMori.AmpleTopSelfIntersection.capDegree_chowPushforward_fundamentalChowClass W hW _ (d + 1)
      (W.pointClosure x) (hWx x) (W.pointClosureι x)
      (AlgebraicGeometry.Scheme.dimension_pointClosure x (hht x hx))]
    simp only [nsmul_eq_mul]
  -- 6. supp Z(s) ≠ ∅ ⇒ S ≠ ∅
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := hsurj c
    have hwI : w ∈ I.support :=
      (mem_support_pullback_section_iff π W ι N s w).mpr (by rw [hw]; exact hc)
    obtain ⟨x, hxI, hx1⟩ :=
      MiyaokaMori.AmpleTopSelfIntersection.exists_mem_support_coheight_eq_one L σ hσ hwI
    have hxpos :=
      MiyaokaMori.AmpleTopSelfIntersection.idealSheafOfSection_cycle_pos_of_coheight_eq_one (k := K)
        L σ hσ (d + 1) hdim hxI hx1
    exact ⟨x, (hS x).mpr (ne_of_gt hxpos)⟩

end Core

/-- **The mixed intersection number of a class pulled back from the curve with `B` is nonnegative**:
`w := deg(c₁(ι^*B)^{d+1} ∩ c₁(ι^*π^*N) ∩ [W]) ≥ 0`.

Setting: `C` a smooth projective curve, `π : V → C`, `B` a line bundle on `V`, `A` a line bundle on `C` with
`A₀ := B ⊗ π^*A` ample (written `tensor (tensorPow B 1) (tensorPow (π^*A) 1)`, i.e.
`NegativeCurveViaFibration.fiberedTwist π B A 1 1`); `W ⊂ V` integral, proper over `K`, `dim W = d + 2`,
`π|_W` nonconstant; `N` a line bundle on `C` and `s ≠ 0` a global section of it.

**Source**: Fulton, Intersection Theory, §2.3–2.5; Stacks 02SJ/02SK, 02QU.

**Proof**: `capDeg_pullback_section_eq_sum` writes `w` as a finite sum of positive terms (`w = Σ_{x∈S} f x`,
`f > 0`), so `w ≥ 0` (the sum is `0` for `S = ∅`).

**Edge cases**: `Z(s)` may be empty (then `w = 0`); `Z(σ)` may be non-reduced or reducible; `d = 0` is allowed.
`[IsAlgClosed K]` appears in the statement but is not needed in the proof. -/
theorem capDeg_pullback_section_nonneg {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1)))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (d : ℕ) (hdim : W.dimension = d + 2)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (N : C.toScheme.Modules) [N.IsLineBundle] (s : Γ(N, ⊤)) (hs : s ≠ 0) :
    0 ≤ capDeg W hW ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) (d + 1)
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (d + 2)
        (W.fundamentalChowClass (d + 2))) := by
  obtain ⟨S, f, hf, heq, -⟩ := capDeg_pullback_section_eq_sum π B A hA W ι hW d hdim hns N s hs
  rw [heq]
  exact Finset.sum_nonneg fun x hx => (hf x hx).le

/-- **The mixed intersection number of a class pulled back from the curve with `B` is positive**: if the zero
locus of `s` is nonempty, then `w' := deg(c₁(ι^*B)^{d+1} ∩ c₁(ι^*π^*N) ∩ [W]) > 0`.

Same setting as `capDeg_pullback_section_nonneg`, plus `supp Z(s) ≠ ∅`.

**Source**: as above, plus Stacks 0BCN (`exists_mem_support_coheight_eq_one`) and 02SE
(`idealSheafOfSection_cycle_pos_of_coheight_eq_one`).

**Proof**: `capDeg_pullback_section_eq_sum` gives `w' = Σ_{x∈S} f x` with `f > 0` and
`supp Z(s) ≠ ∅ ⇒ S ≠ ∅`; a nonempty sum of positive terms is positive.

**Edge case** `d = 0`: `W_x` is an integral curve and `((ι_x^*ι^*B)^1) > 0` by ampleness. -/
theorem capDeg_pullback_section_pos {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1)))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (d : ℕ) (hdim : W.dimension = d + 2)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (N : C.toScheme.Modules) [N.IsLineBundle] (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (hsupp : (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection N s).support).Nonempty) :
    0 < capDeg W hW ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) (d + 1)
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (d + 2)
        (W.fundamentalChowClass (d + 2))) := by
  obtain ⟨S, f, hf, heq, hne⟩ := capDeg_pullback_section_eq_sum π B A hA W ι hW d hdim hns N s hs
  rw [heq]
  exact Finset.sum_pos hf (hne hsupp)

end MiyaokaMori.FiberedTwistCapDegreeLeaves

end
